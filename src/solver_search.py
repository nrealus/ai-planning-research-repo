from __future__ import annotations

#################################################################################

from typing import Tuple

from fundamentals import *
from solver import *
from solver_sat_reasoner import *

#################################################################################
#################################################################################
#                                   CONTENTS:
# - MAIN SOLVING FUNCTION
#################################################################################
#################################################################################

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # 

def search(
    solver: Solver,
    sat_reasoner: SATReasoner,
#    diff_reasoner: ,
):

    reasoners = (sat_reasoner, )

    last_unposted_constraint_index = 0

    # NOTE: This block of code ("constraint posting", i.e. initial propagation)
    # could be placed in / right before propagation, inside of the loop.
    # This is how it is in Aries. However, this block of code is only executed
    # when the decision level of the solver is top/root/0.
    # So in theory, placing it inside of the loop could make sense if we expect new
    # (already reified / known) reified constraints to be posted when backtracking to
    # the root level. But solution enumeration approaches, for example for optimization,
    # do not reify the constraints they add to "prevent"/"block" the previous solutions...
    # So I don't really understand that well why this constraint posting block was put
    # inside the loop in Aries. Maybe it was simply to "unify" the general propagation
    # code with this initial propagation code. But maybe there's a another reason ?
    # Until this is clarified, I choose to follow a simpler approach: do the constraint
    # posting / initial propagation once at the beginning, and make it explicit in the code.
    while last_unposted_constraint_index < len(solver.reified_constraints):
        (constr_formula, reification_literal) = solver.reified_constraints[last_unposted_constraint_index]

        scope_literal = solver.vars_presence_literals[reification_literal.signed_var.var]
        
        # If the scope of the constraint is false, it means
        # the constraint is absent. So it is ignored.
        if solver.is_literal_entailed(scope_literal.negation()):
            pass
        
        else:
            res = _actually_post_reified_constraint(
                solver,
                sat_reasoner,
                ReifiedConstraint(constr_formula, reification_literal),
            )
            if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                return "INCONSISTENT"

    while True:

        # PROPAGATION

        propagation_result = solver.propagate(reasoners)

        if propagation_result is not None:
            (contradiction, reasoner) = propagation_result

            if solver.dec_level == 0:
                return "INCONSISTENT"

            # CONFLICT ANALYSIS

            conflict_analysis_info: SolverConflictInfo.AnalysisResult
            if isinstance(contradiction, SolverConflictInfo.InvalidBoundUpdate):
                conflict_analysis_info = solver.explain_invalid_bound_update(
                    contradiction,
                    reasoner,
                )

            elif isinstance(contradiction, SolverConflictInfo.ReasonerExplanation):
                conflict_analysis_info = solver.refine_explanation(
                    list(contradiction.explanation_literals),
                    reasoner,
                )

            else:
                assert False

            if len(conflict_analysis_info.asserting_clause_literals) == 0:
                return "INCONSISTENT"

            # CLAUSE LEARNING

            (is_clause_conflicting_at_top_level,
            backtrack_level,
            asserted_literal) = solver.get_decision_level_to_backtrack_to(conflict_analysis_info.asserting_clause_literals)

            if is_clause_conflicting_at_top_level:
                return "INCONSISTENT"

            solver.backtrack_to_decision_level(backtrack_level, reasoners)
            sat_reasoner.add_new_learned_clause(conflict_analysis_info.asserting_clause_literals, asserted_literal)

        else:

            if solver.is_vars_assignment_complete():
                return "CONSISTENT, SOLUTION FOUND"

            # DECISION

            decision = solver.choose_next_decision()

            if isinstance(decision, SolverDecision.Restart):
                solver.backtrack_to_decision_level(0, reasoners)

            elif isinstance(decision, SolverDecision.SetLiteral):
                solver.increment_decision_level_and_perform_set_literal_decision(decision, reasoners)

            else:
                assert False

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# aka initially propagate a constraint
def _actually_post_reified_constraint(
    solver: Solver,
    sat_reasoner: SATReasoner,
#    diff_reasoner: ,
    reified_constraint: ReifiedConstraint,
) -> Optional[SolverConflictInfo.InvalidBoundUpdate]:
    """
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_clause_from_raw_clause_literals_and_scope(
        raw_clause_literals: Tuple[Literal,...],
        raw_scope_literal: Literal,
    # FIXME: shouldn't we actually ALWAYS want to do this ?
        return_false_if_tautological_clause_literals: bool,
    ) -> Union[bool, SolverConflictInfo.InvalidBoundUpdate]:

        clause_literals: List[Literal] = list(raw_clause_literals)
        processed_scope_literal: Literal = raw_scope_literal

        # Sort clause literals (lexicographically) and remove duplicate
        # literals (weaker literals on the same signed variable).

        clause_literals.sort()

        n = len(raw_clause_literals)
        i = 0
        while i < n-1:
            # Because the clause literals are now lexicographically sorted,
            # we know that if two literals are on the same signed variable,
            # the weaker one is necessarily the next one.
            if clause_literals[i].entails(clause_literals[i+1]):
                clause_literals.pop(i)
            else:
                i += 1

        # Remove clause literals that are guaranteed to not become true
        # (i.e. whose value is False / whose negation literal is entailed)

        n = len(clause_literals)
        i = 0
        while i < n:
            if solver.is_literal_entailed(clause_literals[i].negation()):
                clause_literals.pop(i)
            else:
                i += 1

        if return_false_if_tautological_clause_literals:
            n = len(raw_clause_literals)
            i = 0
            while i < n-1:
                if clause_literals[i].signed_var == clause_literals[i+1].signed_var.opposite_signed_var():
                    if clause_literals[i].bound_value + clause_literals[i+1].bound_value >= 0:
                        return False

        # Analyze processed clause literals and scope.
        #
        # If the processing of the clause literals removed all of them,
        # then the scope must be enforced to be false.
        #
        # If the processed clause literals are not empty, the we must make
        # sure the clause added to the solver (or rather its sat reasoner)
        # can be unit propagated safely, as its literals' variables can be optional.
        #
        # NOTE: this could be generalized to look at literals in the clause as potential scopes

        if len(clause_literals) == 0:

            processed_scope_literal_neg = processed_scope_literal.negation()

            scope_negation_enforcement_result = solver.set_bound_value(
                processed_scope_literal_neg.signed_var,
                processed_scope_literal_neg.bound_value,
                SolverCause.Encoding()
            ) 
            if isinstance(scope_negation_enforcement_result, SolverConflictInfo.InvalidBoundUpdate):
                return scope_negation_enforcement_result
            else:
                return True

        elif all(solver.is_implication_true(
            solver.vars_presence_literals[lit.signed_var.var],processed_scope_literal)
            for lit in clause_literals
        ):
            pass
        
        else:
            clause_literals.append(processed_scope_literal.negation())
            processed_scope_literal = TrueLiteral

        sat_reasoner.add_new_fixed_clause_with_scope(
            tuple(clause_literals),
            processed_scope_literal)
        return True

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    assert solver.dec_level == 0

    (constr_formula, reification_literal) = reified_constraint

    scope_literal = solver.vars_presence_literals[reification_literal.signed_var.var]

    if isinstance(constr_formula, ConstrFormula.SingleLit):

        assert solver.is_implication_true(
            scope_literal,
            solver.vars_presence_literals[constr_formula.literal.signed_var.var])

        _add_clause_from_raw_clause_literals_and_scope(
            (reification_literal.negation(), constr_formula.literal),
            scope_literal,
            False,
        )
        _add_clause_from_raw_clause_literals_and_scope(
            (constr_formula.literal.negation(), reification_literal),
            scope_literal,
            False,
        )

    elif isinstance(constr_formula, ConstrFormula.MaxDiffCnt):
        #FIXME
        # _add_reified_edge(
        #     solver,
        #     diff_reasoner,
        #     reification_literal,
        #     constr_.to_var,
        #     constr_.from_var,
        #     constr_.max_diff,
        # )
        pass

    elif isinstance(constr_formula, ConstrFormula.Or):

        if solver.is_literal_entailed(reification_literal):
            _add_clause_from_raw_clause_literals_and_scope(
                constr_formula.literals,
                scope_literal,
                False,
            )
            return None
        
        elif solver.is_literal_entailed(reification_literal.negation()):
            for lit in constr_formula.literals:
                res = _add_clause_from_raw_clause_literals_and_scope(
                    (lit.negation(),),
                    scope_literal,
                    False,
                )
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
            return None
        
        else:

            res = _add_clause_from_raw_clause_literals_and_scope(
                (reification_literal.negation(),)+constr_formula.literals,
                scope_literal,
                True,
            )
            if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                return res
            
            for literal in constr_formula.literals:
                res = _add_clause_from_raw_clause_literals_and_scope(
                    (literal.negation(), reification_literal),
                    scope_literal,
                    False,
                )
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res

            return None

    elif isinstance(constr_formula, ConstrFormula.And):

        return _actually_post_reified_constraint(
            solver,
            sat_reasoner,
            ReifiedConstraint(constr_formula.negation(), reification_literal.negation()),
        )

    else:
        assert False

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
