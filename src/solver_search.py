from __future__ import annotations

#################################################################################

from typing import Dict, List, NamedTuple, Optional, Set, Tuple, Union

from fundamentals import (
    Lit, TRUE_LIT,
    ConstraintElementaryExpression,
    ReifiedConstraint,
    TightDisjunction,
)

from solver import SolverDecisions, SolverCauses, SolverConflictInfo, Solver
from solver_sat_reasoner import SATReasoner

#################################################################################
#################################################################################
#                                   CONTENTS:
# - MAIN SOLVING FUNCTION
#
# - HELPER FUNCTION FOR CONSTRAINT POSTING / INITIAL PROPAGATION
#################################################################################
#################################################################################

#################################################################################
# 
#################################################################################

def search(
    solver: Solver,
):

    sat_reasoner: SATReasoner = SATReasoner()
#    diff_reasoner: ,

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
                ReifiedConstraint(constr_formula, reification_literal))
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
                    reasoner)

            elif isinstance(contradiction, SolverConflictInfo.ReasonerExplanation):
                conflict_analysis_info = solver.refine_explanation(
                    list(contradiction.explanation_literals),
                    reasoner)

            else:
                assert False

            if len(conflict_analysis_info.asserting_clause_literals) == 0:
                return "INCONSISTENT"

            # CLAUSE LEARNING

            (is_clause_conflicting_at_top_level,
            backtrack_level,
            asserted_literal) = solver.get_decision_level_to_backtrack_to(
                conflict_analysis_info.asserting_clause_literals)

            if is_clause_conflicting_at_top_level:
                return "INCONSISTENT"

            solver.backtrack_to_decision_level(backtrack_level, reasoners)
            sat_reasoner.add_new_learned_clause(
                conflict_analysis_info.asserting_clause_literals,
                asserted_literal)

        else:

            if solver.is_vars_assignment_complete():
                return "CONSISTENT, SOLUTION FOUND"

            # DECISION

            decision = solver.choose_next_decision()

            if isinstance(decision, SolverDecisions.Restart):
                solver.backtrack_to_decision_level(0, reasoners)

            elif isinstance(decision, SolverDecisions.SetLiteral):
                solver.increment_decision_level_and_perform_set_literal_decision(decision, reasoners)

            else:
                assert False

#################################################################################
# 
#################################################################################

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
    def _add_clause_from_clause_literals_and_scope(
        clause_literals: Tuple[Lit,...],
        scope_literal: Lit,
        clause_literals_already_tight: bool=False,
    ) -> bool | SolverConflictInfo.InvalidBoundUpdate:

        clause_in_tight_form = TightDisjunction(clause_literals, clause_literals_already_tight)

        # Remove clause literals that are guaranteed to not become true
        # (i.e. whose value is False / whose negation literal is entailed)
        lits: List[Lit] = list(clause_in_tight_form.literals)
        n: int = len(lits)
        i: int = 0
        j: int = 0
        while i < n-j:
            if solver.is_literal_entailed(lits[i].negation()):
                lits.pop(i)
                j += 1
            else:
                i += 1

        clause_in_tight_form = TightDisjunction(tuple(lits), True)

        processed_scope_literal: Lit = scope_literal

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

        if len(clause_in_tight_form.literals) == 0:

            processed_scope_literal_neg = processed_scope_literal.negation()

            scope_negation_enforcement_result = solver.set_bound_value(
                processed_scope_literal_neg.signed_var,
                processed_scope_literal_neg.bound_value,
                SolverCauses.Encoding()) 
            if isinstance(scope_negation_enforcement_result, SolverConflictInfo.InvalidBoundUpdate):
                return scope_negation_enforcement_result
            else:
                return True

        elif all(solver.is_implication_true(
            solver.vars_presence_literals[lit.signed_var.var],processed_scope_literal)
            for lit in clause_in_tight_form.literals
        ):
            pass
        
        else:
            clause_in_tight_form = TightDisjunction(
                clause_in_tight_form.literals+(processed_scope_literal.negation(),))
            processed_scope_literal = TRUE_LIT

        sat_reasoner.add_new_fixed_clause_with_scope(
            clause_in_tight_form.literals,
            processed_scope_literal)
        return True

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    assert solver.dec_level == 0

    (constraint_elementary_expression, reification_literal) = reified_constraint
    scope_literal = solver.vars_presence_literals[reification_literal.signed_var.var]

    # If the scope is False, then the constraint is absent: we thus ignore it.
    if solver.is_literal_entailed(scope_literal.negation()):
        return None

    if isinstance(constraint_elementary_expression, ConstraintElementaryExpression.LitExpr):

        assert solver.is_implication_true(
            scope_literal,
            solver.vars_presence_literals[constraint_elementary_expression.literal.signed_var.var])

        _add_clause_from_clause_literals_and_scope(
            (reification_literal.negation(), constraint_elementary_expression.literal),
            scope_literal)

        _add_clause_from_clause_literals_and_scope(
            (constraint_elementary_expression.literal.negation(), reification_literal),
            scope_literal)

    elif isinstance(constraint_elementary_expression, ConstraintElementaryExpression.MaxDiffCnt):
        #FIXME
        # _add_reified_edge(
        #     solver,
        #     diff_reasoner,
        #     reification_literal,
        #     constr_.to_var,
        #     constr_.from_var,
        #     constr_.max_diff,
        # )
        raise NotImplementedError

    elif isinstance(constraint_elementary_expression, ConstraintElementaryExpression.Or):

        if solver.is_literal_entailed(reification_literal):
            _add_clause_from_clause_literals_and_scope(
                constraint_elementary_expression.literals,
                scope_literal,
            )
            return None
        
        elif solver.is_literal_entailed(reification_literal.negation()):
            for lit in constraint_elementary_expression.literals:
                res = _add_clause_from_clause_literals_and_scope(
                    (lit.negation(),),
                    scope_literal,
                )
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
            return None
        
        else:

            clause_in_tight_form = TightDisjunction(
                (reification_literal.negation(),)+constraint_elementary_expression.literals)

            if clause_in_tight_form.is_tautological():
                res = _add_clause_from_clause_literals_and_scope(
                    clause_in_tight_form.literals,
                    scope_literal,
                    True)
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
            
            for literal in constraint_elementary_expression.literals:
                res = _add_clause_from_clause_literals_and_scope(
                    (literal.negation(), reification_literal),
                    scope_literal)
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res

            return None

    elif isinstance(constraint_elementary_expression, ConstraintElementaryExpression.And):

        return _actually_post_reified_constraint(
            solver,
            sat_reasoner,
            ReifiedConstraint(constraint_elementary_expression.negation(), reification_literal.negation()),
        )

    else:
        assert False

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
