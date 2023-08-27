from __future__ import annotations

#################################################################################

from typing import Dict, List, NamedTuple, Optional, Set, Tuple, Union

from fundamentals import (
    Lit, TRUE_LIT,
    ConstraintElementaryExpression,
#    ReifiedConstraint,
    tighten_literals,
    are_tightened_literals_tautological,
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
    while last_unposted_constraint_index < len(solver.constraints):
        (constr_elementary_expr, constr_literal) = solver.constraints[last_unposted_constraint_index]

        scope_literal = solver.vars_presence_literals[constr_literal.signed_var.var]
        
        # If the scope of the constraint is false, it means
        # the constraint is absent. So it is ignored.
        if solver.is_literal_entailed(scope_literal.negation()):
            pass
        
        else:
            res = _actually_post_reified_constraint(
                solver,
                sat_reasoner,
                (constr_elementary_expr, constr_literal))
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
    constraint: Tuple[ConstraintElementaryExpression.AnyExpr, Lit],
) -> Optional[SolverConflictInfo.InvalidBoundUpdate]:
    """
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    def _add_clause_to_sat_reasoner(
        clause_literals: Tuple[Lit,...],
        scope_literal: Lit,
        clause_literals_already_tightened: bool=False,
    ) -> bool | SolverConflictInfo.InvalidBoundUpdate:

        if clause_literals_already_tightened:
            clause_tightened_literals = tighten_literals(clause_literals)
        else:
            clause_tightened_literals = clause_literals

        # Remove clause literals that are guaranteed to not become true
        # (i.e. whose value is False / whose negation literal is entailed)
        lits: List[Lit] = list(clause_tightened_literals)
        n: int = len(lits)
        i: int = 0
        j: int = 0
        while i < n-j:
            if solver.is_literal_entailed(lits[i].negation()):
                lits.pop(i)
                j += 1
            else:
                i += 1

        clause_tightened_literals = tuple(lits)

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

        if len(clause_tightened_literals) == 0:

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
            for lit in clause_tightened_literals
        ):
            pass
        
        else:
            clause_tightened_literals = tighten_literals(
                clause_tightened_literals+(processed_scope_literal.negation(),))
            processed_scope_literal = TRUE_LIT

        sat_reasoner.add_new_fixed_clause_with_scope(
            clause_tightened_literals,
            processed_scope_literal)
        return True

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    assert solver.dec_level == 0

    (constr_elementary_expr, constr_literal) = constraint
    scope_literal = solver.vars_presence_literals[constr_literal.signed_var.var]

    # If the scope is False, then the constraint is absent: we thus ignore it.
    if solver.is_literal_entailed(scope_literal.negation()):
        return None

    if isinstance(constr_elementary_expr, ConstraintElementaryExpression.LitExpr):

        assert solver.is_implication_true(
            scope_literal,
            solver.vars_presence_literals[constr_elementary_expr.literal.signed_var.var])

        _add_clause_to_sat_reasoner(
            (constr_literal.negation(), constr_elementary_expr.literal),
            scope_literal)

        _add_clause_to_sat_reasoner(
            (constr_elementary_expr.literal.negation(), constr_literal),
            scope_literal)

    elif isinstance(constr_elementary_expr, ConstraintElementaryExpression.MaxDiffCnt):
        #FIXME
        # _add_reified_edge(
        #     solver,
        #     diff_reasoner,
        #     constr_literal,
        #     constr_.to_var,
        #     constr_.from_var,
        #     constr_.max_diff,
        # )
        raise NotImplementedError

    elif isinstance(constr_elementary_expr, ConstraintElementaryExpression.Or):

        if solver.is_literal_entailed(constr_literal):
            _add_clause_to_sat_reasoner(
                constr_elementary_expr.literals,
                scope_literal,
            )
            return None
        
        elif solver.is_literal_entailed(constr_literal.negation()):
            for lit in constr_elementary_expr.literals:
                res = _add_clause_to_sat_reasoner(
                    (lit.negation(),),
                    scope_literal,
                )
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
            return None
        
        else:

            clause_tightened_literals = tighten_literals(
                (constr_literal.negation(),)+constr_elementary_expr.literals)

            if are_tightened_literals_tautological(clause_tightened_literals):
                res = _add_clause_to_sat_reasoner(
                    clause_tightened_literals,
                    scope_literal,
                    True)
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
            
            for lit in constr_elementary_expr.literals:
                res = _add_clause_to_sat_reasoner(
                    (lit.negation(), constr_literal),
                    scope_literal)
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res

            return None

    elif isinstance(constr_elementary_expr, ConstraintElementaryExpression.And):

        return _actually_post_reified_constraint(
            solver,
            sat_reasoner,
            (constr_elementary_expr.negation(), constr_literal.negation()),
        )

    else:
        assert False

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
