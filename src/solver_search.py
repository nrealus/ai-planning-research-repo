from __future__ import annotations

#################################################################################

from typing import List, Optional, Tuple

from .fundamentals import (TRUE_LIT, Lit, Var,
                          are_tightened_disj_literals_tautological,
                          tighten_disj_literals)
from .constraint_expressions import ElemConstrExpr
from .solver import (Causes, ConflictAnalysisResult, Decisions,
                    InvalidBoundUpdateInfo, ReasonerBaseExplanation, Solver)
from .solver_diff_reasoner import DiffReasoner
from .solver_sat_reasoner import SATReasoner

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
    """
    TODO

    (NOTE:a specialized structure (or just a tuple) will obviously have to be used for returns)
    """

    sat_reasoner: SATReasoner = SATReasoner()
    diff_reasoner: DiffReasoner = DiffReasoner()

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

        scope_literal = solver.presence_literals[constr_literal.signed_var.var]
        
        # If the scope of the constraint is false, it means
        # the constraint is absent. So it is ignored.
        if solver.is_entailed(scope_literal.negation()):
            pass
        
        else:

            res = _actually_post_reified_constraint((constr_elementary_expr, constr_literal),
                                                    solver,
                                                    sat_reasoner,
                                                    diff_reasoner)
            if res is not None:
                return "INCONSISTENT"
                                
    while True:

        # PROPAGATION

        propagation_result = solver.propagate(reasoners)

        if propagation_result is not None:
            (contradiction, reasoner) = propagation_result

            if solver.decision_level == 0:
                return "INCONSISTENT"

            # CONFLICT ANALYSIS

            conflict_analysis_info: ConflictAnalysisResult

            match contradiction:
                case InvalidBoundUpdateInfo():
                    conflict_analysis_info = solver.explain_invalid_bound_update(contradiction,
                                                                                 reasoner.explain)
                case ReasonerBaseExplanation():
                    conflict_analysis_info = solver.refine_explanation(list(contradiction.literals),
                                                                       reasoner.explain)
                case _:
                    assert False

            if len(conflict_analysis_info.asserting_clause_literals) == 0:
                return "INCONSISTENT"

            tightened_asserting_clause_literals = tighten_disj_literals(conflict_analysis_info.asserting_clause_literals)

            # CLAUSE LEARNING

            (is_clause_conflicting_at_top_level,
            backtrack_level,
            asserted_literal) = solver.get_decision_level_to_backtrack_to(tightened_asserting_clause_literals)

            if is_clause_conflicting_at_top_level:
                return "INCONSISTENT"

            solver.backtrack_to_decision_level(backtrack_level, reasoners)
            sat_reasoner.add_new_learned_clause(tightened_asserting_clause_literals,
                                                asserted_literal)

        else:

            if solver.is_assignment_complete():
                return "CONSISTENT, SOLUTION FOUND"

            # DECISION

            decision = solver.choose_next_decision()

            match decision:
                case Decisions.Restart():
                    solver.backtrack_to_decision_level(0, reasoners)
                    
                case Decisions.SetLiteral(lit):
                    solver.increment_decision_level(reasoners)
                    solver.set_bound_value(lit.signed_var,
                                           lit.bound_value, 
                                           Causes.Decision())
                case _:
                    assert False

#################################################################################
# 
#################################################################################

# aka initially propagate a constraint
def _actually_post_reified_constraint(
    constraint: Tuple[ElemConstrExpr, Lit],
    solver: Solver,
    sat_reasoner: SATReasoner,
    diff_reasoner: DiffReasoner,
) -> Optional[InvalidBoundUpdateInfo]:
    """
    TODO
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
 
    def make_safe(
        clause_lits: Tuple[Lit,...],
        scope_lit: Lit,
    ) -> Tuple[Tuple[Lit,...], Lit]:
        """
        NOTE: this could be generalized to look at literals
        in the clause as potential scopes
        """

        if scope_lit == TRUE_LIT:
            return (clause_lits,
                    TRUE_LIT)
        
        # The clause can never be true, so it will have to be made absent.
        if len(clause_lits) == 0:
            return ((scope_lit.negation(),),
                    TRUE_LIT)

        if all(solver.is_implication_true(solver.presence_literals[lit.signed_var.var],
                                          scope_lit)
                                          for lit in clause_lits):
            return (clause_lits,
                    scope_lit)

        return (tighten_disj_literals(clause_lits+(scope_lit.negation(),)),
                TRUE_LIT)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def preprocess_then_add_scoped_clause_to_sat_reasoner(
        clause_lits: Tuple[Lit,...],
        scope_lit: Lit,
        clause_lits_already_tightened: bool,
    ) -> Optional[InvalidBoundUpdateInfo]:
        """
        Preprocesses the clause literals and scope literal by:

        - Tightening the clause literals if they weren't already
        
        - Removing "unnecessary" literals from the clause literals 
        (those already known to be false). 
            - If this removes all literals, then the clause is false 
            and thus we must leave its scope: we set the scope literal to false.
        
        - Making the clause literals and the scope literal "safe" for unit
        propagation, by (in the general case) adding the negation of the scope
        literal to the clause literals, and changing the scope literal to TRUE_LIT.
        
        - Adding the "safe" clause literals and scope literal to the SATReasoner
        as a fixed/non-learned scoped clause.
        """

        if clause_lits_already_tightened:
            tightened_lits = tighten_disj_literals(clause_lits)
        else:
            tightened_lits = clause_lits
            
        # Remove clause literals that are guaranteed to not become true
        # (i.e. whose value is False / whose negation literal is entailed)
        true_or_unbounded_lits = list(tightened_lits)
        n = len(true_or_unbounded_lits)
        i = 0
        j = 0
        while i < n-j:
            if solver.is_entailed(true_or_unbounded_lits[i].negation()):
                true_or_unbounded_lits.pop(i)
                j += 1
            else:
                i += 1

        # If the preprocessing of the clause literals removed all of them,
        # then the scope literal must be enforced to be false.

        if len(true_or_unbounded_lits) == 0:

            res = solver.set_bound_value(scope_lit.negation().signed_var,
                                         scope_lit.negation().bound_value,
                                         Causes.Encoding()) 
            return res if isinstance(res, InvalidBoundUpdateInfo) else None

        # The clause literals may have literals on optional variables.
        # Thus the clause must be made "safe" for unit propagation in the SATReasoner.

        safe_clause_lits, safe_scope_lit = make_safe(tuple(true_or_unbounded_lits),
                                                     scope_lit)

        sat_reasoner.add_new_fixed_clause_with_scope(safe_clause_lits,
                                                     safe_scope_lit)
        return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    assert solver.decision_level == 0

    (elem_constr_expr, constr_lit) = constraint
    scope_lit = solver.presence_literals[constr_lit.signed_var.var]

    # If the scope is False, then the constraint is absent: we thus ignore it.
    if solver.is_entailed(scope_lit.negation()):
        return None

    kind, terms = elem_constr_expr.kind, elem_constr_expr.terms

    match kind, terms:
        case ElemConstrExpr.Kind.LIT, Lit() as lit:

            assert solver.is_implication_true(scope_lit, solver.presence_literals[lit.signed_var.var])

            preprocess_then_add_scoped_clause_to_sat_reasoner((constr_lit.negation(), lit),
                                                              scope_lit,
                                                              False)
            preprocess_then_add_scoped_clause_to_sat_reasoner((lit.negation(), constr_lit),
                                                              scope_lit,
                                                              False)
            return None

        case (ElemConstrExpr.Kind.MAX_DIFFERENCE,
              (Var() as from_var, Var() as to_var, int() as max_diff)
        ):
            diff_reasoner.add_reified_difference_constraint(constr_lit,
                                                            from_var,
                                                            to_var,
                                                            max_diff,
                                                            solver)
            return None

        case ElemConstrExpr.Kind.OR, [Lit(), *_] as lits:

            if solver.is_entailed(constr_lit):

                preprocess_then_add_scoped_clause_to_sat_reasoner(lits, 
                                                                  scope_lit, 
                                                                  False)
                return None
            
            elif solver.is_entailed(constr_lit.negation()):

                for lit in lits:

                    res = preprocess_then_add_scoped_clause_to_sat_reasoner((lit.negation(),),
                                                                            scope_lit,
                                                                            False)
                    if res is not None:
                        return res

                return None
            
            else:

                tightened_clause_lits = tighten_disj_literals((constr_lit.negation(),)+lits)

                if are_tightened_disj_literals_tautological(tightened_clause_lits):

                    res = preprocess_then_add_scoped_clause_to_sat_reasoner(tightened_clause_lits,
                                                                            scope_lit,
                                                                            True)
                    if res is not None:
                        return res
                
                for lit in lits:

                    res = preprocess_then_add_scoped_clause_to_sat_reasoner((lit.negation(), constr_lit),
                                                                            scope_lit,
                                                                            False)
                    if res is not None:
                        return res

                return None

        case ElemConstrExpr.Kind.AND, [Lit(), *_]:

            return _actually_post_reified_constraint((elem_constr_expr.negation(), constr_lit.negation()),
                                                     solver,
                                                     sat_reasoner,
                                                     diff_reasoner)
        case _:
            assert False

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
