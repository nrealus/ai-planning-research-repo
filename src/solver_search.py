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

def search(
    solver: Solver,
    reasoners: List[SolverReasoner],
):

    sat_reasoner = [reasoner for reasoner in reasoners if isinstance(reasoner, SATReasoner)][0]

    # any initialization ?

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
                conflict_analysis_info = solver.explain_invalid_bound_update_into_asserting_clause(
                    contradiction,
                    reasoner,
                )

            elif isinstance(contradiction, SolverConflictInfo.ReasonerExplanation):
                conflict_analysis_info = solver.refine_explanation_into_asserting_clause(
                    list(contradiction.explanation_literals_tuple),
                    reasoner,
                )

            else:
                raise UnreachableCodeError

            if len(conflict_analysis_info.asserting_clause_literals) == 0:
                return "INCONSISTENT"

            clause_to_learn = Clause(
                conflict_analysis_info.asserting_clause_literals,
                TrueLiteral,
                True
            )

            # CLAUSE LEARNING

            (is_clause_conflicting_at_top_level,
            backtrack_level,
            asserted_literal) = solver.get_decision_level_to_backtrack_to(clause_to_learn)

            if is_clause_conflicting_at_top_level:
                return "INCONSISTENT"

            solver.backtrack_to_decision_level(backtrack_level, reasoners)
            sat_reasoner.register_learned_clause_and_set_as_pending(clause_to_learn, asserted_literal)

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
                raise UnreachableCodeError

#################################################################################