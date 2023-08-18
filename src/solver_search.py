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
    reasoners: List[SolverReasoner],
):

    sat_reasoner = [reasoner for reasoner in reasoners if isinstance(reasoner, SATReasoner)][0]

    # We assume constraints are already posted at this point, using the "solver api" functions

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
            sat_reasoner.add_clause_learned(conflict_analysis_info.asserting_clause_literals, asserted_literal)

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

#################################################################################