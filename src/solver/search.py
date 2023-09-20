"""
TODO
"""

from __future__ import annotations

#################################################################################

from typing import Optional, Tuple

from src.fundamentals import Lit, tighten_literals
from src.solver.common import (Causes, ConflictAnalysisResult, Decisions,
                               InvalidBoundUpdateInfo,
                               ReasonerBaseExplanation)
from src.solver.branchers.brancher import Brancher
from src.solver.solver import Solver
from src.solver.solver_state import SolverState

#################################################################################
#
#################################################################################

class ExampleBrancher(Brancher):

    def __init__(self,
        main_brancher: Brancher,
        until_first_conflict_brancher: Optional[Brancher],
        use_restarts: bool = True,
        num_allowed_conflicts_before_restart_first_time: int = 20,
        increase_ratio_for_num_allowed_conflicts: float = 1.05,
    ):
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        self.main_brancher: Brancher = main_brancher

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        self.until_first_conflict_brancher: Optional[Brancher] = until_first_conflict_brancher
        
        self.encountered_first_conflict: bool = False

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        self.use_restarts: bool = use_restarts
        
        self.num_allowed_conflicts_before_restart_first_time: int = num_allowed_conflicts_before_restart_first_time
        
        self.num_allowed_conflicts_before_restart: int = num_allowed_conflicts_before_restart_first_time
        
        self.increase_ratio_for_num_allowed_conflicts: float = increase_ratio_for_num_allowed_conflicts
        
        self.num_conflicts_at_last_restart: int = 0

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_after_assignments_at_current_decision_level(self,
        state: SolverState,
    ):

        if (not self.encountered_first_conflict
            and self.until_first_conflict_brancher is not None
        ):
            self.until_first_conflict_brancher.on_after_assignments_at_current_decision_level(state)

        self.main_brancher.on_after_assignments_at_current_decision_level(state)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def branchers_on_before_backtracking(self,
        target_decision_level: int,
        state: SolverState,
    ):

        if (not self.encountered_first_conflict
            and self.until_first_conflict_brancher is not None
        ):
            self.until_first_conflict_brancher.on_before_backtracking(target_decision_level, state)

        self.main_brancher.on_before_backtracking(target_decision_level, state)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_after_conflict_analysis(self,
        asserting_clause_literals: Tuple[Lit,...],
        explain_function,
        state: SolverState,
    ):

        self.encountered_first_conflict = True

        self.main_brancher.on_after_conflict_analysis(asserting_clause_literals,
                                                      explain_function,
                                                      state)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def choose_next_decision(self,
        num_conflicts: int,
        state: SolverState,
    ) -> Decisions.AnyDecision:

        if (not self.encountered_first_conflict
            and self.until_first_conflict_brancher is not None
        ):
            assert num_conflicts == 0
            return self.until_first_conflict_brancher.choose_next_decision(num_conflicts, state)

        elif (self.use_restarts
              and num_conflicts - self.conflicts_at_last_restart >= self.num_allowed_conflicts_before_restart
        ):
            self.conflicts_at_last_restart = num_conflicts
            self.num_allowed_conflicts_before_restart = int(self.num_allowed_conflicts_before_restart_first_time
                                                            * self.increase_ratio_for_num_allowed_conflicts)
            return Decisions.Restart()
        
        else:
            return self.main_brancher.choose_next_decision(num_conflicts, state)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def search(
    solver: Solver,
    brancher: Brancher
):
    """
    TODO

    (NOTE:a specialized structure (or just a tuple) will obviously have to be used for returns)
    """

    if solver.sat_reasoner is None:
        raise ValueError("Search requires the solver to have an attached SAT reasoner.")

    if solver.diff_reasoner is None:
        raise ValueError("Search requires the solver to have an attached Difference Logic reasoner.")

    brancher.initialize(solver.state)

    while True:

        # PROPAGATION

        propagation_result = solver.propagate()

        brancher.on_after_assignments_at_current_decision_level(solver.state)

        if propagation_result is not None:

            (conflict_info, reasoner) = propagation_result

            if solver.state.decision_level == 0:
                return "INCONSISTENT"

            # CONFLICT ANALYSIS

            conflict_analysis_info: ConflictAnalysisResult

            match conflict_info:
                case InvalidBoundUpdateInfo():
                    conflict_analysis_info = solver.explain_invalid_bound_update(conflict_info,
                                                                                 reasoner.explain)
                case ReasonerBaseExplanation():
                    conflict_analysis_info = solver.refine_explanation(list(conflict_info.literals),
                                                                       reasoner.explain)
                case _:
                    assert False

            if len(conflict_analysis_info.asserting_clause_literals) == 0:
                return "INCONSISTENT"

            tightened_asserting_clause_literals = tighten_literals(conflict_analysis_info.asserting_clause_literals)

            brancher.on_after_conflict_analysis(tightened_asserting_clause_literals,
                                                reasoner.explain,
                                                solver.state)

            # CLAUSE LEARNING

            (is_clause_conflicting_at_top_level,
            decision_level_to_backtrack_to,
            asserted_literal) = solver.get_decision_level_to_backtrack_to(tightened_asserting_clause_literals)

            if is_clause_conflicting_at_top_level:
                return "INCONSISTENT"

            brancher.on_before_backtracking(decision_level_to_backtrack_to, solver.state)

            solver.backtrack_to_decision_level(decision_level_to_backtrack_to)
            solver.sat_reasoner.add_new_learned_clause(tightened_asserting_clause_literals,
                                                       asserted_literal)

        else:

            if solver.state.is_assignment_complete():
                return "CONSISTENT, SOLUTION FOUND"

            # DECISION

            decision = brancher.choose_next_decision(solver.sat_reasoner.num_conflicts,
                                                     solver.state)

            match decision:

                case Decisions.Restart():

                    brancher.on_before_backtracking(0, solver.state)
                    solver.backtrack_to_decision_level(0)
                    
                case Decisions.SetLiteral(lit):

                    solver.increment_one_decision_level()
                    solver.state.set_literal(lit, Causes.Decision())
                case _:
                    assert False

#################################################################################
