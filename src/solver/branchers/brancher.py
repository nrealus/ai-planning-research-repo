"""
TODO
"""

#################################################################################

from __future__ import annotations

#################################################################################

from abc import ABC, abstractmethod
from typing import Callable, List, Tuple

from src.fundamentals import Lit
from src.solver.common import Causes, Decisions
from src.solver.solver_state import SolverState

#################################################################################
# BRANCHER
#################################################################################

class Brancher(ABC):
    """
    TODO
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def initialize(self,
        state: SolverState,
    ) -> None:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_after_assignments_at_current_decision_level(self,
        state: SolverState,
    ) -> None:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_before_backtracking(self,
        target_decision_level: int,
        state: SolverState,
    ) -> None:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_after_conflict_analysis(self,
        asserting_clause_literals: Tuple[Lit,...],
        explain_function: Callable[[List[Lit], Lit, Causes.ReasonerInference], None],
        state: SolverState,
    ) -> None:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def choose_next_decision(self,
        num_conflicts: int,
        state: SolverState,
    ) -> Decisions.AnyDecision:
        """
        TODO
        """
        pass
