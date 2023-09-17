"""
TODO
"""

#################################################################################

from __future__ import annotations

#################################################################################

from abc import ABC, abstractmethod
from typing import List, Optional

from src.fundamentals import Lit
from src.solver.common import (Causes, InvalidBoundUpdateInfo,
                               ReasonerBaseExplanation)
from src.solver.solver_state import SolverState

#################################################################################
# REASONER
#################################################################################

class Reasoner():
    """
    Base class (or rather interface) for reasoners.
    
    Reasoners are specialized inference engines / "modules" of
    the (main) solver. They are queried by the solver's propagation
    method one by one, to perform specialized propagation / inference.
    Each of them processes newly accumulated events (bound updates),
    including those resulting from inference / propagation
    by other reasoners, until nothing new can be inferred.
    
    When a reasoner encounters a conflict, it returns an
    initial / base / "starting point" explanation.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_solver_increment_one_decision_level(self) -> None:
        """
        Updates the internal state of the reasoner when the decision level is
        incremented by 1 (which happens when applying a set literal decision).
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_solver_backtrack_one_decision_level(self) -> None:
        """
        Updates the internal state of the reasoner when the decision level is
        decreased by 1 (which happens when backtracking one level (or more)).
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def propagate(self) -> Optional[InvalidBoundUpdateInfo | ReasonerBaseExplanation]:
        """
        Propagates the accumulated events to the reasoner (namely to its
        specialized constraints) and performs specialized inference.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def explain(self,
        explanation_literals: List[Lit],
        literal: Lit,
        inference_cause: Causes.ReasonerInference,
    ) -> None:
        """REVIEW
        Contributes to building a "full" explanation by adding to it
        literals l_1, ... l_n, such that l_1 & ... & l_n => literal.
        """
        pass
