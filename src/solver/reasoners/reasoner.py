"""
This module defines the base class for reasoners.

Reasoners are specialized inference engines or "modules" of
the solver. They are queried by the solver's propagation method
one by one, to perform specialized propagation / inference.
Each of them processes newly accumulated events (bound updates),
including those resulting from inference / propagation
by other reasoners, until nothing new can be inferred.
"""

#################################################################################

from __future__ import annotations

#################################################################################
# FILE CONTENTS:
# - REASONER BASE CLASS
#################################################################################

from abc import ABC, abstractmethod
from typing import List, Optional

from src.fundamentals import Lit
from src.solver.common import (Causes, InvalidBoundUpdate,
                               ReasonerBaseExplanation)

#################################################################################
# DOC: OK 25/10/23
#################################################################################

class Reasoner(ABC):
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
    def on_solver_increment_decision_level_by_one(self) -> None:
        """
        Updates the internal state of the reasoner when
        `Solver.increment_decision_level_by_one` is called.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_solver_backtrack_one_decision_level(self) -> None:
        """
        Updates the internal state of the reasoner when `Solver` backtracks one level.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def propagate(self) -> Optional[InvalidBoundUpdate | ReasonerBaseExplanation]:
        """
        Propagates the accumulated events to the reasoner (namely to its
        specialized constraints) and performs specialized inference.

        Returns:
            None if the propagation was successful, and a conflict if one is encountered.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def explain(self,
        explanation: List[Lit],
        literal: Lit,
        inference_cause: Causes.ReasonerInference,
    ) -> None:
        """REVIEW
        Contributes to building a "full" explanation by adding to it
        literals `l_1, ... l_n`, such that `l_1 & ... & l_n => literal`.

        Args:
            explanation: The list of literals making up the explanation. \
                Modified by the function.

            literal: The literal whose implying literals we want to add to the explanation.

            inference_cause: TODO.
        """
        pass
