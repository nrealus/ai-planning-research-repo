"""
This module defines some common "helper" types used by the solver, as well as
a "helper" or "wrapper" collection.
"""

from __future__ import annotations

#################################################################################

from abc import ABC
from typing import (Dict, Generic, List, NamedTuple, Optional, Sequence, Set,
                    Tuple, TypeVar, Union)

from src.fundamentals import Bound, Lit, SignedVar

#################################################################################
# DOC: OK 23/10/23
#################################################################################

T = TypeVar('T')

class SetGuardedByLits(Generic[T]):
    """
    Represents a "guarded" collection of elements. Each element is
    guarded by a literal (and implicitly all literals stronger than it).

    Implemented as a simple wrapper around a `Dict[SignedVar, Dict[Bound, Set[T]]]`.

    Note:
        This class is most notably used for the implication graph on non optional
        variables in `Solver`, as well as for (watched) literals `watches` in
        `SATReasoner` and `DiffReasoner`.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def __init__(self):
        self._data: Dict[SignedVar, Dict[Bound, Set[T]]] = {}
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add(self,
        element: T,
        literal: Lit,
    ) -> None:
        """
        Adds a new guarded element to the collection.
        
        Raises:
            ValueError: If `element` is already present and already guarded \
                by `literal` (or, implicitly, any literal stronger than it).
        
        Note:
            An element can be added if it is absent from the collection, or if
            it is guarded by a literal stronger than `literal`. When we
            record this new, weaker guard, the previous guard becomes redundant.
            However we make no effort to erase it, as it does not harm or
            interfere with anything functionality of the class.
        """
        
        if literal.signed_var not in self._data:
            self._data[literal.signed_var] = {}
        
        if literal.bound not in self._data[literal.signed_var]:
            self._data[literal.signed_var][literal.bound] = set()

        if element in self.elements_guarded_by(literal):
            raise ValueError("Element already present (guarded by {0}).".format(literal))
        
        self._data[literal.signed_var][literal.bound].add(element)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def remove(self,
        element: T,
        literal: Lit,
    ) -> None:
        """
        Removes a guarded element from the colleciton.
        
        Raises:
            ValueError | KeyError: If `element` is not in the collection \
                or is not guarded by `literal`.
        """
        
        self._data[literal.signed_var][literal.bound].remove(element)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def remove_all_on(self,
        signed_var: SignedVar,
    ) -> None:
        """
        Removes all elements guarded by any literal on the given signed variable.

        Raises:
            KeyError: If no guard literal on `signed_var` is registered.
        """
        
        self._data.pop(signed_var)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def elements_guarded_by(self,
        literal: Lit,
    ) -> Tuple[T,...]:
        """        
        Returns:
            All elements guarded by `literal` (and, implicitly, all literals stronger \
                than it). The elements returned are unique, there are no duplicates.
        """

        if literal.signed_var not in self._data:
            return ()

        res = set()

        for guard_bound, guarded_elements in self._data[literal.signed_var].items():
            if literal.bound.is_stronger_than(guard_bound):
                res.update(guarded_elements)

        return tuple(res)
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def has_elements_guarded_by_literals_on(self,
        signed_var: SignedVar
    ) -> bool:
        """
        Returns:
            Whether there are any elements guarded by a literal on `signed_var`.
        """
        
        return signed_var in self._data and len(self._data[signed_var]) > 0

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def has_elements_guarded_by(self,
        literal: Lit
    ) -> bool:
        """
        Returns:
            Whether there are any elements guarded by `literal` \
                (and, implicitly, all literals stronger than it).
        """
        
        if literal.signed_var not in self._data:
            return False
        
        for guard_bound in self._data[literal.signed_var]:
            if literal.bound.is_stronger_than(guard_bound):
                return True
        
        return False

#################################################################################
# DOC: OK 23/10/23
#################################################################################

class Decisions(ABC):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class SetLit(NamedTuple):
        """Represents a decision to increment the decision level and enforce a certain literal."""

        literal_to_set: Lit
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Restart(NamedTuple):
        """Represents a decision to backtrack to the top decision level."""
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyDecision = SetLit | Restart

#################################################################################
# DOC: OK 23/10/23
#################################################################################

class Causes(ABC):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Decision(NamedTuple):
        """
        Represents a cause corresponding to a decision to
        enforce a certain literal (see `Decisions.SetLit`).
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Encoding(NamedTuple):
        """
        REVIEW?
        Represents a cause corresponding to the deactivation of a scope in which an
        (already reified) constraint, found to be impossible to satisfy, is defined.
        In other words, this means setting the corresponding scope literal as false.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ImplicationPropagation(NamedTuple):
        """
        Represents a cause corresponding to an implication propagation.

        Note:
            Implication propagations are triggered on bound updates of non optional
            variables (notably presence variables) and concern literals that are implied
            by the newly entailed literal. This is possible thanks to the implication
            graph on non optional variables' literals maintained by the solver.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        literal: Lit
        """The literal whose entailment triggered the implication propagation."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class EmptyDomain(NamedTuple):
        """
        Represents a cause corresponding to the prevention of an optional variable's
        domain becoming empty, by setting its presence literal to false.

        Note:
            Presence variables are non optional by definition.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        literal: Lit
        """The literal whose entailment would make its variable's domain empty."""

        cause: Causes.AnyCause
        """
        The cause of the attempt to entail the literal that would make its
        variable's domain empty.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ReasonerInference(NamedTuple):
        """This cause corresponds to an inference made by a `Reasoner` during propagation."""

        reasoner_id: int
        """REVIEW? The id of the `Reasoner` that made the inference."""

        inference_info: object          # TODO
        """The inference information"""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyCause = Decision | Encoding | ImplicationPropagation | EmptyDomain | ReasonerInference

#################################################################################
# DOC: OK 23/10/23
#################################################################################

class Event(NamedTuple):
    """
    Represents an event, i.e. (meta)data on the entailment of a literal
    (or, equivalently, a signed variable's bound update).
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    signed_var: SignedVar
    """The signed variable whose bound was updated with the event."""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    bound: Bound
    """
    The new bound of the event's signed variable.
    It is necessarily strictly stronger than its previous bound.
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    old_bound: Bound
    """The previous bound that this event's signed variable had, before the event."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    index: Tuple[int, int]  # TODO: EventIndex type ?
    """
    The index of the event (see `Solver.events_trail`).
    
    Note:
        It is a "double index": the first int of the tuple corresponds to the decision
        level, and the second one corresponds to the event's index in that decision level.
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    old_index: Optional[Tuple[int, int]]
    """
    The index of the previous event on the same signed variable (if not None).
    This previous event set the signed variable's old bound. A None value indicates
    that there is no earlier events on the signed variable (i.e. the event is the
    first one on the signed variable).
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    cause: Causes.AnyCause
    """The cause of this event."""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#    @property
#    def literal(self) -> Lit:
#        return Lit(self.signed_var, self.bound)

#################################################################################
# DOC: OK 23/10/23
#################################################################################

class InvalidBoundUpdate(NamedTuple):
    """
    Represents an encountered conflict, corresponding to an invalid bound update
    (i.e. an attempt to entail a literal which would cause its variable's domain to become empty).

    It will be analyzed as part of conflict analysis, to produce a clause for the solver to "learn".
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    literal: Lit
    """The literal whose entailment would cause its variable's domain to become empty."""

    cause: Causes.AnyCause
    """The cause for the attempt to make the invalid bound update."""

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

class ReasonerBaseExplanation(NamedTuple):
    """
    Represents a "starting point" or "base" explanation
    for a conflict encountered by a reasoner.

    It will be refined into a full explanation as part of conflict analysis,
    to produce a clause for the solver to "learn".
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    literals: Tuple[Lit,...]    # TODO
    """The literals of the base / "starting point" explanation made by the reasoner."""

#################################################################################
# DOC: TODO
#################################################################################

class ConflictAnalysisResult(NamedTuple):
    """
    Represents the results of conflict analysis, namely the clause for the solver
    to "learn" (i.e. integrate in a SATReasoner after backtracking to an appropriate
    earlier decision level - in our case, the 1st Unique Implication Point (1UIP))
    to prevent the analyzed conflict from being encountered again.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    asserting_clause: Tuple[Lit,...]
    """
    The literals composing the asserting clause obtained as a result of conflict analysis.

    Should be simplified before being learned.

    TODO: explain what an asserting clause is.
    """

    resolved_literals: Dict[SignedVar, Bound] #REVIEW ? # Tuple[Literal,...]
    """
    The resolved literals that participate in the conflict.
    Stored as a dictionary instead of a tuple of literals.
    
    These literals appeared in an explanation when producing the asserting
    clause, but were "recursively" replaced by their own explanation (and
    thus do not appear in the clause).

    They are typically exploited by some branching heuristics (e.g. LRB) to
    identify literals participating in conflicts.    
    """

#################################################################################