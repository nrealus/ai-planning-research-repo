"""
TODO
"""

from __future__ import annotations

#################################################################################

from abc import ABC
from typing import (Dict, Generic, List, NamedTuple, Optional, Sequence, Set,
                    Tuple, TypeVar, Union)

from src.fundamentals import BoundVal, Lit, SignedVar

#################################################################################
# LITERAL GUARDED SETS / SETS GUARDED BY LITERALS
#################################################################################

T = TypeVar('T')

class SetGuardedByLiterals(Generic[T]):
    """
    Represents a "guarded" collection/set of elements of (generic)
    type `T`. Each element is "guarded" by a literal (as well as
    all literals weaker than it, which is implied).

    This class is most notably used for the implication graph on non optional
    variables in `Solver`, as well as for (watched) literals' "watchlists" in
    `SATReasoner` and `DiffReasoner`.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def __init__(self):
        self._data: Dict[SignedVar, Dict[BoundVal, Set[T]]] = {}
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add(self,
        element: T,
        guard_literal: Lit,
    ) -> None:
        """
        Adds a new `element` guarded by `guard_literal` to the colleciton.

        Args:
            element: An element to add to the collection.

            guard_literal: The literal that should guard `element`.
        
        Raises:
            ValueError: If `element` is already present and guarded by `guard_literal`.

        Note:
            An element can be added when it wasn't already guarded by a
            literal stronger than `guard_literal`. But these elements
            are basically duplicates, since an element being guarded
            by a certain literal implies it being guarded by all literals
            stronger than it. We do not make the effort to remove such a
            duplicate if there is any. However, when using `elements_guarded_by`,
            we return only unique elements (no duplicates), so this is not an issue.
        """
        
        if guard_literal.signed_var not in self._data:
            self._data[guard_literal.signed_var] = {}
        
        if guard_literal.bound_value not in self._data[guard_literal.signed_var]:
            self._data[guard_literal.signed_var][guard_literal.bound_value] = set()

        if element in self.elements_guarded_by(guard_literal):
            raise ValueError("Element already present (guarded by {0}).".format(guard_literal))
        
        self._data[guard_literal.signed_var][guard_literal.bound_value].add(element)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def remove(self,
        element: T,
        guard_literal: Lit,
    ) -> None:
        """
        Removes an `element` guarded by `guard_literal` from the colleciton.

        Args:
            element: An element to remove from the collection.

            guard_literal: The literal that guards `element`.
        
        Raises:
            ValueError | KeyError: If `element` is not present  \
                or not guarded by `guard_literal`.
        """
        
        self._data[guard_literal.signed_var][guard_literal.bound_value].remove(element)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def remove_all_on(self,
        signed_var: SignedVar,
    ) -> None:
        """
        Removes all elements guarded by literals on the given signed variable.
        
        Raises:
            KeyError: If no guard literal on `signed_var` is registered.
        """
        
        self._data.pop(signed_var)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def elements_guarded_by(self,
        guard_literal: Lit,
    ) -> Tuple[T,...]:
        """
        Returns all elements guarded by the given literal (as well as all
        literals stronger than it, which is implied).

        Args:
            guard_literal: The literal whose guarded elements to return.

        Returns:
            An immutable sequence (tuple), with no duplicates, containing   \
                all elements guarded by the `guard_literal`.
        """

        if guard_literal.signed_var not in self._data:
            return ()

        res = set()

        for guard_bound_value, guarded_elements in self._data[guard_literal.signed_var].items():
            if guard_literal.bound_value.is_stronger_than(guard_bound_value):
                res.update(guarded_elements)

        return tuple(res)
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def has_elements_guarded_by_literals_on(self,
        signed_var: SignedVar
    ) -> bool:
        """
        Args:
            signed_var: The signed variable for which to check.

        Returns:
            Whether there are any elements guarded by a literal on  \
                the given signed variable.
        """
        
        return signed_var in self._data and len(self._data[signed_var]) > 0

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def has_elements_guarded_by(self,
        guard_literal: Lit
    ) -> bool:
        """
        Args:
            guard_literal: The literal for which we want to check for.

        Returns:
            Whether there are any elements guarded by the given literal     \
                (as well as all literals stronger than it, which is implied).
        """
        
        if guard_literal.signed_var not in self._data:
            return False
        
        for guard_bound_value in self._data[guard_literal.signed_var]:
            if guard_literal.bound_value.is_stronger_than(guard_bound_value):
                return True
        
        return False

#################################################################################
# DECISIONS
#################################################################################

class Decisions(ABC):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class SetLiteral(NamedTuple):
        """
        Represents a decision to increment the decision level and
        to set / entail / enforce a certain literal.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        literal: Lit
        """The literal to set."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Restart(NamedTuple):
        """Represents a decision to restart the search from the top decision level."""
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyDecision = Union[SetLiteral,
                        Restart]
    """Type alias representing both types of decisions."""

#################################################################################
# CAUSES 
#################################################################################

class Causes(ABC):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Decision(NamedTuple):
        """
        This cause corresponds to a decision to update a bound
        (i.e. a "set literal" decision).
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Encoding(NamedTuple):
        """
        This cause corresponds to the deactivation / forbiddance of a scope in which an
        (already reified) constraint, found to be impossible to satisfy, is defined.
        In other words, this means setting the corresponding scope literal as false.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ImplicationPropagation(NamedTuple):
        """
        This cause corresponds to an implication propagation.

        Implication propagations are triggered on bound updates of non-optional
        variables (notably presence variables) and concern literals that are implied
        by the newly entailed literal. This possible thanks to the implication
        graph on non-optional variables' literals maintained by the solver.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        literal: Lit
        """The literal whose entailment triggered the implication propagation."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class EmptyDomain(NamedTuple):
        """
        This cause corresponds to the prevention of an optional variable's domain
        becoming empty, by setting its presence variable / literal to false.

        Note that presence variables are non-optional by definition.
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
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        reasoner_id: int
        """The id of the `Reasoner` that made the inference."""

        inference_info: object          # TODO
        """The inference information"""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyCause = Union[Decision,
                     Encoding,
                     ImplicationPropagation,
                     EmptyDomain,
                     ReasonerInference]
    """Type alias representing all types of causes."""

#################################################################################
# EVENTS
#################################################################################

class Event(NamedTuple):
    """
    Represents an event, i.e. (meta)data of bound update of a signed variable 
    (i.e. entailment of a literal).
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    signed_var: SignedVar
    """The signed variable whose bound was updated with this event."""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    new_bound_value: BoundVal
    """
    The new value of the signed variable's bound.

    Note that it is necessarily strictly stronger than its previous bound value.
    """
    
    previous_bound_value: BoundVal
    """The previous value that the signed variable's bound had, before this event."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    index: Tuple[int, int]
    """
    The position / index of this event (in the solver's `events_trail`).
    
    It is a "double index": the first int of the tuple corresponds to the decision
    level, and the second one corresponds to the event's index in that decision level.
    """
    
    previous_index: Optional[Tuple[int, int]]
    """
    The position / index of the event (in the solver's `events_trail`) that set
    the signed variable's previous bound value.
    
    It is a "double index": the first int of the tuple corresponds to the decision
    level, and the second one corresponds to the event's index in that decision level.

    A None value however, indicates that this is the first event on its signed variable.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    cause: Causes.AnyCause
    """The cause of this event."""

#################################################################################
# INVALID BOUND UPDATE INFO & REASONER RAW EXPLANATION
#################################################################################

class InvalidBoundUpdateInfo(NamedTuple):
    """
    Represents an encountered conflict, corresponding to an invalid bound
    update. (i.e. an attempt to entail a literal which would cause its
    variable's domain to become empty).

    It will be analyzed as part of conflict analysis, to produce a clause
    for the solver to "learn".
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    literal: Lit
    """The literal whose entailment would cause its variable's domain to become empty."""

    cause: Causes.AnyCause
    """The cause for the attempt to make the invalid bound update."""

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

class ReasonerBaseExplanation(NamedTuple):
    """
    Represents a base / "starting point" explanation for a conflict encountered
    by a reasoner.

    It will be refined into a full explanation as part of conflict analysis,
    to produce a clause for the solver to "learn".
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    literals: Tuple[Lit,...]
    """The literals of the base / "starting point" explanation made by the reasoner."""

#################################################################################
# CONFLICT ANALYSIS RESULT
#################################################################################

class ConflictAnalysisResult(NamedTuple):
    """
    Represents the results of conflict analysis, namely the clause for the solver
    to "learn" (i.e. integrate in a SATReasoner after backtracking to an appropriate
    earlier decision level - in our case, the 1st Unique Implication Point (1UIP))
    to prevent the analyzed conflict from being encountered again.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    asserting_clause_literals: Tuple[Lit,...]
    """
    The literals composing the asserting clause obtained as a result of conflict analysis.

    Should be tightened.

    TODO: explain what an asserting clause is.
    """

    resolved_literals_storage: Dict[SignedVar, BoundVal] #REVIEW ? # Tuple[Literal,...]
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