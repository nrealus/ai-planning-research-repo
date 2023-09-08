from __future__ import annotations

#################################################################################

from typing import Dict, List, NamedTuple, Optional, Set, Tuple, Union, Callable
from abc import abstractmethod, ABC

from fundamentals import (
    Var, ZERO_VAR,
    SignedVar, BoundVal, 
    Lit, TRUE_LIT, FALSE_LIT,
)
from constraint_expressions import (
    ElemConstrExpr
)

import heapq

#################################################################################
#################################################################################
#                                   CONTENTS:
# - SOLVER AUXILIARY CLASSES:
#   - DECISIONS
#   - CAUSES
#   - EVENT
#   - INVALID BOUND UPDATE INFO & REASONERS RAW EXPLANATION
#   - CONFLICT ANALYSIS RESULT
#   - REASONERS (INTERFACE / ABSTRACT BASE CLASS)
#
# - SOLVER CLASS:
#   - UTILITY METHODS
#   - BOUND VALUE UPDATE METHOD
#   - DECISION LEVEL INCREMENTATION
#   - BACKTRACKING
#   - PROPAGATION
#   - CONFLICT ANALYSIS, EXPLANATION GENERATION
#################################################################################
#################################################################################

#################################################################################
# DECISIONS
#################################################################################

class Decisions(ABC):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class SetLiteral(NamedTuple):
        """
        Represents a decision to increment the decision level and
        to set / entail / enforce a certain literal as true.
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
        """This cause corresponds to a ("set literal") decision to attempt to update a bound."""
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Encoding(NamedTuple):
        """
        This cause corresponds to the posting (or "activation") of a constraint,
        i.e. an attempt to set a reification literal of a constraint (i.e. set the
        lower bound of the reification literal's variable to 1).
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ImplicationPropagation(NamedTuple):
        """
        This cause corresponds to an attempt to perform of implication propagation.

        Implication propagations are triggered on bound updates of non-optional
        variables (notably presence variables) and concern literals that are
        "directly implied" by the newly entailed literal. Indeed, the solver has
        an implication graph, on non-optional variables' literals. It stores
        implications that must be satisfied.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        literal: Lit
        """The literal whose entailment triggered the implication propagation."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class PresenceOfEmptyDomain(NamedTuple):
        """
        This cause corresponds to an attempt to set an optional variable's presence
        variable/literal to false, because its domain became empty.
        
        Recall that an optional variables is allowed to have empty domain (lower
        bound strictly greater than upper bound) iff it is "absent" from the model,
        i.e its presence variable's (which is always non optional) domain is reduced
        to 0 (i.e. the negation of the optional variable's presence literal is entailed).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        literal: Lit
        """The literal whose entailment made its variable's domain become empty."""

        cause: Causes.AnyCause
        """The cause of literal's entailment."""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ReasonerInference(NamedTuple):
        """This cause corresponds to an inference made by a reasoner during propagation."""
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        reasoner: Reasoner
        """The reasoner that made the inference."""

        inference_info: object          # TODO
        """The inference information"""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyCause = Union[Decision,
                     Encoding,
                     ImplicationPropagation,
                     PresenceOfEmptyDomain,
                     ReasonerInference]
    """Type alias representing all types of causes."""

#################################################################################
# EVENTS
#################################################################################

class Event(NamedTuple):
    """Represents an event, i.e. (meta)data on a bound update of a signed variable."""
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    signed_var: SignedVar
    """The signed variable whose bound was updated with this event."""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    new_bound_value: BoundVal
    """The new (updated) value of the signed variable's bound."""
    
    previous_bound_value: BoundVal
    """The previous value that the signed variable's bound had, before this event."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    index: Tuple[int, int]
    """
    The index of this event (in the solver's `events_trail`).
    
    It is a "double index": the first int of the tuple corresponds to the decision
    level, and the second one corresponds to the event's index in that decision level.
    """
    
    previous_bound_value_event_index: Optional[Tuple[int, int]]
    """
    The index of the event (in the event trail) that set the signed variable's
    previous bound value.
    
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
    Represents a contradiction corresponding to an invalid bound update (i.e. to
    an empty domain for an non-optional variable).
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    literal: Lit
    """The literal whose entailment caused its variable's domain to become empty."""

    cause: Causes.AnyCause
    """The cause for the entailment of the literal."""

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

class ReasonerRawExplanation(NamedTuple):
    """
    Represents the "raw" or "starting point" explanation that a reasoner may make
    of an encountered contradiction. It is refined into a "full" explanation by
    (the main component of) the solver.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    literals: Tuple[Lit,...]
    """The literals of the "raw" or "starting" point explanation made by the reasoner."""

#################################################################################
# CONFLICT ANALYSIS RESULT
#################################################################################

class ConflictAnalysisResult(NamedTuple):
    """
    Represents information obtained after explanation / conflict analysis.

    Conflicts happen when propagation fails / leads to / encounters a conflict / contradiction.
    They need to be explained into a new clause for the solver to "learn" to
    prevent it from happening again in the search. This is done by adding this
    clause to the clause database of the solver (or rather the `SATReasoner`'s), 
    after backtracking to an appropriate backtrack level (in our case, the 1st Unique Implication Point / 1UIP).
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    asserting_clause_literals: Tuple[Lit,...]
    """
    The asserting clause (as a set of literals). Not yet learned (i.e. not yet
    in the clause database). They are tightened before this structure's instantiation.

    To avoid the conflict, at least one of the literals will have to be true.
    """

    resolved_literals_storage: Dict[SignedVar, BoundVal] #CHECKME ? # Tuple[Literal,...]
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
# REASONER
#################################################################################

class Reasoner():
    """
    Base class (or rather interface) for reasoners.
    
    Reasoners are specialized inference engines / "modules" of the (main) solver.
    They are queried by the solver's propagation method one by one, to perform
    specialized propagation / inference. Each of them processes newly accumulated
    bound updates / events, including those resulting from inference / propagation
    by other reasoners, until nothing new can be inferred. They also help the main
    solver by providing it with an initial (CHECKME?) explanation, when a conflict
    is found during their propagation. This explanation may be further refined
    by the main solver when doing conflict analysis.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_solver_increment_decision_level(self,
        solver:Solver,
    ) -> None:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_solver_backtrack_one_level(self,
        solver: Solver,
    ) -> None:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def propagate(self,
        solver: Solver,
    ) -> Optional[InvalidBoundUpdateInfo | ReasonerRawExplanation]:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def explain(self,
        explanation_literals: List[Lit],
        literal: Lit,
        inference_cause: Causes.ReasonerInference,
        solver: Solver,
    ) -> None:
        """
        TODO
        """
        pass

#################################################################################
# SOLVER
#################################################################################

class Solver():
    """
    The main solver class.
    """

    #############################################################################
    # CONSTRUCTOR
    #############################################################################

    def __init__(self):

        self._vars_id_counter: int = 0
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.vars: Dict[bool, Set[Var]] = { False: set(), True: set() }
        """
        Stores the variables of the problem.

        The controllable variables are in the set under key True,
        and the uncontrollable ones are in the set under key False.
        """

        self.vars_presence_literals: Dict[Var, Lit] = {}
        """
        Maps variables to their presence literals.

        Variables of presence literals have to be non-optional
        (i.e. have the TRUE_LIT as their presence literal).
        """

        self.non_optionals_implication_graph: Dict[SignedVar, Dict[BoundVal, Set[Lit]]] = {}
        """
        Represents an implication graph on literals of non-optional variables.

        Can be seen as a set of "guarded" adjacency sets. Indeed, a signed variable is
        mapped to a dictionary, with keys "guarding" the values, which are adjacency sets.
        
        As such, an implication [svar1 <= a] => [svar2 <= b] is encoded as:
        { svar1 : { a : [svar2 <= b] } }. As such, if we want to check if
        [svar1 <= c] implies [svar2 <= d], we iterate through guard values
        weaker (>=) than c, and search for any literal entailing [svar2 <= d]
        (i.e. on the same signed variable (svar2) and with weaker (>=) bound than d).
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.bound_values: Dict[SignedVar, BoundVal] = {}
        """
        The main "domains" structure.
        Stores the upper and lower bounds of variables' domains (at the current decision level).
        """

        self.bound_values_event_indices: Dict[SignedVar, Optional[Tuple[int, int]]] = {} 
        """
        Stores the indices in `events_trail` of events that set the current bounds of variables.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.decision_level: int = 0
        """The current decision level of the solver."""

        self.events_trail: List[List[Event]] = [[]]
        """
        The trail of events.

        Uses double indices: the index in outer list is the decision level of the event.
        The index in the inner list is the position of the event in that decision level.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.scopes: Dict[Tuple[Lit,...], Lit] = {}
        """
        Stores conjunctions of (presence) literals corresponding to (conjunctive)
        scopes that have been defined in the problem, as well as the associated
        "scope literals" representing them.

        A conjunctive scope is created when we want to refer to a subset of the
        problem that exists iff all required scopes are present. For example, the 
        expression "a <= b" is defined iff both a and b are present. It can be said
        to exist in the conjunctive scope "presence(a) & presence(b)".
        """

        self.scopes_reverse: Dict[Lit, Tuple[Lit,...]] = {}
        """
        The reverse of `scopes`.
        """

        self.scopes_tautologies: Dict[Lit, Lit] = {}
        """
        For each scope literal, associates a literal (on an optional variable).
        When we're in that scope (i.e. the scope literal is true, i.e. all the
        literals defining it are true) that literal is always true. When we're
        not in that scope, the variable of this literal is absent. As such, this
        literal can indeed be called "tautology of the scope".
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.constraints: List[Tuple[ElemConstrExpr, Lit]] = []
        """
        Stores pairs consisting of a constraint (in elementary form) and a literal,
        stating that the literal must be true iff the constraint is true.

        CHECKME? Both "real" reified constraints that were defined in the problem
        and "artificial"/"intermediary" constraints can be found here.
        Apart from pairs consisting of a (reified) constraint and its reification
        literal, there can be pairs where the constraint is simply the satisfaction
        of a reification literal of another constraint. This allows to enforce
        a sort of "chain of constraints". CHECKME?
        """

        self.reifications: Dict[ElemConstrExpr, Lit] = {}
        """
        Stores reification literals of constraints that were defined in the problem (in
        their "elementary" form) and reified.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.vars[False].add(ZERO_VAR)
        self.vars_presence_literals[ZERO_VAR] = TRUE_LIT

        self.bound_values[SignedVar.plus(ZERO_VAR)] = BoundVal(0)
        self.bound_values[SignedVar.minus(ZERO_VAR)] = BoundVal(0)

        self.scopes[()] = TRUE_LIT
        self.scopes_reverse[TRUE_LIT] = ()
        self.scopes_tautologies[TRUE_LIT] = TRUE_LIT

    #############################################################################
    # UTILITY METHODS
    #############################################################################

    def is_literal_entailed(self,
        literal: Lit,
    ) -> bool:
        """
        Args:
            literal (Literal): A literal.

        Returns:
            bool: Whether `literal` is currently entailed / known to be true
            at the current decision level (i.e. the current bound value on its
            signed variable is stronger than its own).
        """ 

        return self.bound_values[literal.signed_var].is_stronger_than(literal.bound_value)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_literal_value(self,
        literal: Lit,
    ) -> Optional[bool]:
        """
        Args:
            literal (Literal): A literal.

        Returns:
            True if `literal` is true (i.e. currently entailed).

            False if it is false (i.e. its negation is currently entailed).

            None otherwise (i.e. `literal` is unbound: it isn't yet known to be true or false).
        """ 

        if self.is_literal_entailed(literal):
            return True
        elif self.is_literal_entailed(literal.negation()):
            return False
        else:
            return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_assignment_complete(self) -> bool:
        """
        Returns:
            bool: Whether all controllable variables' domains are either singletons
        (lower bound equal to upper bound) or empty (lower bound greater than upper bound).
        
        Indeed, the domain of an optional variable that is absent is allowed to be empty.
        """

        return all([self.bound_values[SignedVar.plus(var)]
                    .is_stronger_than(-self.bound_values[SignedVar.minus(var)])
                    for var in self.vars[True]])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_implication_true(self,
        literal_from: Lit,
        literal_to: Lit,
    ) -> bool:
        """
        Returns:
            bool: Whether the implication `literal_from` => `literal_to` is true / satisfied.
        """
        
        # Obvious cases where the implication is known to be true.
        if (literal_to == TRUE_LIT
            or literal_from == FALSE_LIT
            or literal_from.entails(literal_to)
            or self.is_literal_entailed(literal_from.negation())
            or self.is_literal_entailed(literal_to)
        ):
            return True 

        # When there are no "incoming edges" to `literal_to` in the implication
        # graph (i.e. "outgoing edges" from `literal_to`.negation()), there
        # can't be any implications to `literal_to`. This check is possible
        # because for each (x -> y) "edge" to add in the implication graph, we
        # also explicitly add a (!y -> !x) "edge".
        if (not literal_to.signed_var.opposite_signed_var()
            in self.non_optionals_implication_graph
        ):
            return False

        # Depth first search through the implication graph, starting
        # at `literal_from`. Look for a literal that entails `literal_to`
        # to determine whether `literal_from` implies `literal_to`.

        stack: List[Lit] = [literal_from]
        visited: Dict[SignedVar, BoundVal] = {}

        while stack:
            lit = stack.pop()

            # If the current literal entails `literal_to`, then
            # we won: `literal_to` is reachable from `literal_from`, 
            # thus `literal_from` does imply `literal_to`
            if lit.entails(literal_to):
                return True

            if lit.signed_var not in visited:
                visited[lit.signed_var] = lit.bound_value
            
            # If we have already visited a literal that entails the current
            # one, then there is no hope in pursuing the search further in
            # this path (because the search is depth-first).
            elif lit.bound_value.is_stronger_than(visited[lit.signed_var]):
                continue                                                    

            # If the current literal doesn't imply anything, then it can't
            # imply possibly `literal_to`: no hope in pursuing the search
            # further in this path (because the search is depth-first).
            if not lit.signed_var in self.non_optionals_implication_graph:
                continue
            
            # Push literals known to be "directly implied" by
            # the current literal to the search stack.
            for guard_bound, adjacency_set in self.non_optionals_implication_graph[lit.signed_var].items():

                if lit.bound_value.is_stronger_than(guard_bound):
                    stack.extend(adjacency_set)

        return False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_first_event_implying_literal(self,
        literal: Lit,
    ) -> Optional[Event]:
        """
        Args:
            literal (Literal): A literal.

        Returns:
            None: If there are no events (yet) in `events_trail` on `literal`'s
            signed variable.

            Event: The first event `events_trail` that makes `literal` true.

        Invariants / assumptions / requirements:
            `literal` must be currently entailed.

        The method works by walking in reverse order through events on the
        signed variable of `literal`. The first event that makes `literal` true 
        is the one whose previous value was weaker than `literal`'s bound value
        (i.e. the literal wasn't entailed before this event).
        """

        assert self.is_literal_entailed(literal)

        ev_index = self.bound_values_event_indices.get(literal.signed_var, None)

        if ev_index is None:
            return None

        ev: Event

        while True:
            dl, i = ev_index
            ev = self.events_trail[dl][i]

            if not ev.previous_bound_value.is_stronger_than(literal.bound_value):
                break

            ev_index = ev.previous_bound_value_event_index
            if ev_index is None:
                break
        
        return ev

    #############################################################################
    # BOUND VALUE UPDATE
    #############################################################################

    def set_bound_value(self,
        signed_var: SignedVar,
        bound_value: BoundVal,
        cause: Causes.AnyCause,
    ) -> bool | InvalidBoundUpdateInfo:
        """
        Arguably the most important method of the solver.
        (along with the propagate method)

        Attempts to set a new bound value to a signed variable. This is
        equivalent to setting / entailing / enforcing the corresponding literal.

        When the bound update is useless (the variable is optional and absent,
        or the current bound is stronger than the given one), doesn't do
        anything and returns False.

        When the bound update leads to an empty domain for this given signed
        variable's variable, there are 2 possible cases:
            
            - If the variable is non-optional, immediately return a `InvalidBoundUpdateInfo`.
                        
            - If the variable is optional, sets the new bound and attempts to set
            the negation of the variable's presence literal with a new call to
            `set_bound_value`. The results of this recursive call are then returned.

        If the variable is non-optional, the given new bound is not useless (i.e.
        strictly stronger than the current one), and it doesn't make the variable's
        domain empty, lazily" propagates the consequences of this update to non-optional 
        variables in the `non_optional_vars_implication_graph`, that may be concerned
        by it by recursively calling `set_bound_value`. If any of those calls leads
        to a failure / invalid bound update, the corresponding `InvalidBoundUpdateInfo`
        will be returned.

        Finally, when the bound was was successfully updated without leading to an
        empty domain for any variable, True is returned.
        """

        prez_lit = self.vars_presence_literals[signed_var.var]

        # If variable is proven absent (i.e. the negation of its presence
        # literal is entailed), we return False as there is no update to 
        # the domain. Note that non optional variables are always present
        # (i.e. their presence literal is TRUE_LIT) so this indeed doesn't
        # apply to them.
        if self.is_literal_entailed(prez_lit.negation()):
            return False

        # If the new candidate bound value is weaker than the
        # current bound value, (i.e. the current bound value is
        # stronger than the new candidate bound value) there is no
        # update to the domain of the variable and we return False.
        if self.bound_values[signed_var].is_stronger_than(bound_value):     
            return False

        # If the new candidate bound value leads to an empty domain.
        
        if (not (-self.bound_values[signed_var.opposite_signed_var()])  
            .is_stronger_than(bound_value)
        ):

            # If the variable is not optional (i.e. always present),
            # we immediately return the contradiction.
            if prez_lit == TRUE_LIT:
                return InvalidBoundUpdateInfo(Lit(signed_var, bound_value), cause)

            # If the variable is optional and its domain is empty, it
            # can only be absent. As such, we attempt to enforce the
            # entailment of the negation of its presence literal.
            else:
                return self.set_bound_value(prez_lit.negation().signed_var,
                                            prez_lit.negation().bound_value,
                                            Causes.PresenceOfEmptyDomain(Lit(signed_var, bound_value), cause))
        else:

            # If the new candidate bound value is stronger and the current
            # bound value and is valid (doesn't lead to an empty domain), the
            # event corresponding to this update is pushed to the trail, and
            # the current domain of the variable is updated with the new bound.

            ev = Event(signed_var,
                       bound_value,
                       self.bound_values[signed_var],
                       (self.decision_level, len(self.events_trail[self.decision_level])-1),
                       self.bound_values_event_indices.get(signed_var, None),
                       cause)
            
            self.events_trail[self.decision_level].append(ev)

            self.bound_values[signed_var] = bound_value
            self.bound_values_event_indices[signed_var] = ev.index

            # If the variable is optional, we can already return True.
            if prez_lit != TRUE_LIT:
                return True
            
            # If the variable is not optional, we can perform lazy propagation.
            #
            # We need to succesfully propagate the direct implications
            # of all events/updates caused by this bound update attempt.
            # Again, this is only done for non optional variables, as we
            # do not allow literals of optional variables to appear in
            # the implication graph. We do this by looping through the
            # direct implications of all events / updates pushed to the
            # trail since this method is called.

            i = len(self.events_trail[self.decision_level])-2
            j = i+1

            while i < j:
                i += 1
                pending_lit = Lit(self.events_trail[self.decision_level][i].signed_var,
                                  self.events_trail[self.decision_level][i].new_bound_value)
                
                # Propagation is done exactly like in the first part of the function, simply
                # taking into account the fact that the implied literal's variable can't be optional.

                literals_directly_implied_by_pending_literal = []
                for guard_bound, adjacency_set in self.non_optionals_implication_graph[pending_lit.signed_var].items():

                    if pending_lit.bound_value.is_stronger_than(guard_bound):
                        literals_directly_implied_by_pending_literal.extend(adjacency_set)

                for implied_lit in literals_directly_implied_by_pending_literal:

                    # If the implied literal's signed variable bound is weaker
                    # than its current one, nothing to do.
                    if (self.bound_values[implied_lit.signed_var]
                        .is_stronger_than(implied_lit.bound_value)
                    ):
                        continue

                    # If the implied literal's variable's domain is lead to be empty, propagation
                    # is unsuccessful and a conflict indicating the implied literal as the cause
                    # for failure is returned. Because we know the var of the implied literal to
                    # be non-optional, it cannot be made absent to resolve the problem.
                    if ((-self.bound_values[implied_lit.signed_var.opposite_signed_var()])
                        .is_stronger_than(implied_lit.bound_value)
                    ):
                        return InvalidBoundUpdateInfo(implied_lit, cause)
                    
                    # If the implied literal's variable's bound is stronger than its current one
                    # and is valid (doesn't lead to an empty domain) current, it is applied and
                    # a new event corresponding to this update is pushed to the trail.

                    ev = Event(implied_lit.signed_var,
                               implied_lit.bound_value,
                               self.bound_values[implied_lit.signed_var],
                               (self.decision_level, j+1),
                               self.bound_values_event_indices[implied_lit.signed_var],
                               Causes.ImplicationPropagation(implied_lit))

                    self.events_trail[self.decision_level].append(ev)

                    self.bound_values[implied_lit.signed_var] = implied_lit.bound_value
                    self.bound_values_event_indices[signed_var] = ev.index
                    j += 1

        return True

    # TODO: minimal domain size for uncontrollable variables ?
    # (it could be defined by a variable itself, since this minimal domain size depends on the presence of uncontrollable edges/links (stnu))

    #############################################################################
    # DECISION CHOICE
    #############################################################################

    # TODO
    def choose_next_decision(self) -> Decisions.AnyDecision:

        raise NotImplementedError

    #############################################################################
    # DECISION LEVEL INCREMENTATION
    #############################################################################

    def increment_decision_level(self,
        reasoners: Tuple[Reasoner,...],
    ) -> None:
        """
        Increments the current decision level (by 1).

        Args:
            reasoners (Tuple[Reasoner,...]): The reasoners collaborating with the solver.

        Side effects:
            Increments the current decision level.

            Appends an empty list to `events_trail` (if its length is not less
            than the incremented decision level)
            
            Invokes all reasoners' `on_solver_increment_decision_level` "callbacks", which
            updates them internally to account for the decision level incrementation.
        """

        assert len(self.events_trail[self.decision_level]) > 0

        self.decision_level += 1

        if len(self.events_trail) == self.decision_level:
            self.events_trail.append([])
        
        for reasoner in reasoners:
            reasoner.on_solver_increment_decision_level(self)

    #############################################################################
    # BACKTRACKING
    #############################################################################

    def _undo_and_return_last_event_at_current_decision_level(self) -> Event:
        """
        Reverts the last event (at the current decision level).

        Makes corresponding updates to the current bounds values and event
        indices of previous bound values.

        Returns:
            Event: The event that was reverted.
        
        Side effects:
            Pops the last element `events_trail` (at the current - i.e. last - decision level).

            Updates the bound value of the signed variable of the event.

            Updates the dictionary that stores the indices of events that set current bound values.
        """

        assert len(self.events_trail[self.decision_level]) > 0

        ev = self.events_trail[self.decision_level].pop()

        self.bound_values[ev.signed_var] = ev.previous_bound_value
        self.bound_values_event_indices[ev.signed_var] = ev.previous_bound_value_event_index

        return ev

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def backtrack_to_decision_level(self,
        target_dec_level: int,
        reasoners: Tuple[Reasoner,...],
    ) -> None:
        """
        Backtracks to the target decision level.

        Args:
            target_decision_level (int): The target decision level to backtrack to.
            Must be >= 0.

            reasoners (Tuple[Reasoner,...]): The reasoners collaborating with the solver.

        Side effects:
            Reverts all events at all decision levels after the target one.
            
            Invokes the reasoners' `on_solver_backtrack_one_level` "callbacks", at
            each reverted decision level. This updates the reasoners internally to
            account for the backtracking.

            Sets the current decision level to the target one.
        """

        assert target_dec_level >= 0

        while self.decision_level > target_dec_level:

            for reasoner in reasoners:
                reasoner.on_solver_backtrack_one_level(self)

            n = len(self.events_trail[self.decision_level])
            for _ in range(n):
                self._undo_and_return_last_event_at_current_decision_level()

            self.decision_level -= 1

    #############################################################################
    # PROPAGATION
    #############################################################################

    def propagate(self,
        reasoners:Tuple[Reasoner,...],
    ) -> Optional[Tuple[InvalidBoundUpdateInfo | ReasonerRawExplanation, Reasoner]]:
        """
        The propagation method of the solver.

        Args:
            reasoners (Tuple[Reasoner,...]): The reasoners collaborating with the solver.

        Returns:
            None: if the propagation was successful
            Tuple[ConflictEncounter, Reasoner]: if a contradiction was
        encountered during a reasoner's inference.

        For all reasoners, propagates changes / new events. The propagation
        process stops either when nothing new can be inferred (success), or
        when a contradiction is detected by one of the reasoners (failure).
        """

        while True:
            num_events_at_propagation_start = len(self.events_trail[self.decision_level])

            for reasoner in reasoners:
                contradiction = reasoner.propagate(self)

                if contradiction is not None:
                    return (contradiction, reasoner)
        
            if num_events_at_propagation_start == len(self.events_trail[self.decision_level]):
                break

        return None

    #############################################################################
    # CONFLICT ANALYSIS, EXPLANATION GENERATION
    #############################################################################

    def _add_implying_literals_to_explanation(self,
        explanation_literals: List[Lit],
        literal: Lit,
        cause: Causes.AnyCause,
        explain_function: Callable[[List[Lit], Lit, Causes.ReasonerInference, Solver], None],
    ) -> None:
        """
        Computes a set of literals l_1, ..., l_n such that:
         - l_1 & ... & l_n => literal
         - each l_i is entailed at the current decision level.
        Places them in `explanation_literals`.
         
        Assumptions:
         - literal is not entailed in the current state
         - cause provides the explanation for asserting literal (and is not a decision)

        Args:
            explanation_literals (List[Lit]): The list of literals making up the explanation.

            literal (Lit): The literal whose implying literals we want to add to the explanation.

            cause (Cause): The cause for the event that to the contradiction that we're explaining.

            explain_function (Callable[[List[Lit], Lit, ReasonerInferenceCause, Solver], None]): The
            external function that may participate in building the explanation (basically the `explain`
            function of `Reasoner`)

        Side effects:
            Modifies `explanation_literals`.
        """

        # In this function, the literal shouldn't be true yet,
        # but it should be immediately implied.
        assert not self.is_literal_entailed(literal)

        match cause:

            case Causes.ReasonerInference():
                # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => literal
                explain_function(explanation_literals, literal, cause, self)

            case Causes.ImplicationPropagation():
                explanation_literals.append(cause.literal)

            case Causes.PresenceOfEmptyDomain():
                explanation_literals.append(cause.literal.negation())

                match cause.cause:

                    case Causes.ReasonerInference():
                        # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => cause.literal
                        explain_function(explanation_literals, cause.literal, cause.cause, self)

                    case Causes.ImplicationPropagation():
                        explanation_literals.append(cause.cause.literal)
                    
                    case _:
                        assert False

            case _:
                assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def explain_invalid_bound_update(self,
        invalid_bound_update_info: InvalidBoundUpdateInfo,
        explain_function: Callable[[List[Lit], Lit, Causes.ReasonerInference, Solver], None],
    ) -> ConflictAnalysisResult:
        """
        Given an invalid bound update of a literal 'l',
        returns an asserting clause 'l_1' & ... & 'l_n' => not 'l_dec' where:
         - the literals 'l_i' are entailed at the previous decision level (of the current state)
         - the literal 'l_dec' is the decisions that was taken at the current decision level

        The update of 'l' must not directly originate from a decision,
        as it is necessarily the case that 'not l' holds in the current
        state. It is thus considered a logic error to enforce an obviously
        wrong decision.

        Args:
            invalid_bound_update_info (InvalidBoundUpdateInfo): The data of
            the invalid bound update conflict to explain.

            explain_function (Callable[[List[Lit], Lit, ReasonerInferenceCause, Solver], None]): The
            external function that may participate in building the explanation
            (basically the `explain` function of `Reasoner`)
        
        Returns:
            ConflictAnalysisResult: an object containing the results of the
            conflict analysis (the asserting clause and set of resolved literals).
        """
        
        # Remember that an update is invalid iff its negation holds AND
        # the affected variable is present.

        # The base of the explanation is ('not l' v 'l')
        explanation_starting_literals: List[Lit] = [invalid_bound_update_info.literal.negation()]

        # However 'l' does not hold in the current state and it needs
        # to be replaced, with a set of literals 'l_1' v ... v 'l_n',
        # such that 'l_1' v ... v 'l_n' => 'l'. As such, the explanation
        # becomes 'not l' v 'l_1' v ... v 'l_n', and all its disjuncts
        # ('not l' and all 'l_i') hold in the current state.
        self._add_implying_literals_to_explanation(explanation_starting_literals,
                                                   invalid_bound_update_info.literal,
                                                   invalid_bound_update_info.cause,
                                                   explain_function)

        # The explanation clause 'not l' v 'l_1' v ... v 'l_n' must now be 
        # transformed into 1st Unique Implication Point form.
        return self.refine_explanation(explanation_starting_literals,
                                       explain_function)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def refine_explanation(self,
        explanation_literals: List[Lit],
        explain_function: Callable[[List[Lit], Lit, Causes.ReasonerInference, Solver], None],
    ) -> ConflictAnalysisResult:
        """
        Refines an explanation into an asserting clause.
        
        Args:
            explanation_literals (List[Literal]): The list of literals making up the explanation.

            explain_function (Callable[[List[Lit], Lit, ReasonerInferenceCause, Solver], None]): The
            external function that may participate in building the explanation
            (basically the `explain function of `Reasoner`)

        Returns:
            ConflictAnalysisResult: an object containing the results of the
            conflict analysis (the asserting clause and set of resolved literals).

        Side effects:
        
            Modifies `explanation_literals`

            ! A partial backtrack (within the current decision level) will occur
            in the process ! This is necessary to provide explainers (reasoners)
            with the exact state in which their decisions were made.

        NOTE: There is no need to "synchronize"/update the reasoners' earliest
        unprocessed event index because of this partial backtracking. Indeed,
        right after this explanation is made/refined as part of conflict analysis,
        we will backtrack to an earlier decision level anyway. And during with
        that backtracking, the earliest unprocessed event index of each reasoner
        will be reset to 0 (at that decision level). As such, the partial backtracking
        that happens in this method doesn't cause any problem for reasoners.
        """

        # Literals falsified at the current decision level,
        # we need to proceed until there is a single one left (1UIP).
        # The int is MINUS the index of the event (in the events trail)
        # where the literal was implied. It acts as the priority value
        # of the maxheap. But since the Python heapq is a minheap
        # and we want a maxheap, we need to invert the priority values...

        prio_queue: List[Tuple[Tuple[int,int], Lit]] = []
        heapq.heapify(prio_queue)

        # Literals that are beyond the current decision and
        # will be part of the final asserting clause.
        asserting_clause_literals: List[Lit] = []

        resolved_literals: Dict[SignedVar, BoundVal] = {}

        while True:

            for lit in explanation_literals:

                if self.is_literal_entailed(lit):

                    first_impl_ev = self.get_first_event_implying_literal(lit)

                    # If lit is implied at decision level 0, then it
                    # is always true. So we can discard it.

                    if first_impl_ev is None:
                        continue

                    ev_i_dl, ev_i = first_impl_ev.index

                    if ev_i_dl == 0:
                        continue

                    # If lit is implied at the current decision
                    # level, then add it to the queue.
                    #
                    # But if lit is implied at a decision level
                    # before the current one, then its negation
                    # will appear in the final clause (1UIP).

                    if ev_i_dl == self.decision_level:
                        heapq.heappush(prio_queue, ((-ev_i_dl, -ev_i), lit))

                    elif ev_i_dl < self.decision_level:
                        asserting_clause_literals.append(lit.negation())

                    else:
                        assert False
                
                # If lit is is not entailed, it must have been added in
                # an eager propagation. Even if it was not necessary for
                # this propagation to occur, it must be part of the clause
                # for correctness.
                else:
                    asserting_clause_literals.append(lit.negation())
                
            # If the queue is empty, it means that all literals in the clause
            # will be at decision levels earlier than the current decision level.
            # This can happen if we are at the top decision level, or if we
            # had a lazy propagator that didn't immediately detect the 
            # inconsistency # NOTE: need to be better understand this.
            #
            # Corollary: if dl is 0, the derived clause must be empty.
            if not prio_queue:
                return ConflictAnalysisResult(tuple(asserting_clause_literals),
                                              resolved_literals)
            
            # At this point, we haven't reached the 1st UIP yet.

            # Select the latest falsified literal from the queue.
            _prio_queue_head = heapq.heappop(prio_queue)
            ((ev_i_dl, ev_i), lit) = ((-_prio_queue_head[0][0], -_prio_queue_head[0][1]), _prio_queue_head[1])

            # However, the queue might contain more than onen reference
            # to the same event. Because of the priority of the queue
            # (event indices), they are necessarily contiguous.
            while prio_queue:
                _prio_queue_head = prio_queue[0]    # peek
                ((next_dl, next_ev_i), next_lit) = ((-_prio_queue_head[0][0], -_prio_queue_head[0][1]), _prio_queue_head[1])

                # If the event is the same, pop it from the queue
                # and keep the most general one of them as 'lit'.
                # (i.e. the one with the weaker bound value).
                if (next_dl, next_ev_i) == (ev_i_dl, ev_i):
                    heapq.heappop(prio_queue)
                    if lit.bound_value.is_stronger_than(next_lit.bound_value):
                        lit = next_lit
                # If the event isn't the same, none of the remaining
                # ones will be either, because of the priority of the queue.
                else:
                    break

            # If the queue is empty, we have reached the 1UIP.
            # The contents of asserting_clause_literals now corresponds
            # to a conjunction of literals that imply 'not lit'.
            # Thus, to finish building the asserting clause, we just
            # need to add 'not lit' to asserting_clause_literals.
            if not prio_queue:
                asserting_clause_literals.append(lit.negation())
                return ConflictAnalysisResult(tuple(asserting_clause_literals),
                                              resolved_literals)

            # Now, we need to until the latest falsifying event. This
            # will undo some of the changes, but we will remain in the
            # same decision level (see function description for the
            # reason behind this partial backtracking). Indeed, the event
            # cannot be a decision, because otherwise it would have been
            # detected as a UIP earlier.

            cause: Optional[Causes.AnyCause] = None
            while ev_i < len(self.events_trail[self.decision_level]):
                ev = self._undo_and_return_last_event_at_current_decision_level()
                cause = ev.cause

            assert cause is not None

            resolved_literals[lit.signed_var] = min(resolved_literals.get(lit.signed_var,
                                                                          lit.bound_value),
                                                    lit.bound_value)

            # Add a set of literals whose conjunction implies lit to explanation_literals
            self._add_implying_literals_to_explanation(explanation_literals,
                                                       lit,
                                                       cause,
                                                       explain_function)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_decision_level_to_backtrack_to(self,
        asserting_clause_literals: Tuple[Lit,...],
    ) -> Tuple[bool, int, Optional[Lit]]:
        """
        Returns the appropriate backtracking level for the clause formed by the
        given clause literals, and the literal that is asserted at that level.
        Also returns True if the clause is conflicting at the top decision level
        (this makes the clause a contradiction) and False otherwise.
        
        Normally, in the 1UIP backtracking scheme (1st Unique Implication Point),
        the decision level to backtrack to should be the largest one (i.e. "closest"
        to the conflict) at which the clause is unit. However, the explanation of
        eager propagation of optionals might generate explanations where some literals
        are not violated. These are ignored when determining the backtrack level.
        
        If there is more than one violated literal at that level, then no literal is
        asserted and the determined backtrack level is further decreased by 1. This might
        occur with clause sharing.
        """
         
        max_dl = 0
        next_max_dl = 0

        asserted_literal: Optional[Lit] = None

        for literal in asserting_clause_literals:
            literal_neg = literal.negation()

            if not self.bound_values[literal_neg.signed_var].is_stronger_than(literal_neg.bound_value):

                first_impl_ev = self.get_first_event_implying_literal(literal_neg)

                if first_impl_ev is None:
                    continue

                (dl, _) = first_impl_ev.index
                if dl > 0:
                    if dl > max_dl:
                        next_max_dl = max_dl
                        max_dl = dl
                        asserted_literal = literal
                    elif dl > next_max_dl:
                        next_max_dl = dl

        if max_dl == 0:
            return (True, 0, None)
        elif max_dl == next_max_dl:
            return (False, max_dl-1, None)
        else:
            return (False, next_max_dl, asserted_literal)

#################################################################################