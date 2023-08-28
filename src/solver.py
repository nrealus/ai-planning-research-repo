from __future__ import annotations

#################################################################################

from typing import Dict, List, NamedTuple, Optional, Set, Tuple, Union, Callable
from abc import ABC, abstractmethod

from fundamentals import (
    Var, ZERO_VAR,
    SignedVar, BoundVal, Lit, TRUE_LIT, FALSE_LIT,
    ConstraintElementaryExpression,
    tighten_literals,
)

import heapq

#################################################################################
#################################################################################
#                                   CONTENTS:
# - SOLVER AUXILIARY CLASSES:
#   - DECISIONS
#   - CAUSES
#   - EVENT
#   - CONFLICT INFORMATION
#   - REASONER (INTERFACE / ABSTRACT BASE CLASS)
#
# - SOLVER CLASS ITSELF
#################################################################################
#################################################################################

#################################################################################
# SOLVER DECISIONS 
#################################################################################

class SolverDecisions(ABC):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class SetLiteral(NamedTuple):
        """
        Represents a decision to set a certain literal. (i.e. set to true, entail, enforce it)
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        literal: Lit
        """
        The literal to set.
        """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Restart(NamedTuple):
        """
        Represents a decision to restart the search from the top decision level.
        """   
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyDecision = Union[SetLiteral, Restart]
    """
    Type alias representing both kinds of decisions.
    """

#################################################################################
# SOLVER CAUSES 
#################################################################################

class SolverCauses(ABC):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Decision(NamedTuple):
        """
        Represents a cause corresponding to a decision of the solver.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Encoding(NamedTuple):
        """
        Represents a cause corresponding to the encoding/posting of a constraint.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ImplicationPropagation(NamedTuple):
        """
        Represents a cause corresponding to an implication propagation.

        Implication propagations are triggered on bound updates of
        non-optional variables (notably presence variables) and 
        concern literals that are "directly implied" by the newly entailed
        literal. Indeed, the solver has an implication graph, on
        non-optional variables' literals. It stores implications that
        must be satisfied.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        literal: Lit
        """
        The literal that triggered implication propagation.
        """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class PresenceOfEmptyDomain(NamedTuple):
        """
        Represents a cause corresponding to an empty domain of an optional variable.
        
        Indeed, optional variables are allowed to have empty domains
        (lower bound strictly greater than upper bound), but if and only if they
        are "absent" from the model, i.e their (boolean) presence variables,
        which are non-optional, are not entailed.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        literal: Lit
        """
        The literal whose direct entailment leads to an empty domain of its variable.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        cause: SolverCauses.AnyCause
        """
        The cause of the event that led to the entailment of the literal.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ReasonerInference(NamedTuple):
        """
        Represents a cause corresponding to an inference made by a reasoner
        (see `SolverReasoner`), during propagation.        
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        reasoner: SolverReasoner
        """
        The reasoner that made the inference.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        inference_info: object #FIXME
        """
        The inference information.
        TODO
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyCause = Union[
        Decision,
        Encoding,
        ImplicationPropagation,
        PresenceOfEmptyDomain,
        ReasonerInference,
    ]
    """
    Type alias representing all kinds of causes of an event.
    """

#################################################################################
# SOLVER EVENTS 
#################################################################################

class SolverEvent(NamedTuple):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    signed_var: SignedVar
    """
    The signed variable whose bound was updated with this event.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    new_bound_value: BoundVal
    """
    The new (updated) value of the signed variable's bound.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    previous_bound_value: BoundVal
    """
    The previous value that the signed variable's bound had, before this event.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    previous_bound_value_event_index: Optional[Tuple[int, int]]
    """
    The index of the event (in the event trail) that set the signed variable's
    previous bound value.
    
    It is a "double index": the first int of the tuple corresponds to the decision
    level, and the second one corresponds to the event's index in that decision level.

    A None value however, indicates that this is the first event on its signed variable.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    cause: SolverCauses.AnyCause
    """
    The cause of this event.
    """

#################################################################################
# SOLVER CONFLICTS INFO
#################################################################################

class SolverConflictInfo(ABC):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class InvalidBoundUpdate(NamedTuple):
        """
        Represents a contradiction corresponding to an invalid bound
        update (leading to an empty domain for an non-optional variable).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        literal: Lit
        """
        The literal whose entailment caused its variable's domain to become empty.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        cause: SolverCauses.AnyCause
        """
        The cause of the entailment of the literal that led to the conflict.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ReasonerExplanation(NamedTuple):
        """
        Represents an explanation for a conflict, given by the reasoner which detected it.
        
        This explanation must be "refined" by the solver into an asserting / learned
        clause (conflict analysis).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        explanation_literals: Tuple[Lit,...]
        """
        The literals returned by a reasoner, as an explanation for the conflict.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class AnalysisResult(NamedTuple):
        """
        Represents information obtained after explanation / conflict analysis.

        Conflicts happen when propagation leads to a contradiction and fails.
        They need to be explained and learned into a new "learned" or "asserting"
        clause, which is then added to the clause database of the solver (or
        rather the `SATReasoner`'s), after backtracking to an appropriate
        backtrack level (in our case, the 1st Unique Implication Point / 1UIP).

        A conflict can be returned to the solver in two ways: either with an
        `InvalidBoundUpdate`, or with a `ReasonerExplanation`.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        asserting_clause_literals: Tuple[Lit,...]
        """
        The asserting clause (as a set of literals). Not yet learned (i.e.
        not yet in the clause database). They are tightened before the
        structure (`AnalysisResult`) is created.

        To avoid the conflict, at least one of the literals will have to be true.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        resolved_literals_storage: Dict[SignedVar, BoundVal] #CHECKME ? # Tuple[Literal,...]
        """
        The resolved literals that participate in the conflict. Stored as a
        dictionary instead of a tuple of literals.
        
        These literals appeared in an explanation when producing the asserting
        clause, but were "recursively" replaced by their own explanation (and
        thus do not appear in the clause).

        They are typically exploited by some branching heuristics (e.g. LRB) to
        identify literals participating in conflicts.    
        """

#################################################################################
# SOLVER REASONER
#################################################################################

class SolverReasoner():
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
    def explain(self,
        explanation_literals: List[Lit],
        literal: Lit,
        inference_cause: SolverCauses.ReasonerInference,
        solver: Solver,
    ) -> None:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @abstractmethod
    def on_solver_new_set_literal_decision(self,
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
    ) -> Optional[SolverConflictInfo.InvalidBoundUpdate | SolverConflictInfo.ReasonerExplanation]:
        """
        TODO
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

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
        #########################################################################
        self.vars: Dict[bool, Set[Var]] = { False: set(), True: set() }
        """
        Stores the variables of the problem.

        The controllable variables are in the set under key `True`,
        and the uncontrollable ones are in the set under key `False`.
        """
        #########################################################################
        self.conjunctive_scopes: Dict[Tuple[Lit,...], Lit] = {}
        """
        Stores conjunctions (of presence literals) corresponding to conjunctive scopes
        that have been defined in the problem, as well as their associated "scope
        literals" that represent them.

        A conjunctive scope is created when we want to refer to a subset of the
        problem that exists iff all required scopes are present. For example, the 
        expression "a <= b" is defined iff both a and b are present. It can be said
        to exist in the conjunctive scope "presence(a) & presence(b)".
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.conjunctive_scopes_reverse: Dict[Lit, Tuple[Lit,...]] = {}
        """
        The reverse of `conjunctive_scopes`.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.conjunctive_scopes_tautologies: Dict[Lit, Lit] = {}
        """
        For each scope literal, associates a literal (on an optional variable).
        When we're in that scope (i.e. the scope literal is true, i.e. all the
        literals defining it are true) that literal is always true. When we're
        not in that scope, the variable of this literal is absent. As such, this
        literal can indeed be called "tautology of the scope".
        """
        #########################################################################
        self.constraints: List[Tuple[ConstraintElementaryExpression.AnyExpr, Lit]] = []
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
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.reifications: Dict[ConstraintElementaryExpression.AnyExpr, Lit] = {}
        """
        Stores reification literals of constraints that were defined in the problem (in
        their "elementary" form) and reified.
        """
        #########################################################################
        self.bound_values: Dict[SignedVar, BoundVal] = {}
        """
        The main "domains" structure.
        Stores the upper and lower bounds of variables' domains (at the current decision level).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.bound_values_event_indices: Dict[SignedVar, Optional[Tuple[int, int]]] = {} 
        """
        Stores the indices of events in that set the current bounds of variables.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.vars_presence_literals: Dict[Var, Lit] = {}
        """
        Maps variables to their presence literals.

        Variables of presence literals have to be non-optional
        (i.e. have the `TRUE_LIT` as their presence literal).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.non_optional_vars_implication_graph: Dict[SignedVar, Dict[BoundVal, Set[Lit]]] = {}
        """
        Represents an implication graph on literals of non-optional variables.

        Maps a signed variable to a dictionary of adjancency lists (sets),
        which can be seen as a "labeled adjacency list".
        The key of the inner dict is a "guard" bound value for the signed variable,
        and the value (list of literals) corresponds to literals that
        are implied by the literal formed by the signed variable and
        the guard bound value.

        Note that if a literal is present in a adjacency list "guarded"
        by a value v, there is no need to have it also be in the adjacency
        list for values greater (weaker) than v.
        """
        #########################################################################
        self.dec_level: int = 0
        """
        The current decision level of the solver.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.events_trail: List[List[SolverEvent]] = [[]]
        """
        The trail of events.

        Uses double indices: the index in the first list is the decision level
        of the event. The index in the inner list is the index of the event in
        that decision level.
        """
        #########################################################################

        self.vars[False].add(ZERO_VAR)
        self.vars_presence_literals[ZERO_VAR] = TRUE_LIT

        self.bound_values[SignedVar(ZERO_VAR, True)] = BoundVal(0)
        self.bound_values[SignedVar(ZERO_VAR, False)] = BoundVal(0)

        self.conjunctive_scopes[tuple()] = TRUE_LIT
        self.conjunctive_scopes_reverse[TRUE_LIT] = tuple()
        self.conjunctive_scopes_tautologies[TRUE_LIT] = TRUE_LIT

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
            bool: Whether `literal` is currently entailed / known to be true at the
        current decision level (i.e. the current bound value on its signed variable
        is stronger than its own)
        """ 

        return self.bound_values[literal.signed_var].is_stronger_than(literal.bound_value)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_literal_current_value(self,
        literal: Lit,
    ) -> Optional[bool]:
        """
        Args:
            literal (Literal): A literal.

        Returns:
            Optional[bool]: True if the literal is currently entailed (i.e. literal is True),
        False if its negation is currently entailed (i.e. literal is False), and None otherwise
        (i.e. literal is unbound, i.e. its value/status is unknown yet).
        """ 

        if self.is_literal_entailed(literal):
            return True
        elif self.is_literal_entailed(literal.negation()):
            return False
        else:
            return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_vars_assignment_complete(self) -> bool:
        """
        Returns:
            bool: Whether all controllable variables' domains are either singletons
            (lower bound equal to upper bound) or empty (lower bound greater than upper bound).
        
        Indeed, the domain of an optional variable that is absent is allowed to be empty.
        """

        return all([
            self.bound_values[SignedVar(var, True)]
                .is_stronger_than(BoundVal(-self.bound_values[SignedVar(var, False)]))
            for var in self.vars[True]])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_implication_true(self,
        from_literal: Lit,
        to_literal: Lit,
    ) -> bool:
        """
        Returns:
            bool: Whether the implication from_literal => to_literal is true.
        """
        if (self.is_literal_entailed(from_literal.negation())
            or self.is_literal_entailed(to_literal)):
            return True
        return self._is_implication_true(from_literal, to_literal)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _is_implication_true(self,
        from_literal: Lit,
        to_literal: Lit,
    ) -> bool:
        """
        Returns:
            bool: Whether from_literal is known to imply to_literal.
            
        This function is only used for tests for the implication graph.
        
        The main/"actual" function to use to check if from_literal => to_literal is
        true is `is_implication_true()`.

        The difference between the two is that this function only checks whether the
        implication is "known", be it explicitly (specifically stored in the
        implication graph) or implicitly (stronger literal implying a weaker one),
        but the other function also checks if the implication is satisfied.
        """
        
        # Obvious cases where implication is true
        if (to_literal == TRUE_LIT
            or from_literal == FALSE_LIT
            or from_literal.entails(to_literal)
        ):
            return True

        # If there are no "incoming edges" to to_literal in the implication graph,
        # (i.e. "outgoing edges" from to_literal.negation()), there are no
        # implications to to_literal.
        # This check is possible because for each (x -> y) "edge" to add in
        # the implication graph, we also explicitly add a (!y -> !x) "edge".
        if (not to_literal.signed_var.opposite_signed_var()
            in self.non_optional_vars_implication_graph
        ):
            return False

        # Depth first search through the
        # implication graph, starting at from_literal. Look for
        # a literal that entails to_literal to
        # determine whether from_literal implies to_literal.
        stack: List[Lit] = [from_literal]
        visited: Dict[SignedVar, BoundVal] = {}
        while stack:
            lit = stack.pop()

            # If the current literal entails to_literal,
            # then we won: to_literal is reachable from from_literal,
            # therefore from_literal does imply to_literal.
            if lit.entails(to_literal):
                return True

            # If we have already visited a literal that entails the
            # current one, then there is no hope in pursuing the
            # search further this path (because the search is depth-first).
            if (lit.signed_var in visited
                and lit.bound_value.is_stronger_than(visited[lit.signed_var])
            ):
                continue

            visited[lit.signed_var] = lit.bound_value

            # If the literal isn't implying anything, it can't imply to_literal
            if not lit.signed_var in self.non_optional_vars_implication_graph:
                continue

            # Push the all "directly" implied literals of lit
            guarded_adj_set = self.non_optional_vars_implication_graph[lit.signed_var]
            for guard_bound in guarded_adj_set:
                if lit.bound_value.is_stronger_than(guard_bound):
                    stack.extend(guarded_adj_set[guard_bound])

        return False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_literals_directly_implied_by(self,
        literal: Lit,
    ) -> List[Lit]:
        """
        Args:
            literal (Literal): A literal

        Returns:
            List[Literal]: The list of literals that are "directly implied" 
        by the given literal.
        
        This is only for non-optional variables involved in the
        `non_optional_vars_implication_graph`, and corresponds to the 
        given literal' "neighbour" literals in that graph. This is done by
        taking the signed variable of the literal, and aggregating its adjacency
        lists that are guarded by values weaker than literal's bound value.
        """

        if not literal.signed_var in self.non_optional_vars_implication_graph:
            return []

        res: List[Lit] = []

        guarded_adj_set = self.non_optional_vars_implication_graph[literal.signed_var]
        for guard_bound in guarded_adj_set:
            if literal.bound_value.is_stronger_than(guard_bound):
                res.extend(guarded_adj_set[guard_bound])

        return res

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_index_of_first_event_implying_literal(self,
        literal: Lit,
    ) -> Optional[Tuple[int, int]]:
        """
        Args:
            literal (Literal): The literal whose first event index we want to get.

        Returns:
            Tuple[int, int]: The event index of the first event that makes `literal` true.
            None: This means the given literal is the first event on its signed variable.
        
        This is done by walking in reverse order through events on the
        signed variable of the literal. The first event that makes the
        given literal true is the one whose previous value was weaker than
        the literal's bound value (i.e. the literal wasn't entailed before this event).
        """

        assert self.is_literal_entailed(literal)

# NOTE?        prev_ev_index = self.bound_values_event_indices[literal.signed_var]
        prev_ev_index = self.bound_values_event_indices.get(literal.signed_var, None)
        if prev_ev_index is None:
            return None
        (dl, ev_i) = prev_ev_index

        while dl > 0:
            ev = self.events_trail[dl][ev_i]
            
            if not ev.previous_bound_value.is_stronger_than(literal.bound_value):
                break

            prev_ev_index = ev.previous_bound_value_event_index
            if prev_ev_index is None:
                return None
            (dl, ev_i) = prev_ev_index

        return (dl, ev_i)

    #############################################################################
    # SIGNED VARIABLE BOUND VALUE UPDATE
    #############################################################################

    def set_bound_value(self,
        signed_var: SignedVar,
        bound_value: BoundVal,
        cause: SolverCauses.AnyCause,
    ) -> bool | SolverConflictInfo.InvalidBoundUpdate:
        """
        Arguably the most important method of the solver.
        (along with the propagate method)

        Attempts to set a new bound value to a signed variable. This is
        equivalent to setting / entailing / enforcing the corresponding literal.

        When the bound update is useless (the variable is optional and absent,
        or the current bound is stronger than the given one), doesn't do
        anything and returns False.

        When the bound update leads to an empty domain for the variable,
        returns a InvalidBoundUpdate if the variable is non-optional,
        and if it isn't, sets the new bound and attempts to set the negation
        of the variable's presence literal (with recursive call
        to set_bound_value).

        Additionally, if the variable isn't optional, "lazily" propagates the
        consequences of this update to non optional variables in the 
        non_optional_vars_implication_graph, that may be concerned by it.
        As such, recursive calls to set_bound_value or returns of 
        an InvalidBoundUpdate are possible during this process.

        Returns True if the bound was successfully updated
        without leading to an InvalidBoundUpdate.
        """

        prez_lit = self.vars_presence_literals[signed_var.var]

        # If variable is proven absent (i.e. the negation of its
        # presence literal is entailed), we return False as there
        # is no update to the domain. Note: Non optional variables
        # are always present (i.e. their presence literal is TrueBoundLiteral)
        # so this indeed doesn't apply to them.
        if self.is_literal_entailed(prez_lit.negation()):
            return False

        # If the new candidate bound value is weaker than the current
        # bound value, (i.e. the current bound value is stronger the
        # new candidate bound value) there is no update to the domain
        # of the variable and we return False.
        if self.bound_values[signed_var].is_stronger_than(bound_value):
            return False

        # If the new candidate bound value leads to an empty domain.
        if (not BoundVal(-self.bound_values[signed_var.opposite_signed_var()])
            .is_stronger_than(bound_value)
        ):
            # If the variable is not optional (i.e. always present),
            # we directly return a conflict for this invalid 
            # domain update that we attempted to make, indicating
            # the corresponding literal as the cause of the conflict.
            if prez_lit == TRUE_LIT:
                return SolverConflictInfo.InvalidBoundUpdate(Lit(signed_var, bound_value), cause)

            # If the variable is optional and its domain is empty, it
            # can only be absent. As such, we attempt to enforce the
            # entailment of the negation of its presence literal.
            prez_lit_neg = prez_lit.negation()
            return self.set_bound_value(
                prez_lit_neg.signed_var,
                prez_lit_neg.bound_value,
                SolverCauses.PresenceOfEmptyDomain(Lit(signed_var, bound_value), cause))
            
        # If the new candidate bound value is stronger and the current
        # bound value and is valid (doesn't lead to an empty domain)
        # and event corresponding to this update is pushed to the trail,
        # the current domain of the variable is updated with the new bound.
        self.events_trail[self.dec_level].append(SolverEvent(
            signed_var,
            bound_value,
            self.bound_values[signed_var],
            self.bound_values_event_indices.get(signed_var, None),
            cause,
        ))
        self.bound_values[signed_var] = bound_value
        self.bound_values_event_indices[signed_var] = (self.dec_level, len(self.events_trail[self.dec_level])-1)

        # If the variable is optional, we can already return True.
        if prez_lit != TRUE_LIT:
            return True

        # Now, if the variable is not optional, we want to perform 
        # one more step to succesfully complete the variable's bound
        # update. We need to succesfully propagate the direct implications
        # of all events/updates caused by this bound update attempt.
        # Again, this is only done for non optional variables, as we do
        # not allow literals of optional variables to appear in the implication
        # graph. We do this by looping through the direct implications of
        # all events / updates pushed to the trail since this method is called.
        i = len(self.events_trail[self.dec_level])-2
        j = i+1
        while i < j:
            i += 1
            pending_literal = Lit(
                self.events_trail[self.dec_level][i].signed_var,
                self.events_trail[self.dec_level][i].new_bound_value)
            
            # Propagation is done exactly like in the first part of the function,
            # simply taking into account the fact that the implied literal's
            # variable can't be optional.
            for implied_literal in self.get_literals_directly_implied_by(pending_literal):

                # If the implied literal's signed variable bound is weaker
                # than its current one, nothing to do.
                if (self.bound_values[implied_literal.signed_var]
                    .is_stronger_than(implied_literal.bound_value)
                ):
                    continue

                # If the implied literal's variable's domain is lead to be
                # empty, propagation is unsuccessful and a conflict indicating
                # the implied literal as the cause for failure is returned. Because
                # we know the var of the implied literal to be non-optional, it
                # cannot be made absent to resolve the problem.
                if (BoundVal(-self.bound_values[implied_literal.signed_var.opposite_signed_var()])
                    .is_stronger_than(implied_literal.bound_value)
                ):
                    return SolverConflictInfo.InvalidBoundUpdate(implied_literal, cause)
                
                # If the implied literal's variable's bound is stronger than its 
                # current one and is valid (doesn't lead to an empty domain)
                # current, it is applied and a new event corresponding to this
                # update is pushed to the trail.
                self.events_trail[self.dec_level].append(SolverEvent(
                    implied_literal.signed_var,
                    implied_literal.bound_value,
                    self.bound_values[implied_literal.signed_var],
                    self.bound_values_event_indices[implied_literal.signed_var],
                    SolverCauses.ImplicationPropagation(implied_literal)))
                self.bound_values[implied_literal.signed_var] = implied_literal.bound_value
                self.bound_values_event_indices[signed_var] = (self.dec_level, j+1)
                j += 1

        return True

    # TODO: minimal domain size for uncontrollable variables ?
    # (it could be defined by a variable itself, since this minimal domain size depends on the presence of uncontrollable edges/links (stnu))

    #############################################################################
    # DECISION CHOICE
    #############################################################################

    # TODO
    def choose_next_decision(self) -> SolverDecisions.AnyDecision:

        raise NotImplementedError

    #############################################################################
    # DECISION APPLICATION / DECISION LEVEL INCREMENTATION
    #############################################################################

    def increment_decision_level_and_perform_set_literal_decision(self,
        set_literal_decision: SolverDecisions.SetLiteral,
        reasoners: Tuple[SolverReasoner,...],
    ) -> None:
        """
        Increments the current decision level and applies the given set literal decision.

        Args:
            set_literal_decision (Solver.SetLiteralDecision): The decision to apply.

        Side effects:
            Increments the current decision level.
            
            Invokes the reasoners' on_solver_new_decision "callbacks", which
        updates them internally to account for the decision level incrementation.
            
            Then, applies the given set literal decision by
        calling `set_bound_value`. It is in that call that the
        first event of this new decision level will actually be applied
        and pushed to the trail of events.
        """

        self.dec_level += 1
        if len(self.events_trail) == self.dec_level:
            self.events_trail.append([])
        
        for reasoner in reasoners:
            reasoner.on_solver_new_set_literal_decision(self)

        self.set_bound_value(
            set_literal_decision.literal.signed_var,
            set_literal_decision.literal.bound_value,
            SolverCauses.Decision())

    #############################################################################
    # BACKTRACKING
    #############################################################################

    def _undo_and_return_last_event_at_current_decision_level(self) -> SolverEvent:
        """
        Reverts the last (latest) event in the events trail
        (at the current decision level).

        Makes corresponding updates to the current bounds values and event
        indices of previous bound values.

        Returns:
            SolverEvent: The event that was reverted.
        
        Side effects:
            Pops the last element of the event trail (at the current decision level).

            Updates the bound value of the signed variable of the event.

            Updates the dictionary that stores the indices of events
        that set the current bound value of a signed variable.
        """

        assert len(self.events_trail[self.dec_level]) > 0

        ev = self.events_trail[self.dec_level].pop()
        self.bound_values[ev.signed_var] = ev.previous_bound_value
        self.bound_values_event_indices[ev.signed_var] = ev.previous_bound_value_event_index
        return ev

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def backtrack_to_decision_level(self,
        target_dec_level: int,
        reasoners: Tuple[SolverReasoner,...],
    ) -> None:
        """
        Backtracks to the target decision level.

        Args:
            target_decision_level (int): The target decision level to backtrack to.

        Side effects:
            Reverts all events at all decision levels after the target one.
            
            Invokes the reasoners' on_solver_backtrack_one_level "callbacks", at
        each reverted decision level. This updates the reasoners internally to
        account for the backtracking.

            Sets the current decision level to the target one.
        """

        assert target_dec_level >= 0

        while self.dec_level > target_dec_level:
            _n = len(self.events_trail[self.dec_level])
            for reasoner in reasoners:
                reasoner.on_solver_backtrack_one_level(self)
            for _ in range(_n):
                self._undo_and_return_last_event_at_current_decision_level()
            self.dec_level -= 1

    #############################################################################
    # PROPAGATION
    #############################################################################

    def propagate(self,
        reasoners:Tuple[SolverReasoner,...],
    ) -> Optional[Tuple[
        Union[SolverConflictInfo.InvalidBoundUpdate, SolverConflictInfo.ReasonerExplanation],
        SolverReasoner,
    ]]:
        """
        The propagation method of the solver.

        For all reasoners, propagates changes / new events. The propagation
        process stops either when nothing new can be inferred (success), or
        when a contradiction is detected by one of the reasoners (failure).
        """

        while True:
            num_events_at_propagation_start: int = len(self.events_trail[self.dec_level])

            for reasoner in reasoners:
                contradiction = reasoner.propagate(self)
                if contradiction is not None:
                    return (contradiction, reasoner)
        
            if num_events_at_propagation_start == len(self.events_trail[self.dec_level]):
                break

        return None

    #############################################################################
    # CONFLICT ANALYSIS, EXPLANATION GENERATION
    #############################################################################

    def _add_implying_literals_to_explanation_literals(self,
        explanation_literals: List[Lit],
        literal: Lit,
        cause: SolverCauses.AnyCause,
        explain_function: Callable[[List[Lit], Lit, SolverCauses.ReasonerInference, Solver], None],
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
            explanation_literals (List[Literal]): The list of literals making up the explanation.

            literal (Literal): The literal whose implying literals we want to add to the explanation.

            cause (Solver.Cause):. TODO

            explain_function (Callable[[List[Lit], Lit, SolverCauses.ReasonerInference, Solver], None]): TODO

        Side effects:
            Modifies `explanation_literals`.
        """

        # In this function, the literal shouldn't be true yet,
        # but it should be immediately implied.
        assert not self.is_literal_entailed(literal)

        if isinstance(cause, SolverCauses.ReasonerInference):
            # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => literal
            explain_function(explanation_literals, literal, cause, self)

        elif isinstance(cause, SolverCauses.ImplicationPropagation):
            explanation_literals.append(cause.literal)

        elif isinstance(cause, SolverCauses.PresenceOfEmptyDomain):
            # cause.literal & (not cause.literal) => "variable of cause.literal is absent"
            #                                        (i.e. presence literal of cause.literal's variable is absent)
            explanation_literals.append(cause.literal.negation())
            if isinstance(cause.cause, SolverCauses.ReasonerInference):
                # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => cause.literal
                explain_function(explanation_literals, cause.literal, cause.cause, self)

            elif isinstance(cause.cause, SolverCauses.ImplicationPropagation):
                explanation_literals.append(cause.cause.literal)

            else:
                assert False

        else:
            assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def explain_invalid_bound_update(self,
        invalid_bound_update: SolverConflictInfo.InvalidBoundUpdate,
        explain_function: Callable[[List[Lit], Lit, SolverCauses.ReasonerInference, Solver], None],
    ) -> SolverConflictInfo.AnalysisResult:
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
            invalid_bound_update (Solver.InvalidBoundUpdate): The invalid bound update conflict to explain.

            reasoner (Solver.Reasoner): .TODO
        
        Returns:
            ConflicAnalysisInfo: an object containing the results of the
        conflict analysis (the asserting clause and set of resolved literals).
        """

        # Remember that an update is invalid iff its negation holds AND
        # the affected variable is present.

        # The base of the explanation is ('not l' v 'l')
        explanation_literals: List[Lit] = [invalid_bound_update.literal.negation()]

        # However 'l' does not hold in the current state and it needs
        # to be replaced, with a set of literals 'l_1' v ... v 'l_n',
        # such that 'l_1' v ... v 'l_n' => 'l'. As such, the explanation
        # becomes 'not l' v 'l_1' v ... v 'l_n', and all its disjuncts
        # ('not l' and all 'l_i') hold in the current state.
        self._add_implying_literals_to_explanation_literals(
            explanation_literals,
            invalid_bound_update.literal,
            invalid_bound_update.cause,
            explain_function)

        # The explanation clause 'not l' v 'l_1' v ... v 'l_n' must now be 
        # transformed into 1st Unique Implication Point form.
        return self.refine_explanation(
            explanation_literals,
            explain_function)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def refine_explanation(self,
        explanation_literals: List[Lit],
        explain_function: Callable[[List[Lit], Lit, SolverCauses.ReasonerInference, Solver], None],
    ) -> SolverConflictInfo.AnalysisResult:
        """
        Refines an explanation into an asserting clause.
        
        Args:
            explanation_literals (List[Literal]): The list of literals making up the explanation.

            reasoner (Solver.Reasoner): .TODO

        Returns:
            ConflicAnalysisInfo: an object containing the results of the
        conflict analysis (the asserting clause and set of resolved literals).

        Side effects:
        
            Modifies `explanation_literals`

            !! A partial backtrack (within the current decision level) will occur
        in the process !! This is necessary to provide explainers (reasoners)
        with the exact state in which their decisions were made.

        NOTE: There is no need to "synchronize"/update the reasoners' earliest unprocessed
        event index because of this partial backtracking. Indeed, right after this explanation is
        made/refined as part of conflict analysis, we will backtrack to an earlier decision
        level anyway. And during with that backtracking, the earliest unprocessed event index of each
        reasoner will be reset to 0 (at that decision level). As such, the partial backtracking
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

        # Literals that are beyond the curren decision and
        # will be part of the final asserting clause.
        asserting_clause_literals: List[Lit] = []

        resolved_literals: Dict[SignedVar, BoundVal] = {}

        while True:

            for lit in explanation_literals:

                # If lit is entailed (standard case).
                if self.bound_values[lit.signed_var].is_stronger_than(lit.bound_value):

                    # Find the location of the event that made lit true.
                    first_impl_ev_index = self.get_index_of_first_event_implying_literal(lit)

                    # If lit is implied at decision level 0, then it is always true.
                    # So we can discard it.
                    if first_impl_ev_index is None:
                        continue
                    (ev_i_dl, ev_i) = first_impl_ev_index
                    if ev_i_dl == 0:
                        continue

                    # If lit is implied at the current decision level,
                    # then add it to the queue.
                    if ev_i_dl == self.dec_level:
                        heapq.heappush(prio_queue, ((-ev_i_dl, -ev_i), lit))

                    # If lit is implied at a decision level before the current one,
                    # then its negation will appear in the final clause (1UIP).
                    elif ev_i_dl < self.dec_level:
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
            # will be at decision levels earlier than the current ont.
            # This can happen if we are at the top decision level, or if we
            # had a lazy propagator that didn't immediately detect the 
            # inconsistency # NOTE: need to be better understand this.
            #
            # Corollary: if dl is 0, the derived clause must be empty.
            if not prio_queue:
                return SolverConflictInfo.AnalysisResult(
                    tighten_literals(asserting_clause_literals),
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
                return SolverConflictInfo.AnalysisResult(
                    tighten_literals(asserting_clause_literals),
                    resolved_literals)

            # Now, we need to until the latest falsifying event. This
            # will undo some of the changes, but we will remain in the
            # same decision level (see function description for the
            # reason behind this partial backtracking). Indeed, the event
            # cannot be a decision, because otherwise it would have been
            # detected as a UIP earlier.

            cause: Optional[SolverCauses.AnyCause] = None
            while ev_i < len(self.events_trail[self.dec_level]):
                ev = self._undo_and_return_last_event_at_current_decision_level()
                cause = ev.cause

            assert cause is not None

            resolved_literals[lit.signed_var] = min(
                resolved_literals.get(lit.signed_var, lit.bound_value),
                lit.bound_value)

            # Add a set of literals whose conjunction implies lit to explanation_literals
            self._add_implying_literals_to_explanation_literals(
                explanation_literals,
                lit,
                cause,
                explain_function)

    #############################################################################
    # CLAUSE LEARNING
    #############################################################################

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
            
            literal_negation = literal.negation()

            if not self.bound_values[literal_negation.signed_var].is_stronger_than(literal_negation.bound_value):
                first_impl_ev_index = self.get_index_of_first_event_implying_literal(literal_negation)
                if first_impl_ev_index is None:
                    continue
                (dl, _) = first_impl_ev_index
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

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#################################################################################