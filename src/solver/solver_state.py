"""
This module defines the main low-level class of the solver.

It contains low-level methods allowing to query the state of the solver,
as well as arguably the most important method of the whole solver:
`set_bound` (and its syntactic sugar `set_literal`). 
"""

from __future__ import annotations

#################################################################################

from typing import Dict, List, NamedTuple, Optional, Set, Tuple

from src.constraint_expressions import ElemConstrExpr
from src.fundamentals import (FALSE_LIT, TRUE_LIT, ZERO_VAR, Bound, Lit,
                              SignedVar, Var)
from src.solver.common import Causes, Event, InvalidBoundUpdate, SetGuardedByLits

#################################################################################

class SolverState():

    #############################################################################
    # SCOPE INFO | DOC: OK 23/10/23.
    #############################################################################

    class ScopeInfo(NamedTuple):
        """
        Encapsulates information about a scope. A scope (aka conjunctive scope)
        is created when we want to refer to a subset of the problem that exists
        iff all required scopes are present. For example, the expression `a <= b`
        is defined iff both `a` and `b` are present. It can be said to exist in
        the (conjunctive) scope defined by the literals `presence(a)` and `presence(b)`.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        scope: Tuple[Lit,...]
        """
        The presence literals whose conjunction defines the scope.
        
        Note:
            Since order doesn't matter, we could use a Python `frozenset` instead
            of a tuple. However, we prefer to keep our types as simple as we can.

            To deal with the problem of order, we simply sort the literals
            (lexicographically) before registering a new scope. Moreover, if
            a new scope with the same literals in another order was to be
            given, we could simply use the same representative literal and
            tautology literal for it.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        representative_literal: Lit
        """
        A literal representing the scope. It is a non optional literal, enforced
        to be true iff all the literals of defining the scope are true.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        tautology_literal: Lit
        """
        The tautology literal of the scope. It is a literal `[v >= 1]` where `v`
        is an optional variable that is either absent (when we're out of the
        scope, i.e. not all literals in `scope` are entailed) or always equal
        to 1 (when we're in the scope).
        
        Note:
            This special tautology literal is needed because `TRUE_LIT` literal cannot
            be used, as it is shared in all scopes and its variable is always present.
            The representative literal cannot be used either because its domain is not
            reduced to the single value 1.
        """

    #############################################################################
    # INIT | DOC: OK 23/10/23. | 1 TODO | 1 REVIEW
    #############################################################################

    def __init__(self):

        self._vars_id_counter: int = 0

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._vars: Dict[bool, Set[Var]] = { False: set(), True: set() }
        """
        TODO DEAL WITH CONTROLLABILITY ? TODO: controllable variables are in the set under key True,
        and the uncontrollable ones are in the set under key False.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._presence_lits: Dict[Var, Lit] = {}
        """
        Maps variables to their presence literals. Recall that presence literals must
        be defined on non optional variables (i.e whose presence literal is TRUE_LIT).
        """

        self._presence_lits_implication_graph: SetGuardedByLits[Lit] = SetGuardedByLits()
        """
        Represents an implication graph presence literals.
        
        Note:
            An implication `[svar1 <= a] => [svar2 <= b]` is encoded as:
            `{ svar1 : { a : [svar2 <= b] } }`. As such, if we want to check if
            `[svar1 <= c]` implies `[svar2 <= d]`, we iterate through guards
            weaker than (i.e. greater than or equal to) `c`, and search for any
            literal entailing `[svar2 <= d]` (i.e. on the same signed variable
            (`svar2`) and with weaker (i.e. greater or equal) bound than `d`).
        """

        self._bounds: Dict[SignedVar, Bound] = {}
        """
        Stores the bounds of signed variables at the current decision level.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._decision_level: int = 0
        """The current decision level of the solver."""

        self._events_trail: List[List[Event]] = [[]]
        """
        The trail (or history) of events.
        The outer index is the decision level of the event.
        The inner index is the position of the event in that decision level.
        """

        self._bounds_event_indices: Dict[SignedVar, Optional[Tuple[int, int]]] = {} 
        """
        Stores the indices of the latest events for each signed variable.
        A None value indicates that the no event on the signed variable was registered yet.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._scopes: Dict[Tuple[Lit,...], SolverState.ScopeInfo] = {}
        """
        Maps registered scopes (i.e. conjunctions of (presence) literals)
        to structures encapsulating information about them.
        """

        self._scopes_representative_lits: Dict[Lit, SolverState.ScopeInfo] = {}
        """
        Maps scopes' representative literals
        to structures encapsulating information about them.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._constraints: List[Tuple[ElemConstrExpr, Lit]] = []
        """
        Stores pairs consisting of a constraint (in elementary form) and a literal,
        stating that the literal must be true iff the constraint is true.

        REVIEW? Both "real" reified constraints that were defined in the problem
        and "artificial"/"intermediary" constraints can be found here.
        Apart from pairs consisting of a (reified) constraint and its reification
        literal, there can be pairs where the constraint is simply the satisfaction
        of a reification literal of another constraint. This allows to enforce
        a sort of "chain of constraints". REVIEW?
        """

        self._reifications: Dict[ElemConstrExpr, Lit] = {}
        """
        Stores reification literals of constraints that were defined in the problem (in
        their "elementary" form) and reified.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._vars[False].add(ZERO_VAR)
        self._presence_lits[ZERO_VAR] = TRUE_LIT

        self._bounds[SignedVar.plus(ZERO_VAR)] = Bound(0)
        self._bounds[SignedVar.minus(ZERO_VAR)] = Bound(0)

        self._scopes[()] = SolverState.ScopeInfo((), TRUE_LIT, TRUE_LIT)
        self._scopes_representative_lits[TRUE_LIT] = self._scopes[()]

    #############################################################################
    # BASIC QUERIES, PROPERTIES, GETTERS | DOC: OK (23/10/23)
    #############################################################################

    def bound_of(self,
        signed_var: SignedVar,
    ) -> Bound:
        """
        Returns the bound of `signed_var` (at the current decision level).
        """
        return self._bounds[signed_var]

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#    def lower_bound_value_of(self,
#        var: Var
#    ) -> BoundVal:
#        """
#        Args:
#            var: The variable whose lower bound to get.
#        
#        Returns:
#            The current lower bound of `var`.
#        """
#        return -self.bound_value_of(SignedVar.minus(var))
#
#    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#    def upper_bound_value_of(self,
#        var: Var
#    ) -> BoundVal:
#        """
#        Args:
#            var: The variable whose upper bound to get.
#        
#        Returns:
#            The current upper bound of `var`.
#        """
#        return self.bound_value_of(SignedVar.plus(var))
#
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def presence_literal_of(self,
        var: Var,
    ) -> Lit:
        """
        Returns the presence literal of `var`.
        """
        return self._presence_lits[var]

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def entails(self,
        literal: Lit,
    ) -> bool:
        """
        Returns whether `literal` is entailed by the solver (at the current decision level).
        """

        return self.bound_of(literal.signed_var).is_stronger_than(literal.bound)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def entails_implication(self,
        literal_from: Lit,
        literal_to: Lit,
    ) -> bool:
        """
        Returns whether the implication `literal_from` => `literal_to` is entailed
        by the solver (at the current decision level).
        """
        
        # Obvious cases where the implication is known to be true.
        if (literal_to == TRUE_LIT
            or literal_from == FALSE_LIT
            or literal_from.entails(literal_to)
            or self.entails(literal_from.neg)
            or self.entails(literal_to)
        ):
            return True 

        # When there are no "incoming edges" to `literal_to` in the implication
        # graph (i.e. "outgoing edges" from `literal_to.neg`), there can't
        # be any implications to `literal_to`. Thus we return False.
        # NOTE: This check is possible because for each (l1 -> l2) "edge" to add
        # in the implication graph, we also explicitly add a (l2.neg -> l1.neg) "edge".
        if not self._presence_lits_implication_graph.has_elements_guarded_by(literal_to.neg):
            return False

        # Depth first search through the implication graph, starting
        # at `literal_from`. Look for a literal that entails `literal_to`
        # to determine whether `literal_from` implies `literal_to`.

        stack: List[Lit] = [literal_from]
        visited: Dict[SignedVar, Bound] = {}

        while stack:
            lit = stack.pop()

            # If the current literal entails `literal_to`, then we won:
            # `literal_to` is reachable from `literal_from`.
            # Thus `literal_from` does imply `literal_to` and we return True.
            if lit.entails(literal_to):
                return True

            if lit.signed_var not in visited:
                visited[lit.signed_var] = lit.bound
            
            # If we have already visited a literal that entails the
            # current one, then there is no hope in pursuing the search
            # further in this path (because the search is depth-first).
            elif lit.bound.is_stronger_than(visited[lit.signed_var]):
                continue                                                    

            # If the current literal doesn't imply anything, then it can't
            # imply possibly `literal_to`: no hope in pursuing the search
            # further in this path (because the search is depth-first).
            if not self._presence_lits_implication_graph.has_elements_guarded_by(lit):
                continue
            
            # Push literals "directly implied" by the current literal to the search stack.
            stack.extend(self._presence_lits_implication_graph.elements_guarded_by(lit))

        return False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def decision_level(self) -> int:
        """The current decision level of the solver."""
        return self._decision_level

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def num_events_at_current_decision_level(self) -> int:
        """The number of events at the current decision level."""
        return len(self._events_trail[self.decision_level])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_first_event_entailing(self,
        literal: Lit,
    ) -> Optional[Event]:
        """
        Returns the earliest first event that makes `literal` true, if there is one.
        Otherwise (if there are no events on `literal`'s signed variable), returns None.

        Raises:
            ValueError: if `literal` isn't currently entailed.

        Note:
            The method works by walking through past events on the signed
            variable of `literal`. The first event that makes `literal`
            true is the one whose previous value was weaker than
            `literal`'s bound value (i.e. the literal wasn't
            entailed before this event).
        """

        if not self.entails(literal):
            raise ValueError(("Literal not entailed: A literal must be entailed ",
                              "to find its first entailing event"))

        ev: Event
        ev_index: Optional[Tuple[int, int]] = self._bounds_event_indices.get(literal.signed_var, None)

        if ev_index is None:
            return None

        while True:

            assert ev_index is not None

            dl, i = ev_index
            ev = self._events_trail[dl][i]

            if ev.old_bound.is_stronger_than(literal.bound):
                ev_index = ev.old_index 
            else:
                break
        
        return ev

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_assignment_complete(self) -> bool:
        """
        TODO
        """

        return all([self.bound_of(SignedVar.plus(var)).is_stronger_than(-self.bound_of(SignedVar.minus(var)))
                    for var in self._vars[True]])

    #############################################################################
    # BOUND UPDATE | DOC: OK (23/10/23)
    #############################################################################

    def set_literal(self,
        literal: Lit,
        cause: Causes.AnyCause,
    ) -> bool | InvalidBoundUpdate:
        """
        Syntactic sugar for `set_bound`.
        """
        
        return self.set_bound(literal.signed_var, literal.bound, cause)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def set_bound(self,
        signed_var: SignedVar,
        bound: Bound,
        cause: Causes.AnyCause,
    ) -> bool | InvalidBoundUpdate:
        """
        Attempts to set a new bound on a signed variable,
        which is equivalent to enforcing the corresponding literal.
        Arguably the most important method of the solver.

        Args:
            signed_var: The signed variable whose bound to set.
            bound: The bound to set to `signed_var`.
            cause: The cause for this bound update.
        
        Returns:
            False if the update is useless, \
                True if the update is successful, \
                and `InvalidBoundUpdate` if the update is failed \
                (i.e. a conflict is encountered).

        Note:
            The update is:
            - Useless when either the variable is optional and absent 
            or the current bound is stronger than the suggested one.
            - Failed when it leads to an empty domain for a non optional variable.
            - Successful when it doesn't lead to an empty domain for a non optional variable.

            When we detect that applying the update would lead to the domain
            of `signed_var`'s variable to be empty (i.e. lower bound strictly
            greater than upper bound), there are 2 possibilities:
            - If the variable is non-optional, immediately return a `InvalidBoundUpdate`.
            - If the variable is optional, sets the new bound and attempts to set
            the negation of the variable's presence literal with a new call to
            `set_bound`. The results of this recursive call are then returned.
            
            When the bound of the signed variable is updated, we also perform
            "implication propagation" on presence literals, which can lead to a
            conflict (empty domain for the variable of a presence literal) as well.
        """

        prez_lit: Lit = self.presence_literal_of(signed_var.var)

        # If the variable is absent, then the update is useless.
        if self.entails(prez_lit.neg):
            return False

        # Similarly, the update is useless when the new
        # candidate bound is weaker than the current bound.
        if self.bound_of(signed_var).is_stronger_than(bound):     
            return False

        # If the new candidate bound value leads to an empty domain, then:
        # - if it is non optional, the conflict is unavoidable
        # - if it is optional, the bound update is ignored but the variable
        #   is enforced to be absent (i.e. its presence literal is enforced 
        #   to be false). However, this in turn can cause another variable's
        #   domain to become empty.
        if not (-self.bound_of(signed_var.opposite)).is_stronger_than(bound):

            if prez_lit == TRUE_LIT:
                return InvalidBoundUpdate(Lit(signed_var, bound), cause)
            else:
                return self.set_bound(prez_lit.neg.signed_var,
                                      prez_lit.neg.bound,
                                      Causes.EmptyDomain(Lit(signed_var, bound), cause))

        # If the new candidate bound value does not lead to an 
        # empty domain, then it is applied and "implication propagation"
        # is performed if the variable is non optional.
        else:

            ev = Event(signed_var,
                       bound=bound,
                       old_bound=self.bound_of(signed_var),
                       index=(self.decision_level, self.num_events_at_current_decision_level),
                       old_index=self._bounds_event_indices.get(signed_var, None),
                       cause=cause)
            
            self._events_trail[self.decision_level].append(ev)

            self._bounds[signed_var] = bound
            self._bounds_event_indices[signed_var] = ev.index

            if prez_lit != TRUE_LIT:
                return True
            
            # Perform "implication propagation" of the bound update to
            # presence variables (using the implication graph), as the
            # variable is non optional. This propagation is done by looping
            # through the direct implications of all events / bound updates
            # pushed to the trail since the method was called.

            i = self.num_events_at_current_decision_level-1
            j = i

            while i <= j:

                pending_lit = Lit(self._events_trail[self.decision_level][i].signed_var,
                                  self._events_trail[self.decision_level][i].bound)

                for implied_lit in self._presence_lits_implication_graph.elements_guarded_by(pending_lit):

                    # If the implied literal's bound is weaker than its
                    # current one, then the update is useless for it.
                    if self.bound_of(implied_lit.signed_var).is_stronger_than(implied_lit.bound):
                        continue

                    # If the implied literal's variable's domain is lead to be empty, propagation
                    # is unsuccessful and a conflict indicating the implied literal as the cause
                    # for failure is returned. Because we know the variable of the implied literal
                    # to be non optional, it cannot be made absent to resolve the problem.
                    if not (-self.bound_of(implied_lit.signed_var.opposite)).is_stronger_than(implied_lit.bound):
                        return InvalidBoundUpdate(implied_lit, cause)

                    # The update to the implied literal's variable's bound is not useless and is valid.
                    # It is pushed to the trail of events, and information on the old bound is recorded.

                    assert j+1 == self.num_events_at_current_decision_level

                    ev = Event(implied_lit.signed_var,
                               bound=implied_lit.bound,
                               old_bound=self.bound_of(implied_lit.signed_var),
                               index=(self.decision_level, j+1),
                               old_index=self._bounds_event_indices.get(implied_lit.signed_var, None),
                               cause=Causes.ImplicationPropagation(pending_lit))

                    self._events_trail[self.decision_level].append(ev)

                    self._bounds[implied_lit.signed_var] = implied_lit.bound
                    self._bounds_event_indices[implied_lit.signed_var] = ev.index

                    j += 1

                i += 1
                
        return True

    # TODO: minimal domain size for uncontrollable variables ?
    # (it could be defined by a variable itself, since this minimal domain size depends on the presence of uncontrollable edges/links (stnu))

    #############################################################################
    # VARIABLE ADDITION, IMPLICATION REGISTRATION | DOC: OK 23/10/23
    #############################################################################

    def add_new_variable(self,
        initial_domain: Tuple[int, int],
        controllable: bool,
        presence_literal: Lit,
    ) -> Var:
        """
        Registers and returns a new variable with the
        given `initial_domain` and `presence_literal`.

        Raises:
            ValueError: If `presence_literal` is defined on a optional variable.
        """

        if self.presence_literal_of(presence_literal.signed_var.var) != TRUE_LIT:
            raise ValueError(("The presence literal of an optional variable must ", 
                              "not be based on an optional variable."))

        self._vars_id_counter += 1

        var = Var(self._vars_id_counter)

        self._vars[controllable].add(var)
        self._presence_lits[var] = presence_literal
        
        self._bounds[SignedVar.minus(var)] = Bound(-initial_domain[0])
        self._bounds[SignedVar.plus(var)] = Bound(initial_domain[1])

        return var

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def register_presence_literals_implication(self,
        literal_from: Lit,
        literal_to: Lit,
    ) -> None:
        """
        Registers an implication between two presence literals.

        Raises:
            ValueError: If one of the literals' variables is optional.

        Note:
            The literals aren't really required to be "presence literals".
            The actual requirement is for their variables to be non optional.
            However our usage is basically only for presence literals.
        """

        if (self.presence_literal_of(literal_from.signed_var.var) != TRUE_LIT
            or self.presence_literal_of(literal_to.signed_var.var) != TRUE_LIT
        ):
            raise ValueError(("Only literals on non optional variables ",
                              "are supported for the internal implication graph."))

        # If the implication is implicit/obvious, no need to add it.
        if (literal_to == TRUE_LIT
            or literal_from == FALSE_LIT
            or literal_from.entails(literal_to)
        ):
            pass

        # Otherwise, add the implication to the implication graph
        # (both `literal_from` => `literal_to` and (!`literal_to`) => (!`literal_from`))
        else:
            self._presence_lits_implication_graph.add(element=literal_to,
                                                      literal=literal_from)

            self._presence_lits_implication_graph.add(element=literal_from.neg,
                                                      literal=literal_to.neg)

        # If `literal_from` is true, `literal_to` needs to be enforced as true.
        # Indeed (`literal_from` => `literal_to`) <=> (!`literal_from` | `literal_to`)
        if self.entails(literal_from):

            bound_update_result = self.set_literal(literal_to,
                                                   Causes.ImplicationPropagation(literal_from))

            if isinstance(bound_update_result, InvalidBoundUpdate):
                raise ValueError(("Inconsistency on the addition of the ",
                                  "implication {0} => {1}".format(literal_from, literal_to)))

        # If `literal_to` is false, `literal_from` needs to be enforced as false.
        # Indeed (!`literal_to` => !`literal_from`) <=> (`literal_to` | !`literal_from`)
        if self.entails(literal_to.neg):

            bound_update_result = self.set_literal(literal_from.neg,
                                                   Causes.ImplicationPropagation(literal_to))

            if isinstance(bound_update_result, InvalidBoundUpdate):
                raise ValueError(("Inconsistency on the addition of the ",
                                  "implication {0} => {1}".format(literal_from, literal_to)))

    #############################################################################
    # SCOPES | DOC: OK 23/10/23
    #############################################################################

    def register_and_sort_scope(self,
        scope: Tuple[Lit,...],
        scope_representative_literal: Lit,
    ) -> None:
        """
        Sorts the literals in `scope` and registers them as defining a new scope,
        and represented by `scope_representative_literal`.
        """

        scope_sorted = tuple(sorted(scope))

        scope_tautology_literal = Lit.geq(self.add_new_variable((1, 1), False, scope_representative_literal), 1)

        self._scopes[scope_sorted] = SolverState.ScopeInfo(scope_sorted,
                                                           scope_representative_literal,
                                                           scope_tautology_literal)

        if scope_representative_literal not in self._scopes_representative_lits:
            self._scopes_representative_lits[scope_representative_literal] = self._scopes[scope_sorted]

        # NOTE: The absence of the "not in" condition was causing a bug !
        #
        # REVIEW: The collection `_scope_representatives` pairs up two associated
        # different kinds of "representatives" (as in the notion of
        # equivalence class) of a scope: its "scope literal" and its
        # *defining* conjunction of literals.
        # Together with the `_scopes` collection, this allows to
        # "bind" different conjunctions falling in the same scope.
        #
        # Ideally, we'd like each scope literal to point to
        # the smallest conjunction defining the scope.

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#    def get_or_make_scope_tautology_literal(self,
    def get_scope_tautology_literal(self,
        scope: Tuple[Lit,...],
    ) -> Lit:
        """
        Returns the tautology literal for the scope defined by `scope`.

        If `scope` isn't registered yet, we register it first
        and then return its tautology literal.
        """
        
#        scope_sorted = sorted(scope)
#
#        if scope_sorted in self._scopes_info:
#            return self._scopes_info[scope_sorted].tautology_literal

        if scope in self._scopes:
            return self._scopes[scope].tautology_literal
        else:
            scope_representative_literal = self.get_scope_representative_literal(scope)
            return self._scopes_representative_lits[scope_representative_literal].tautology_literal

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#    def get_or_make_scope_representative_literal(self,
    def get_scope_representative_literal(self,
        scope: Tuple[Lit,...],
    ) -> Lit:
        """
        Returns the representative literal for the scope defined by `scope`.

        If `scope` isn't registered yet, we register it first
        and then return its representative literal.
        
        Note:
            In some cases, when the scope is composed of 1 or 2 literals,
            the representative literal of the scope can be computed and enforced
            to be true at the same time as all its literals quite easily.
            Otherwise it is "manually" enforced to be true at the same
            time as all its literals.
        """

#        scope_sorted = sorted(scope)
#
#        if scope_sorted in self._scopes_info:
#            return self._scopes_info[scope_sorted].representative_literal

        if scope in self._scopes:
            return self._scopes[scope].representative_literal

        # If the scope is not already known we need to register it with
        # a new representative literal. There are 2 possibilities:
        # - If we find a literal that simplifies the conjunction,
        #   use it as representative literal of the scope.
        # - Otherwise, create the scope representative literal from
        #   scratch, as a new literal l such that:
        #   l => l_1, l => l_2, ..., l => l_n, and l | !l_1 | !l_2 | ... | !l_n
        #   (which is equivalent to l <=> l_1 & l_2 & ... & l_n)

        scope_representative_literal: Optional[Lit] = None

        if len(scope) == 1:
            scope_representative_literal = scope[0]

        elif len(scope) == 2:

            # If l_1 => l_2, the conjunction can be simplified to l_1
            if (self.entails_implication(scope[0],
                                         scope[1])
            ):
                scope_representative_literal = scope[0]

            # If l_2 => l_1, the conjunction can be simplified to l_2
            elif (self.entails_implication(scope[1],
                                           scope[0])
            ):
                scope_representative_literal = scope[1]

            # If l_1 and l_2 are exclusive (i.e. cannot be true at the same
            # time, i.e. l_1 => not l_2), then the scope literal is false.
            # However, we cannot directly use FALSE_LIT, because we
            # need to uniquely identify the literal as the conjunction
            # of the other two in some corner cases.
            # So we create a new literal that is always false.
            elif (self.entails_implication(scope[0],
                                         scope[1].neg)
            ):
                scope_representative_literal = Lit.geq(self.add_new_variable((0, 1), False, TRUE_LIT), 1)

        # A simplification was found. Use it as the scope's representative literal.
        if scope_representative_literal is not None:

            self.register_and_sort_scope(scope, scope_representative_literal)
            return scope_representative_literal

        # No simplification was found. Build the scope's representative literal from scratch.
        else:

            scope_representative_literal = Lit.geq(self.add_new_variable((0, 1), False, TRUE_LIT), 1)

            lits: List[Lit] = [scope_representative_literal]

            for l in scope:
                self.register_presence_literals_implication(scope_representative_literal, l)
                lits.append(l.neg)

            self._add_elem_constraint(ElemConstrExpr.from_lits_simplify_or(lits),
                                      self._scopes_representative_lits[TRUE_LIT].tautology_literal)           
            # we know that self._scopes_info_reverse[TRUE_LIT].tautology_literal = TRUE_LIT,
            # but we choose to keep it explicit for clarity

            self.register_and_sort_scope(scope, scope_representative_literal)
            return scope_representative_literal

    #############################################################################
    # ELEMENTARY CONSTRAINT REGISTRATION HELPERS | DOC: TODO 23/10/23
    #############################################################################

    def _add_elem_constraint(self,
        elem_constr_expr: ElemConstrExpr,
        constr_value_lit: Lit,
    ) -> None:
        """
        "Binds" `elem_constr_expr` with `constr_value_lit` (i.e. reigsters the fact
        that `elem_constr_expr` must hold iff `constr_value_lit` is entailed).

        Note:
            To find a suitable reification literal
            for `elem_constr_expr`, 3 possible cases are considered:

            - `elem_constr_expr` is already reified (which is possible if a constraint
              decomposed into the same "elementary form" was added earlier, or if it
              results from "intermediary" reification in `Solver._preprocess_constr_expr_into_elem_form`).
              In this case, we "unify" the already known reification literal with
              `constr_value_lit` by adding an "artificial" constraint binding them together.

            - `elem_constr_expr` wasn't already reified and its own "natural" scope
              is compatible (i.e. is valid simultaneously) with the presence literal 
              of `constr_value_lit`'s variable. In this case, we reify `elem_constr_expr`
              with `constr_value_lit`.

            - `elem_constr_expr` wasn't already reified, but its own "natural" scope
              is not compatible (i.e. not valid simultaneously) with the presence literal
              of `constr_value_lit`'s variable. In this case, we reify `elem_constr_expr` with
              a new reification literal, but also "unify" it with `constr_value_lit` by
              adding an "artificial" constraint binding them together.
        """

        expr_scope_representative_lit = \
            self.get_scope_representative_literal(self._get_elem_constr_expr_scope(elem_constr_expr))

        if elem_constr_expr in self._reifications:
        
            reif_lit = self._reifications[elem_constr_expr]

            if constr_value_lit != reif_lit:
                self._constraints.append((ElemConstrExpr.from_lit(reif_lit), constr_value_lit))
        
        else:

            if expr_scope_representative_lit == self.presence_literal_of(constr_value_lit.signed_var.var):

                self._reifications[elem_constr_expr] = constr_value_lit
                self._reifications[elem_constr_expr.negated] = constr_value_lit.neg
                self._constraints.append((elem_constr_expr, constr_value_lit))
            
            else:
                
                reif_lit = Lit.geq(self.add_new_variable((0,1), True, expr_scope_representative_lit), 1)

                self._reifications[elem_constr_expr] = reif_lit
                self._reifications[elem_constr_expr.negated] = reif_lit.neg
                self._constraints.append((elem_constr_expr, reif_lit))

                self._constraints.append((ElemConstrExpr.from_lit(reif_lit), constr_value_lit))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _get_elem_constr_expr_scope(self,
        elem_constr_expr: ElemConstrExpr,
    ) -> Tuple[Lit,...]:
        """
        Returns literals whose conjunction defines the scope
        of the given elementary constraint expression.

        Args:
            elem_constr_expr: The elementary constraint expression whose scope we want.
        
        Returns:
            A conjunction of literals which defines the scope of `elem_constr_expr`.
        """

        raw_required_presences, raw_guards = self._get_raw_required_presences_and_guards(elem_constr_expr)

        return self._process_raw_required_presences_and_guards(raw_required_presences, raw_guards, False)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _get_raw_required_presences_and_guards(self,
        elem_constr_expr: ElemConstrExpr,
    ) -> Tuple[Tuple[Lit,...], Tuple[Lit,...]]:
        """
        Get a special representation of the scope of the given elementary
        expression, depending on its kind, in the following tuple form:
        
        - 1st element ("required presences"): set of presence literals that
        appear in the expression.

        - 2nd element ("guards"): set of literals such that if one of them is
        true, the expression is valid/well-defined.

        Note that the required presences are "raw": tautological and multiple
        literals on the same signed variable are allowed. They will be
        processed by the `_process_raw_required_presences_and_guards` function.
        """

        match elem_constr_expr.kind, elem_constr_expr.terms:

            case ElemConstrExpr.Kind.LIT, Lit() as lit:

                prez_lit = self.presence_literal_of(lit.signed_var.var)

                return (prez_lit,), ()

            case ElemConstrExpr.Kind.OR, [Lit(), *_] as lits:

                return (tuple(self.presence_literal_of(lit.signed_var.var) for lit in lits),
                        tuple(lit for lit in lits 
                              if self.presence_literal_of(lit.signed_var.var) == TRUE_LIT
                                 and lit != FALSE_LIT))

            case ElemConstrExpr.Kind.AND, [Lit(), *_] as lits:

                return (tuple(self.presence_literal_of(lit.signed_var.var) for lit in lits),
                        tuple(lit.neg for lit in lits 
                              if self.presence_literal_of(lit.signed_var.var) == TRUE_LIT
                                 and lit.neg != FALSE_LIT))
                    
            case (ElemConstrExpr.Kind.MAX_DIFFERENCE,
                (Var() as var_from, Var() as var_to, int())
            ):
                prez_lit_var_from = self.presence_literal_of(var_from)
                prez_lit_var_to = self.presence_literal_of(var_to)

                return (prez_lit_var_from, prez_lit_var_to), ()

            case _:
                assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _process_raw_required_presences_and_guards(self,
        raw_required_presences: Tuple[Lit,...],
        guards: Tuple[Lit,...],
        only_remove_lits_entailed_at_top_decision_level: bool,
    ) -> Tuple[Lit,...]:
        """
        "Flattens" / processes "raw" required presences and guards obtained from 
        `_get_raw_required_presences_and_guards`.

        This is done by:

        1. Keeping only the strongest literals of the "raw" required presences.
    
        2. Replacing literals defined as a conjunction of other literals by
        that conjunction (using `_scope_representative_lit_conjs`)
        
        3. Keeping non-tautological literals (i.e. non entailed ones).

        4. Keeping non-guarded literals (i.e. removing the literals that
        are contradicting a literal from "guards")
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def is_tautology(lit: Lit):

            if self.entails(lit):

                if not only_remove_lits_entailed_at_top_decision_level:
                    return True
                else:
                    first_entailing_ev = self.get_first_event_entailing(lit)
                    return first_entailing_ev is None or first_entailing_ev[0] == 0
            
            return False

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        required_presences = { }

        for lit in raw_required_presences:
            
            if (lit.signed_var not in required_presences
                or lit.bound.is_stronger_than(required_presences[lit.signed_var])
            ):
                required_presences[lit.signed_var] = lit.bound

        for signed_var, bound_value in required_presences.copy().items():

            lit = Lit(signed_var, bound_value)
            scope_info = self._scopes_representative_lits.get(lit, None)

            if scope_info is not None:

                for l in scope_info.scope:

                    if is_tautology(l):
                        continue

                    if (l.signed_var not in required_presences
                        or l.bound.is_stronger_than(required_presences[l.signed_var])
                    ):
                        required_presences[l.signed_var] = l.bound

            else:

                if is_tautology(lit):
                    continue

                if (lit.signed_var not in required_presences
                    or lit.bound.is_stronger_than(required_presences[lit.signed_var])
                ):
                    required_presences[lit.signed_var] = lit.bound

        for lit in guards:

            if (lit.signed_var in required_presences
                and lit.neg.bound.is_stronger_than(required_presences[lit.neg.signed_var])
            ):
                weaker = Lit(lit.signed_var, lit.bound + Bound(1))
                if is_tautology(weaker):
                    required_presences.pop(lit.signed_var)
                else:
                    required_presences[lit.signed_var] = weaker.bound
        
        return tuple(sorted(Lit(signed_var, bound_value) 
                            for signed_var, bound_value in required_presences.items()))
