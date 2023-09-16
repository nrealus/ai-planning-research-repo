"""
TODO
"""

from __future__ import annotations

#################################################################################

from typing import Dict, List, Optional, Set, Tuple

from src.constraint_expressions import ElemConstrExpr
from src.fundamentals import (FALSE_LIT, TRUE_LIT, ZERO_VAR, BoundVal, Lit,
                              SignedVar, Var)
from src.solver.common import Causes, Event, InvalidBoundUpdateInfo, SetGuardedByLiterals

#################################################################################
# SOLVER STATE
#################################################################################

class SolverState():

    def __init__(self):

        self._vars_id_counter: int = 0
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._vars: Dict[bool, Set[Var]] = { False: set(), True: set() }
        """
        Stores all the variables known to the solver.

        The controllable variables are in the set under key True,
        and the uncontrollable ones are in the set under key False.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._presence_literals: Dict[Var, Lit] = {}
        """
        Maps variables to their presence literals.

        Variables of presence literals have to be non-optional
        (i.e. have the TRUE_LIT as their presence literal).
        """

        self._non_optionals_implication_graph: SetGuardedByLiterals[Lit] = SetGuardedByLiterals()
        """
        Represents an implication graph on literals of non-optional variables
        (most notably presence literals).
        
        An implication [svar1 <= a] => [svar2 <= b] is encoded as:
        { svar1 : { a : [svar2 <= b] } }. As such, if we want to check if
        [svar1 <= c] implies [svar2 <= d], we iterate through guard values
        weaker (>=) than c, and search for any literal entailing [svar2 <= d]
        (i.e. on the same signed variable (svar2) and with weaker (>=) bound than d).
        """

        self._bound_values: Dict[SignedVar, BoundVal] = {}
        """
        The main "domains" structure.
        Stores the upper and lower bounds of variables' domains (at the current decision level).
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._dec_lvl: int = 0
        """The current decision level of the solver."""

        self._events_trail: List[List[Event]] = [[]]
        """
        The trail of events.

        Uses double indices: the index in outer list is the decision level of the event.
        The index in the inner list is the index of the event in that decision level.
        """

        self._bound_values_event_indices: Dict[SignedVar, Optional[Tuple[int, int]]] = {} 
        """
        Stores the indices in `events_trail` of events that set the (current) bounds of variables.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._scope_lits_of_lit_conjs: Dict[Tuple[Lit,...], Lit] = {}
        """
        Stores conjunctions of (presence) literals corresponding to (conjunctive)
        scopes that have been defined in the problem, as well as the associated
        "scope literals" representing them.

        A conjunctive scope is created when we want to refer to a subset of the
        problem that exists iff all required scopes are present. For example, the 
        expression "a <= b" is defined iff both a and b are present. It can be said
        to exist in the conjunctive scope "presence(a) & presence(b)".
        """

        self._scope_representative_lit_conjs: Dict[Lit, Tuple[Lit,...]] = {}
        """
        The reverse of `scopes`.
        """

        self._scope_tautologies: Dict[Lit, Lit] = {}
        """
        For each scope literal, associates a literal (on an optional variable).
        When we're in that scope (i.e. the scope literal is true, i.e. all the
        literals defining it are true) that literal is always true. When we're
        not in that scope, the variable of this literal is absent. As such, this
        literal can indeed be called "tautology of the scope".
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
#
#        self.reasoners: List[Reasoner] = []
#        """
#        The set of reasoners plugged into the solver. There cannot be 2 or more
#        reasoners of the same type.
#        """
#
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._vars[False].add(ZERO_VAR)
        self._presence_literals[ZERO_VAR] = TRUE_LIT

        self._bound_values[SignedVar.plus(ZERO_VAR)] = BoundVal(0)
        self._bound_values[SignedVar.minus(ZERO_VAR)] = BoundVal(0)

        self._scope_lits_of_lit_conjs[()] = TRUE_LIT
        self._scope_representative_lit_conjs[TRUE_LIT] = ()
        self._scope_tautologies[TRUE_LIT] = TRUE_LIT

    #############################################################################
    # PROPERTIES & QUERIES / GETTERS
    #############################################################################

    def bound_value_of(self,
        signed_var: SignedVar,
    ) -> BoundVal:
        """
        Args:
            signed_var: The signed variable whose bound to get.
        
        Returns:
            The current bound of `signed_var`.
        """
        return self._bound_values[signed_var]

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
        Args:
            var: The variable whose presence literal to get.
        
        Returns:
            The presence literal of `var`.
        """
        return self._presence_literals[var]

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_entailed(self,
        literal: Lit,
    ) -> bool:
        """
        Args:
            literal: The literal whose entailment to check.

        Returns:
            Whether `literal` is entailed at the current decision   \
                level (i.e. its bound value is weaker than its      \
                signed variable's current bound).
        """ 

        return self.bound_value_of(literal.signed_var).is_stronger_than(literal.bound_value)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_implication_true(self,
        literal_from: Lit,
        literal_to: Lit,
    ) -> bool:
        """
        Args:
            literal_from: The "source" of the implication to check.
            literal_to: The "target" of the implication to check.

        Returns:
            Whether the implication `literal_from` => `literal_to` is true.
        """
        
        # Obvious cases where the implication is known to be true.
        if (literal_to == TRUE_LIT
            or literal_from == FALSE_LIT
            or literal_from.entails(literal_to)
            or self.is_entailed(literal_from.negated)
            or self.is_entailed(literal_to)
        ):
            return True 

        # When there are no "incoming edges" to `literal_to` in the implication
        # graph (i.e. "outgoing edges" from `literal_to.negated`), there can't
        # be any implications to `literal_to`. Thus we return False.
        # NOTE: This check is possible because for each (x -> y) "edge" to add
        # in the implication graph, we also explicitly add a (!y -> !x) "edge".
        if not self._non_optionals_implication_graph.has_elements_guarded_by(literal_to.negated):
            return False

        # Depth first search through the implication graph, starting
        # at `literal_from`. Look for a literal that entails `literal_to`
        # to determine whether `literal_from` implies `literal_to`.

        stack: List[Lit] = [literal_from]
        visited: Dict[SignedVar, BoundVal] = {}

        while stack:
            lit = stack.pop()

            # If the current literal entails `literal_to`, then we won:
            # `literal_to` is reachable from `literal_from`.
            # Thus `literal_from` does imply `literal_to` and we return True.
            if lit.entails(literal_to):
                return True

            if lit.signed_var not in visited:
                visited[lit.signed_var] = lit.bound_value
            
            # If we have already visited a literal that entails the
            # current one, then there is no hope in pursuing the search
            # further in this path (because the search is depth-first).
            elif lit.bound_value.is_stronger_than(visited[lit.signed_var]):
                continue                                                    

            # If the current literal doesn't imply anything, then it can't
            # imply possibly `literal_to`: no hope in pursuing the search
            # further in this path (because the search is depth-first).
            if not self._non_optionals_implication_graph.has_elements_guarded_by(lit):
                continue
            
            # Push literals "directly implied" by the current literal to the search stack.
            stack.extend(self._non_optionals_implication_graph.elements_guarded_by(lit))

        return False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def decision_level(self) -> int:
        """The current decision level of the solver."""
        return self._dec_lvl

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def num_events_at_current_decision_level(self) -> int:
        """The number of events at the current decision level."""
        return len(self._events_trail[self.decision_level])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def first_event_entailing(self,
        literal: Lit,
    ) -> Optional[Event]:
        """
        Args:
            literal: The literal whose first entailing event to find.

        Returns:
            The earliest first event that makes `literal` true.
            None if there are no events on `literal`'s signed variable.

        Raises:
            ValueError: if `literal` isn't currently entailed.

        Note:
            The method works by walking in reverse order through events on
            the signed variable of `literal`. The first event that makes
            `literal` true is the one whose previous value was weaker
            than `literal`'s bound value (i.e. the literal wasn't
            entailed before this event).
        """

        if not self.is_entailed(literal):
            raise ValueError(("Literal not entailed: A literal must be entailed ",
                             "to find its first entailing event"))

        ev_index = self._bound_values_event_indices.get(literal.signed_var, None)

        if ev_index is None:
            return None

        ev: Event

        while True:
            dl, i = ev_index
            ev = self._events_trail[dl][i]

            if not ev.previous_bound_value.is_stronger_than(literal.bound_value):
                break

            ev_index = ev.previous_index
            if ev_index is None:
                break
        
        return ev

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_assignment_complete(self) -> bool:
        """
        """

        return all([self.bound_value_of(SignedVar.plus(var))
                    .is_stronger_than(-self.bound_value_of(SignedVar.minus(var)))
                    for var in self._vars[True]])

    #############################################################################
    # BOUND VALUE UPDATE
    #############################################################################

    def set_literal(self,
        literal: Lit,
        cause: Causes.AnyCause,
    ) -> bool | InvalidBoundUpdateInfo:
        
        return self.set_bound_value(literal.signed_var, literal.bound_value, cause)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def set_bound_value(self,
        signed_var: SignedVar,
        bound_value: BoundVal,
        cause: Causes.AnyCause,
    ) -> bool | InvalidBoundUpdateInfo:
        """
        One of the most (arguably the most) important method of the solver.

        Attempts to set a new bound on a signed variable, which is equivalent
        to setting / entailing / enforcing the corresponding literal.

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
        domain empty, performs "implication propagation" of this update to literals
        on non-optional variables (in the `_non_optionals_implication_graph`) by
        recursively calling `set_bound_value`. If any of those calls leads to a
        failure / invalid bound update, the corresponding `InvalidBoundUpdateInfo`
        will be returned.

        Finally, when the bound was was successfully updated without leading to an
        empty domain for any variable, True is returned.

        Args:
            signed_var: The signed variable whose bound to set.
            bound_value: The bound value to set on `signed_var`.
            cause: The cause for this bound update.
        
        Returns:
            False if the update was useless, True if the update was performed
            successfully, `InvalidBoundUpdateInfo` if a conflict was encountered.
        """

        prez_lit = self.presence_literal_of(signed_var.var)

        # If the variable is absent (i.e. its presence literal is false),
        # the update is useless. Thus we return False.
        if self.is_entailed(prez_lit.negated):
            return False

        # Similarly, the update is useless when new candidate bound value
        # is weaker than the current bound value. Thus we return False
        if self.bound_value_of(signed_var).is_stronger_than(bound_value):     
            return False

        # If the new candidate bound value leads to an empty domain:
        if not (-self.bound_value_of(signed_var.opposite)).is_stronger_than(bound_value):

            # When the variable is not optional (i.e. always
            # present), this the conflict is unavoidable.
            if prez_lit == TRUE_LIT:
                return InvalidBoundUpdateInfo(Lit(signed_var, bound_value), cause)

            # When the variable is optional, we have to make it absent to avoid
            # the conflict. Thus we attempt to set its presence literal to false. 
            else:
                return self.set_literal(prez_lit.negated,
                                        Causes.EmptyDomain(Lit(signed_var, bound_value), cause))

        else:

            # The update is not useless and is valid. It is pushed to the trail
            # of events, and information on the previous bound is recorded.

            ev = Event(signed_var,
                       bound_value,
                       previous_bound_value=self.bound_value_of(signed_var),
                       index=(self.decision_level, self.num_events_at_current_decision_level),
                       previous_index=self._bound_values_event_indices.get(signed_var, None),
                       cause=cause)
            
            self._events_trail[self.decision_level].append(ev)

            self._bound_values[signed_var] = bound_value
            self._bound_values_event_indices[signed_var] = ev.index

            if prez_lit != TRUE_LIT:
                return True
            
            # If the variable is not optional, we can perform "implication
            # propagation" of this new bound update to other (non optional)
            # variables. Indeed, only non-optional variables are allowed
            # in the implication graph.
            #
            # This propagation is done by looping through the direct
            # implications of all events / updates pushed to the
            # trail since this method was called.
            #
            # The bound update will succeed only if implication propagation
            # is successful. A conflict will be returned otherwise.

            i = self.num_events_at_current_decision_level-1
            j = i+1

            while i < j:

                pending_lit = Lit(self._events_trail[self.decision_level][i].signed_var,
                                  self._events_trail[self.decision_level][i].new_bound_value)

                for implied_lit in self._non_optionals_implication_graph.elements_guarded_by(pending_lit):

                    # If the implied literal's bound is weaker than its
                    # current one, then the update is useless for it.
                    if self.bound_value_of(implied_lit.signed_var).is_stronger_than(implied_lit.bound_value):
                        continue

                    # If the implied literal's variable's domain is lead to be empty, propagation
                    # is unsuccessful and a conflict indicating the implied literal as the cause
                    # for failure is returned. Because we know the var of the implied literal to
                    # be non-optional, it cannot be made absent to resolve the problem.
                    if (not (-self.bound_value_of(implied_lit.signed_var.opposite))
                        .is_stronger_than(implied_lit.bound_value)
                    ):
                        return InvalidBoundUpdateInfo(implied_lit, cause)

                    # The update to the implied literal's variable's bound is not useless and is valid.
                    # It is pushed to the trail of events, and information on the previous bound is recorded.

                    assert j == self.num_events_at_current_decision_level

                    ev = Event(implied_lit.signed_var,
                               implied_lit.bound_value,
                               previous_bound_value=self.bound_value_of(implied_lit.signed_var),
                               index=(self.decision_level, self.num_events_at_current_decision_level),
                               previous_index=self._bound_values_event_indices.get(implied_lit.signed_var, None),
                               cause=Causes.ImplicationPropagation(pending_lit))

                    self._events_trail[self.decision_level].append(ev)

                    self._bound_values[implied_lit.signed_var] = implied_lit.bound_value
                    self._bound_values_event_indices[signed_var] = ev.index
                    j += 1

                i += 1

        return True

    # TODO: minimal domain size for uncontrollable variables ?
    # (it could be defined by a variable itself, since this minimal domain size depends on the presence of uncontrollable edges/links (stnu))

    #############################################################################
    # GENERAL HELPER METHODS
    #############################################################################

    def _register_implication_between_literals_on_non_optional_vars(self,
        lit_from: Lit,
        lit_to: Lit,
    ) -> None:
        """
        Adds an implication between two literals (defined on
        non-optional variables) to the solver.
        """

        if (self.presence_literal_of(lit_from.signed_var.var) != TRUE_LIT
            or self.presence_literal_of(lit_to.signed_var.var) != TRUE_LIT
        ):
            raise ValueError(("Only implications between non-optional ",
                            "variables are supported"))

        # If the implication is implicit/obvious, no need to add it.
        if (lit_to == TRUE_LIT
            or lit_from == FALSE_LIT
            or lit_from.entails(lit_to)
        ):
            pass

        # Otherwise, add the implication to the implication graph
        # (both from => to and (not to) => (not from))
        else:
            self._non_optionals_implication_graph.add(element=lit_to,
                                                      guard_literal=lit_from)

            self._non_optionals_implication_graph.add(element=lit_from.negated,
                                                      guard_literal=lit_to.negated)

        # If from_literal is true, to_literal needs to be enforced as true.
        # (Indeed (from => to) <=> ((not from) or to))
        if self.is_entailed(lit_from):

            bound_update_result = self.set_literal(lit_to,
                                                   Causes.ImplicationPropagation(lit_from))

            if isinstance(bound_update_result, InvalidBoundUpdateInfo):
                raise ValueError(("Inconsistency on the addition of the ",
                                "implication {0} => {1}".format(lit_from, lit_to)))

        # If to_literal is false, from_literal needs to be enforced as false.
        # (Indeed ((not to) => (not from)) <=> (to or (not from)))
        if self.is_entailed(lit_to.negated):

            bound_update_result = self.set_bound_value(lit_from.negated.signed_var,
                                                       lit_from.negated.bound_value,
                                                       Causes.ImplicationPropagation(lit_to))

            if isinstance(bound_update_result, InvalidBoundUpdateInfo):
                raise ValueError(("Inconsistency on the addition of the ",
                                "implication {0} => {1}".format(lit_from, lit_to)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _register_new_scope_after_sorting(self,
        scope_as_conjunction: Tuple[Lit,...],
        scope_lit: Lit,
    ) -> None:
        """
        First, sorts the given literals, then adds to the solver a conjunctive 
        scope consisting of them, and corresponding to the given scope literal
        (i.e. it is true iff all the literals are).
        """

        scope_as_conjunction_sorted = tuple(sorted(scope_as_conjunction))

        if scope_as_conjunction_sorted in self._scope_lits_of_lit_conjs:
            raise ValueError("Could not insert a new scope because it already exists.")

        self._scope_lits_of_lit_conjs[scope_as_conjunction_sorted] = scope_lit
        
        # NOTE: Actually important ! absence of "not in" condition was a reason for a bug !!
        #
        # REVIEW: The collection `_scope_representatives` pairs up two associated
        # different kinds of "representatives" (as in the notion of
        # equivalence class) of a scope: its "scope literal" and its
        # *defining* conjunction of literals.
        # Together with the `_scopes` collection, this allows to
        # "bind" different conjunctions falling in the same scope.
        if scope_lit not in self._scope_representative_lit_conjs:
            self._scope_representative_lit_conjs[scope_lit] = scope_as_conjunction_sorted

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_new_variable(self,
        initial_domain: Tuple[int, int],
        controllable: bool,
        presence_literal: Lit,
    ) -> Var:
        """
        Helper function for higher level functions that add a new variable.
        """

        if self.presence_literal_of(presence_literal.signed_var.var) != TRUE_LIT:
            raise ValueError(("The presence literal of an optional variable must", 
                            "not be based on an optional variable."))

        self._vars_id_counter += 1

        var = Var(self._vars_id_counter)

        self._vars[controllable].add(var)
        self._presence_literals[var] = presence_literal
        
        self._bound_values[SignedVar.minus(var)] = BoundVal(-initial_domain[0])
        self._bound_values[SignedVar.plus(var)] = BoundVal(initial_domain[1])

        return var

    #############################################################################
    # CONSTRAINT ADDITION HELPER METHODS
    #############################################################################

    def _add_elem_constraint(self,
        elem_constr_expr: ElemConstrExpr,
        scope_tautology_lit: Lit,
    ) -> Tuple[ElemConstrExpr, Lit]:
        """
        See `solver.py` `add_constraint` for more
        general documentation on constraint addition.
        
        We have to "bind" `elem_constr_expr` with `scope_tautology_lit` (i.e.
        reigster the fact that `elem_constr_expr` must be true/satisfied iff
        the current scope is inside the scope defined by `scope_as_conjunction`).
        
        This is done by finding a suitable reification literal
        for `elem_constr_expr`. There are 3 possible cases:
        
        - `elem_constr_expr` is already reified (which is possible if a constraint
          decomposed into the same "elementary form" was added earlier, or if it
          results from "intermediary" reification in `_preprocess_constr_expr_into_elem_form`).
          In this case, we "unify" the already known reification literal with
          `scope_tautology_lit` by adding an "artificial" constraint binding them together.
        
        - `elem_constr_expr` wasn't already reified and its own "natural" scope
          is compatible (i.e. is valid simultaneously) with the scope defined by 
          `scope_as_conjunction`. In this case, we reify `elem_constr_expr`
          with `scope_tautology_lit`.
        
        - `elem_constr_expr` wasn't already reified, but its own "natural" scope
          is not compatible (i.e. not valid simultaneously) with the scope defined
          by `scope_as_conjunction`. In this case, we reify `elem_constr_expr` with
          a new reification literal, but also "unify" it with `scope_tautology_lit` by
          adding an "artificial" constraint binding them together.
        """

        expr_scope_lit = \
            self._get_or_make_new_scope_lit_from_conjunction(
                self._get_scope_as_conjunction(elem_constr_expr))

        if elem_constr_expr in self._reifications:
        
            reif_lit = self._reifications[elem_constr_expr]

            if scope_tautology_lit != reif_lit:
                self._constraints.append((ElemConstrExpr.from_lit(reif_lit), scope_tautology_lit))
        
        else:

            if expr_scope_lit == self.presence_literal_of(scope_tautology_lit.signed_var.var):

                self._reifications[elem_constr_expr] = scope_tautology_lit
                self._reifications[elem_constr_expr.negated] = scope_tautology_lit.negated
                self._constraints.append((elem_constr_expr, scope_tautology_lit))
            
            else:
                
                reif_lit = Lit.geq(self._add_new_variable((0,1), True, expr_scope_lit), 1)

                self._reifications[elem_constr_expr] = reif_lit
                self._reifications[elem_constr_expr.negated] = reif_lit.negated
                self._constraints.append((elem_constr_expr, reif_lit))

                if scope_tautology_lit != reif_lit:
                    self._constraints.append((ElemConstrExpr.from_lit(reif_lit), scope_tautology_lit))
                
        return (elem_constr_expr, scope_tautology_lit)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _get_or_make_new_scope_lit_from_conjunction(self,
        scope_as_conjunction: Tuple[Lit,...],
    ) -> Lit:
        """
        Return a literal representing the scope defined by the given conjunction of
        literals. If there isn't already a scope literal like that, add it to the solver.
        
        In other words, if we denote the literals of the conjunction as `l_i`, then
        the scope literal is defined to satisfy `scope_lit <=> l_1 & l_2 & ... & l_n`.

        Args:
            scope_as_conjunction: A conjunction of literals defining a scope.
        
        Returns:
            A literal (sometimes called scope literal) representing the scope   \
                defined by `scope_as_conjunction`. 
        """

        if scope_as_conjunction in self._scope_lits_of_lit_conjs:
            return self._scope_lits_of_lit_conjs[scope_as_conjunction]

        # If scope is not already known we need to register 
        # with a new literal. There are 2 possibilities:
        #
        # - If we find a literal that simplifies the
        #   conjunction, it will be our scope literal.
        #
        # - Otherwise, we create the scope literal from scratch, as a new literal `l`:
        #   `l => l_1, l => l_2, ..., l => l_n`, and `l | not l_1 | not l_2 | ... | not l_n`
        #   (which is equivalent to `l <=> l_1 & l_2 & ... & l_n`)

        simplification: Optional[Lit] = None

        if len(scope_as_conjunction) == 1:
            simplification = scope_as_conjunction[0]

        elif len(scope_as_conjunction) == 2:

            # If l_1 => l_2, the conjunction can be simplified to l_1
            if (self.is_implication_true(scope_as_conjunction[0],
                                         scope_as_conjunction[1])
            ):
                simplification = scope_as_conjunction[0]

            # If l_2 => l_1, the conjunction can be simplified to l_2
            elif (self.is_implication_true(scope_as_conjunction[1],
                                           scope_as_conjunction[0])
            ):
                simplification = scope_as_conjunction[1]

            # If l_1 and l_2 are exclusive (i.e. cannot be true at the same
            # time, i.e. l_1 => not l_2), then the scope literal is false.
            # However, we cannot directly use FALSE_LIT, because we
            # need to uniquely identify the literal as the conjunction
            # of the other two in some corner cases.
            # So we create a new literal that is always false.
            elif (self.is_implication_true(scope_as_conjunction[0],
                                         scope_as_conjunction[1].negated)
            ):
                simplification = Lit.geq(self._add_new_variable((0, 1), False, TRUE_LIT), 1)

        if simplification is not None:

            self._register_new_scope_after_sorting(scope_as_conjunction, simplification)
            return simplification

        else:

            scope_lit = Lit.geq(self._add_new_variable((0, 1), False, TRUE_LIT), 1)

            lits: List[Lit] = [scope_lit]

            for l in scope_as_conjunction:
                self._register_implication_between_literals_on_non_optional_vars(scope_lit, l)
                lits.append(l.negated)

            self._add_elem_constraint(ElemConstrExpr.from_lits_simplify_or(lits),
                                      self._scope_tautologies[TRUE_LIT])           
                                      # we know that self._scopes_tautologies[TRUE_LIT] = TRUE_LIT,
                                      # but we also keep it explicit for clarity

            self._register_new_scope_after_sorting(scope_as_conjunction, scope_lit)
            return scope_lit

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _get_scope_as_conjunction(self,
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
                        tuple(lit.negated for lit in lits 
                              if self.presence_literal_of(lit.signed_var.var) == TRUE_LIT
                                 and lit.negated != FALSE_LIT))
                    
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

            if self.is_entailed(lit):

                if not only_remove_lits_entailed_at_top_decision_level:
                    return True
                else:
                    first_entailing_ev = self.first_event_entailing(lit)
                    return first_entailing_ev is None or first_entailing_ev[0] == 0
            
            return False

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        required_presences = { }

        for lit in raw_required_presences:
            
            if (lit.signed_var not in required_presences
                or lit.bound_value.is_stronger_than(required_presences[lit.signed_var])
            ):
                required_presences[lit.signed_var] = lit.bound_value

        for signed_var, bound_value in required_presences.copy().items():

            lit = Lit(signed_var, bound_value)
            lits = self._scope_representative_lit_conjs.get(lit, None)

            if lits is not None:

                for l in lits:

                    if is_tautology(l):
                        continue

                    if (l.signed_var not in required_presences
                        or l.bound_value.is_stronger_than(required_presences[l.signed_var])
                    ):
                        required_presences[l.signed_var] = l.bound_value

            else:

                if is_tautology(lit):
                    continue

                if (lit.signed_var not in required_presences
                    or lit.bound_value.is_stronger_than(required_presences[lit.signed_var])
                ):
                    required_presences[lit.signed_var] = lit.bound_value

        for lit in guards:

            if (lit.signed_var in required_presences
                and lit.negated.bound_value.is_stronger_than(required_presences[lit.negated.signed_var])
            ):
                weaker = Lit(lit.signed_var, lit.bound_value + BoundVal(1))
                if is_tautology(weaker):
                    required_presences.pop(lit.signed_var)
                else:
                    required_presences[lit.signed_var] = weaker.bound_value
        
        return tuple(sorted(Lit(signed_var, bound_value) 
                            for signed_var, bound_value in required_presences.items()))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _get_or_make_tautology_of_scope(self,
        scope_lit: Lit,
    ) -> Lit:
        """
        Returns a literal whose presence status must be equal
        to the truth value of the given literal.

        This is functionally equivalent to creating a new optional variable with
        a domain consisting of the single value 1, and ensuring that only one
        such variable is created in the scope represented by `scope_lit`.
        
        Indeed, TRUE_LIT cannot be used for this in general, because its
        variable, (the special ZERO_VAR variable) is always present (i.e. is
        present in all scopes, not just the one represented by `scope_lit`).

        Args:
            scope_lit: A scope literal representing a scope.
        
        Returns:
            The so-called tautology literal for the scope represented by `scope_lit`.
        """

        if scope_lit in self._scope_tautologies:
            return self._scope_tautologies[scope_lit]

        else:
            lit = Lit.geq(self._add_new_variable((1, 1), False, scope_lit), 1)
            self._scope_tautologies[scope_lit] = lit
            return lit

#################################################################################
