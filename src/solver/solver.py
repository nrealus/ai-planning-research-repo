"""
This module defines the main high-level class of the solver.

It contains (relatively) high-level methods to use when encoding a problem,
or when writing a search / solving function.
"""

from __future__ import annotations

#################################################################################
# FILE CONTENTS:
# - MAIN SOLVER CLASS | HIGH LEVEL API AND MACHINERY
#################################################################################

import heapq
from typing import Callable, Dict, List, Optional, Tuple

from src.constraint_expressions import ConstrExpr, ElemConstrExpr
from src.fundamentals import (TRUE_LIT, Bound, Lit, SignedVar, Var,
                              simplify_lits_disjunction, is_lits_disjunction_tautological,
                              BoolAtom, IntAtom, FracAtom, SymbAtom)
from src.solver.common import (Causes, ConflictAnalysisResult,
                               Event, InvalidBoundUpdate,
                               ReasonerBaseExplanation)
from src.solver.reasoners.reasoner import Reasoner
from src.solver.reasoners.sat_reasoner import SATReasoner
from src.solver.reasoners.diff_reasoner import DiffReasoner
from src.solver.solver_state import SolverState

#################################################################################

class Solver():
    """
    TODO
    """

    #############################################################################

    def __init__(self,
        use_sat_reasoner: bool,
        use_diff_reasoner: bool,
    ):

        self.state: SolverState = SolverState()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._sat_reasoner: Optional[SATReasoner] = SATReasoner(self.state) if use_sat_reasoner else None
        self._diff_reasoner: Optional[DiffReasoner] = DiffReasoner(self.state) if use_diff_reasoner else None

        self._reasoners = tuple(r for r in (self._sat_reasoner, self._diff_reasoner) if r is not None)

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.next_reified_constraint_to_process_index: int = 0

    #############################################################################

    @property
    def reasoners(self) -> Tuple[Reasoner,...]:
        return self._reasoners

    @property
    def sat_reasoner(self) -> Optional[SATReasoner]:
        return self._sat_reasoner

    @property
    def diff_reasoner(self) -> Optional[DiffReasoner]:
        return self._diff_reasoner

    #############################################################################
    # DECISION LEVEL INCREMENTATION | DOC: OK 23/10/23
    #############################################################################

    def increment_decision_level_by_one(self) -> None:
        """
        Increments the current decision level by 1
        (i.e. moves the solver to the next decision level).
        
        Note:
            Invokes all reasoners' `on_solver_increment_decision_level` callbacks, which
            updates them internally to account for the decision level incrementation.
        """

        # assert self.curr_dec_lvl == 0 or len(self._events_trail[self.curr_dec_lvl]) > 0

        self.state._decision_level += 1

        if len(self.state._events_trail) == self.state.decision_level:
            self.state._events_trail.append([])
        
        for reasoner in self.reasoners:
            reasoner.on_solver_increment_decision_level_by_one()

    #############################################################################
    # BACKTRACKING | DOC: OK 23/10/23
    #############################################################################

    def _undo_and_return_latest_event_at_current_decision_level(self) -> Event:
        """
        Reverts the last event (at the current decision level) by popping it
        from the events trail, and by updating the current and previous bounds
        (as well as the index of its corresponding event)

        Returns:
            The event that was reverted.
        """

        ev = self.state._events_trail[self.state.decision_level].pop()

        self.state._bounds[ev.signed_var] = ev.old_bound
        self.state._bounds_event_indices[ev.signed_var] = ev.old_index

        return ev

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def backtrack_to_decision_level(self,
        target_decision_level: int,
    ) -> None:
        """
        Backtracks to the `target_decision_level` by reverting all events at all
        decision levels strictly greater than the target one.

        Raises:
            ValueError: If the target decision level was strictly less than 0.

        Note:
            Invokes the reasoners' `on_solver_backtrack_one_level` callbacks, at
            each reverted decision level. This updates the reasoners internally
            to account for the backtracking.
        """

        if target_decision_level < 0:
            raise ValueError("Target decision level must be >= 0.")

        while self.state.decision_level > target_decision_level:

            for _ in range(self.state.num_events_at_current_decision_level):
                self._undo_and_return_latest_event_at_current_decision_level()

            self.state._decision_level -= 1

            for reasoner in self.reasoners:
                reasoner.on_solver_backtrack_one_decision_level()

    #############################################################################
    # PROPAGATION | DOC: OK 23/10/23
    #############################################################################
    
    def propagate(self,
    ) -> Optional[Tuple[InvalidBoundUpdate | ReasonerBaseExplanation, Reasoner]]:
        """
        Propagates the changes accumulated since the last call to this method,
        until nothing new can be infferred.

        Returns:
            None if the propagation was successful, and a tuple if a conflict \
                is encountered. The tuple contains information on the \
                conflict as well as the reasoner that encountered it.

        Note:
            Proceeds by first posting the reified constraints whose scope is
            not false. Then, propagates new events to reasoners, until either
            a conflict is encountered or there are no more new events.
        """

        while self.next_reified_constraint_to_process_index < len(self.state._constraints):

            elem_constr_expr, constr_lit = \
                self.state._constraints[self.next_reified_constraint_to_process_index]
            
            constr_scope_representative_lit = self.state.presence_literal_of(constr_lit.signed_var.var)
            
            # If the scope of the constraint is false, it means
            # the constraint is absent. So it is ignored.
            if self.state.entails(constr_scope_representative_lit.neg):
                conflict_info = None
            else:
                conflict_info = self._post_constraint_to_reasoners((elem_constr_expr, constr_lit))

            if conflict_info is not None:
                if self.sat_reasoner is None:
                    raise ValueError("SAT Reasoner must be defined.")
                return (conflict_info, self.sat_reasoner)
            
            self.next_reified_constraint_to_process_index += 1

        while True:

            num_events = self.state.num_events_at_current_decision_level

            for reasoner in self.reasoners:
                conflict_info = reasoner.propagate()

                if conflict_info is not None:
                    return (conflict_info, reasoner)
        
            if num_events == self.state.num_events_at_current_decision_level:
                break

        return None

    #############################################################################
    # CONFLICT ANALYSIS, EXPLANATION GENERATION | DOC: OK 23/10/23 
    #############################################################################

    def _add_implying_literals_to_explanation(self,
        explanation: List[Lit],
        literal: Lit,
        cause: Causes.AnyCause,
        explain_function: Callable[[List[Lit], Lit, Causes.ReasonerInference], None],
    ) -> None:
        """       
        Assuming `literal` is not entailed in the current state and `cause` provides
        the explanation for asserting `literal` (and is not a decision), computes a
        set of literals `l_1, ..., l_n` and places them in `explanation`.
        
        These literals `l_1, ..., l_n` will be such that:
        - `l_1 & ... & l_n => literal` (i.e. `!l_1 | ... | !l_n | literal`)
        - each `l_i` is entailed at the current decision level.

        Args:
            explanation: The list of literals making up the explanation \
                currently being built. Modified by the method.

            literal: The literal whose implying literals we want to add to the explanation.

            cause: The cause for the event that lead to the contradiction that we're explaining.

            explain_function: An external function that may participate in building \
                the explanation (basically the `explain` function of a relevant `Reasoner`).
        """

        # In this function, the literal shouldn't be
        # true yet, but it should be immediately implied.
        assert not self.state.entails(literal)

        match cause:

            case Causes.ReasonerInference():
                # Ask the reasoner for an explanation
                # clause (l_1 & ... & l_n => literal).
                explain_function(explanation, literal, cause)

            case Causes.ImplicationPropagation():
                explanation.append(cause.literal)

            case Causes.EmptyDomain():
                explanation.append(cause.literal.neg)

                match cause.cause:

                    case Causes.ReasonerInference():
                        # Ask the reasoner for an explanation
                        # clause (l_1 & ... & l_n => cause.literal).
                        explain_function(explanation, cause.literal, cause.cause)

                    case Causes.ImplicationPropagation():
                        explanation.append(cause.cause.literal)
                    
                    case _:
                        assert False

            case _:
                assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def explain_invalid_bound_update(self,
        invalid_bound_update: InvalidBoundUpdate,
        explain_function: Callable[[List[Lit], Lit, Causes.ReasonerInference], None],
    ) -> ConflictAnalysisResult:
        """
        Performs explanation / conflict analysis of an `invalid_bound_update`.

        Args:
            invalid_bound_update: The invalid bound update (conflict) to explain.

            explain_function: An external function that may participate in building \
                the explanation (basically the `explain` function of a relevant `Reasoner`).

        Returns:
            The results of conflict analysis.

        Note: 
            Given an invalid bound update of a literal `l`, returns an asserting
            clause `l_1 & ... & l_n => (!l_dec)` (i.e. `!l_1 | ... | !l_n | !l_dec`) where:
            - the literals 'l_i' are entailed at the previous decision level (of the current state)
            - the literal 'l_dec' is the decisions that was taken at the current decision level

            The update of 'l' must not directly originate from a decision, as it is
            necessarily the case that 'not l' holds in the current state. It is
            thus considered a logic error to enforce an obviously wrong decision.
        """
        
        literal, cause = invalid_bound_update.literal, invalid_bound_update.cause

        # Remember that an update is invalid iff its negation
        # holds AND the affected variable is present.
        assert self.state.entails(literal.neg)
        assert self.state.entails(self.state.presence_literal_of(literal.signed_var.var))

        # The base of the explanation is !l | l
        explanation: List[Lit] = [invalid_bound_update.literal.neg]

        # However l does not hold in the current state and it needs
        # to be replaced, with a set of literals l_1 | ... | l_n,
        # such that l_1 | ... | l_n => l. As such, the explanation
        # becomes !l | l_1 | ... | l_n, and all its disjuncts
        # (!l and all l_i) hold in the current state.
        self._add_implying_literals_to_explanation(explanation,
                                                   literal,
                                                   cause,
                                                   explain_function)

        # The explanation clause !l | l_1 | ... | l_n must now be 
        # transformed into 1st Unique Implication Point form.
        return self.refine_explanation(explanation,
                                       explain_function)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def refine_explanation(self,
        explanation: List[Lit],
        explain_function: Callable[[List[Lit], Lit, Causes.ReasonerInference], None],
    ) -> ConflictAnalysisResult:
        """
        Refines an explanation into an asserting clause.

        Args:
            explanation: The list of literals making up the explanation.   \
                Modified by the method.

            explain_function: An external function that may participate in building \
                the explanation (basically the `explain` function of a relevant `Reasoner`).

        Returns:
            The results of conflict analysis.

        Note:
            A partial backtrack (within the current decision level) will occur
            in this function. This is necessary to provide explainers (reasoners)
            with the exact state in which their decisions were made.

            Do not worry though, there is no need to "synchronize" the reasoners' 
            "cursors" of what new events to process next. Indeed, right after the
            explanation is made as part of conflict analysis, CDCL search will
            backtrack to an earlier decision level anyway. 
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
        asserting_clause: List[Lit] = []

        resolved_literals: Dict[SignedVar, Bound] = {}

        while True:

            for lit in explanation:

                if self.state.entails(lit):

                    first_entailing_ev = self.state.get_first_event_entailing(lit)

                    # If lit is implied at decision level 0, then it
                    # is always true. So we can discard it.
                    if first_entailing_ev is None or first_entailing_ev.index[0] == 0:
                        continue
                    ev_i_dl, ev_i = first_entailing_ev.index

                    # If lit is implied at the current decision
                    # level, then add it to the queue.
                    #
                    # But if lit is implied at a decision level
                    # before the current one, then its negation
                    # will appear in the final clause (1UIP).

                    if ev_i_dl == self.state.decision_level:
                        heapq.heappush(prio_queue, ((-ev_i_dl, -ev_i), lit))

                    elif ev_i_dl < self.state.decision_level:
                        asserting_clause.append(lit.neg)

                    else:
                        assert False
                
                # If lit is is not entailed, it must have been added in
                # an eager propagation. Even if it was not necessary for
                # this propagation to occur, it must be part of the clause
                # for correctness.
                else:
                    asserting_clause.append(lit.neg)
                
            # If the queue is empty, it means that all literals in the clause
            # will be at decision levels earlier than the current decision level.
            # This can happen if we are at the top decision level, or if we
            # had a lazy propagator that didn't immediately detect the 
            # inconsistency NOTE: need to be better understand this.
            #
            # Corollary: if ev_i_dl is 0, the derived clause must be empty.
            if not prio_queue:
                return ConflictAnalysisResult(tuple(asserting_clause),
                                              resolved_literals)
            
            # At this point, we haven't reached the 1st UIP yet.

            # Select the latest falsified literal from the queue.
            _prio_queue_head = heapq.heappop(prio_queue)
            ((ev_i_dl, ev_i), lit) = ((-_prio_queue_head[0][0], -_prio_queue_head[0][1]),
                                      _prio_queue_head[1])

            # However, the queue might contain more than onen reference
            # to the same event. Because of the priority of the queue
            # (event indices), they are necessarily contiguous.
            while prio_queue:
                _prio_queue_head = prio_queue[0]    # peek
                ((next_dl, next_ev_i), next_lit) = ((-_prio_queue_head[0][0], -_prio_queue_head[0][1]),
                                                    _prio_queue_head[1])

                # If the event is the same, pop it from the queue
                # and keep the most general one of them as 'lit'.
                # (i.e. the one with the weaker bound value).
                if (next_dl, next_ev_i) == (ev_i_dl, ev_i):
                    heapq.heappop(prio_queue)
                    if lit.bound.is_stronger_than(next_lit.bound):
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
                asserting_clause.append(lit.neg)
                return ConflictAnalysisResult(tuple(asserting_clause),
                                              resolved_literals)

            # Now, we need to backtrack until the latest falsifying event.
            # This will undo some of the changes, but we will remain in
            # the same decision level. This partial backtracking is necessary
            # to provide explainers (reasoners) with the exact state in which
            # their decisions were made. The event cannot be a decision,
            # because otherwise it would have been detected as a UIP earlier.

            cause: Optional[Causes.AnyCause] = None
            while ev_i < self.state.num_events_at_current_decision_level:
                ev = self._undo_and_return_latest_event_at_current_decision_level()
                cause = ev.cause

            assert cause is not None

            if (lit.signed_var not in resolved_literals
                or lit.bound.is_stronger_than(resolved_literals[lit.signed_var])
            ):
                resolved_literals[lit.signed_var] = lit.bound                

            # Add a set of literals whose conjunction implies lit to explanation_literals
            self._add_implying_literals_to_explanation(explanation,
                                                       lit,
                                                       cause,
                                                       explain_function)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_decision_level_to_backtrack_to(self,
        asserting_clause: Tuple[Lit,...],
    ) -> Tuple[bool, int, Optional[Lit]]:
        """
        Args:
            asserting_clause: The literals composing an asserting clause.

        Returns:
            A tuple interpreted as follows:
                - 1st element indicates whether the clause is conflicting at the \
                    top decision level (which would prove unsatisfiability).
                - 2nd element indicates the appropriate backtrack level.
                - 3rd element indicates asserted at that level.
        
        Note:
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

        for literal in asserting_clause:

            if not (self.state.bound_of(literal.neg.signed_var)
                    .is_stronger_than(literal.neg.bound)
            ):

                first_entailing_ev = self.state.get_first_event_entailing(literal.neg)

                if first_entailing_ev is None or first_entailing_ev.index[0] == 0:
                    continue

                dl = first_entailing_ev.index[0]
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

    #############################################################################
    # VARIABLE ADDITION | DOC: OK 23/10/23 | 1 TODO
    #############################################################################

    def add_new_non_optional_variable(self,
        initial_domain: Tuple[int, int],
        controllable: bool,
    ) -> Var:
        """
        Registers and returns a new non optional variable with the given `initial_domain`.
        """

        return self.state.add_new_variable(initial_domain, controllable, TRUE_LIT)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_new_optional_variable(self,
        initial_domain: Tuple[int, int],
        controllable: bool,
        presence_literal: Lit,
    ) -> Var:
        """
        Registers and returns a new variable with the given `initial_domain` and `presence_literal`.
        """

        return self.state.add_new_variable(initial_domain, controllable, presence_literal)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_new_presence_variable(self,
        scope_representative_literal: Lit,
    ) -> Var:
        """
        Registers and returns a new presence variable
        defined in the scope corresponding to `scope_literal`.

        TODO: details on scopes ?

        Note:
            A presence variable is simply a non optional variable with initial
            domain (0, 1) used to encode presence literals. A presence literal
            is a literal `[pvar >= 1]` where `pvar` is a presence variable.
        """
        
        var = self.state.add_new_variable((0, 1), True, TRUE_LIT)
        
        lit = Lit.geq(var, 1)
        self.state.register_and_sort_scope((lit,), lit)
        self.state.register_presence_literals_implication(lit, scope_representative_literal)
        
        return var

    #############################################################################
    # CONSTRAINT ADDITION | DOC: OK 23/10/23
    #############################################################################

    def add_constraint(self,
        constr_expr: ConstrExpr,
        constr_value_lit: Lit,
#    ) -> Tuple[ElemConstrExpr, Lit]:
    ) -> None:
        """
        Adds a constraint defined by the given high-level expression `constr_expr`,
        enforced to hold iff `constr_value_lit` is true.

        Args:
            constr_expr: A high-level constraint expression defining the constraint.
            constr_value_lit: A literal that should be true iff the constraint holds.

        Note:
            Internally, `constr_expr` is preprocessed into a low-level, elementary
            form. This "elementary form" constraint may make use of new,
            "intermediary" literals created during the preprocessing.
        """

        elem_constr_expr: ElemConstrExpr = self._preprocess_constr_expr_into_elem_form(constr_expr)

        self.state._add_elem_constraint(elem_constr_expr, constr_value_lit)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_scoped_constraint(self,
        constr_expr: ConstrExpr,
        scope: Tuple[Lit,...],
#    ) -> Tuple[ElemConstrExpr, Lit]:
    ) -> Lit:
        """
        Adds a constraint defined by the given high-level expression `constr_expr`,
        enforced to hold in the given `scope`. This corresponds to a full constraint
        `l_1 & ... & l_n => "constraint holds"` (where `l_i` are the literals of `scope`),
        i.e. ``scope_tautology_literal` <=> "constraint holds"` (where `scope_tautology_literal`
        is the `scope`'s tautology literal).
        
        Args:
            constr_expr: A high-level constraint expression defining the constraint.
            scope: The scope in which the constraint must hold.

        Returns:
            The `scope`'s tautology literal.

        Note:
            Internally, `constr_expr` is preprocessed into a low-level, elementary
            form. This "elementary form" constraint may make use of new,
            "intermediary" literals created during the preprocessing.
        """

#        scope_representative_lit = self.state.get_scope_representative_literal(scope)
#        scope_tautology_lit = self.state._scopes_representative_lits[scope_representative_lit].tautology_literal

        # Why not this ?:
        scope_tautology_lit: Lit = self.state.get_scope_tautology_literal(scope)

        self.add_constraint(constr_expr, scope_tautology_lit)

        return scope_tautology_lit
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _preprocess_constr_expr_into_elem_form(self,
        constr_expr: ConstrExpr,
    ) -> ElemConstrExpr:
        """
        Preprocesses a high-level constraint expression by decomposing it
        into a low-level elementary constraint expression.
        
        For equality and disequality constraints, it can be formed of
        new literals resulting from an "intermediary" reification.
        
        For example, an equality constraint expression is interpeted as two "leq"
        elementary constraint expressions, each of which corresponds to either
        single literal, or a "max difference" elementary constraint expression. 
        Both of these elementary constraint expressions are then reified resulting
        in two reification literals. Finally, an "and" elementary constraint
        expression combining these two reification literals is returned.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def get_or_make_reification_of_elem_constr_expr(
            elem_constr_expr: ElemConstrExpr,
        ) -> Lit:

            if elem_constr_expr in self.state._reifications:
                return self.state._reifications[elem_constr_expr]
            
            scope = self.state._get_elem_constr_expr_scope(elem_constr_expr)
            scope_representative_lit = self.state.get_scope_representative_literal(scope)
            
            reif_lit = Lit.geq(self.state.add_new_variable((0,1), True, scope_representative_lit), 1)

            self.state._reifications[elem_constr_expr] = reif_lit
            self.state._reifications[elem_constr_expr.neg] = reif_lit.neg
            self.state._constraints.append((elem_constr_expr, reif_lit))

            return reif_lit

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def preprocess_eq_int_atoms(
            int_atom_left: IntAtom,
            int_atom_right: IntAtom,
        ) -> ElemConstrExpr:

            if int_atom_left.var == int_atom_right.var:
                return ElemConstrExpr.from_lit(TRUE_LIT)

            leq12_elem_form = ElemConstrExpr.from_int_atoms_leq(int_atom_left, int_atom_right)
            leq21_elem_form = ElemConstrExpr.from_int_atoms_leq(int_atom_right, int_atom_left)

            leq12_reif_lit = get_or_make_reification_of_elem_constr_expr(leq12_elem_form)
            leq21_reif_lit = get_or_make_reification_of_elem_constr_expr(leq21_elem_form)

            return ElemConstrExpr.from_lits_and((leq12_reif_lit, leq21_reif_lit))  # FIXME: or of negs ?

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        def preprocess_eq_bool_atoms(
            bool_atom1: BoolAtom,
            bool_atom2: BoolAtom,
        ) -> ElemConstrExpr:

            if bool_atom1.var == bool_atom2.var:
                return ElemConstrExpr.from_lit(TRUE_LIT)

            lit1 = Lit.geq(bool_atom1.var, 1)
            lit2 = Lit.geq(bool_atom2.var, 1)

            imply12_elem_form = ElemConstrExpr.from_lits_or((lit1.neg, lit2))
            imply21_elem_form = ElemConstrExpr.from_lits_or((lit2.neg, lit1))

            imply12_reif_lit = get_or_make_reification_of_elem_constr_expr(imply12_elem_form)
            imply21_reif_lit = get_or_make_reification_of_elem_constr_expr(imply21_elem_form)

            return ElemConstrExpr.from_lits_and((imply12_reif_lit, imply21_reif_lit))  # FIXME: or of negs ?

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        match constr_expr.terms:

            case IntAtom(), IntAtom():
                int_atom_left, int_atom_right = constr_expr.terms
            
                match constr_expr.kind:

                    case ConstrExpr.Kind.LEQ:
                        return ElemConstrExpr.from_int_atoms_leq(int_atom_left, int_atom_right)
                    case ConstrExpr.Kind.LT:
                        return ElemConstrExpr.from_int_atoms_leq(int_atom_left, IntAtom(int_atom_right.var,
                                                                                        int_atom_right.offset_cst-1))
                    case ConstrExpr.Kind.GEQ:
                        return ElemConstrExpr.from_int_atoms_leq(int_atom_right, int_atom_left)
                    case ConstrExpr.Kind.GT:
                        return ElemConstrExpr.from_int_atoms_leq(int_atom_right, IntAtom(int_atom_left.var,
                                                                                         int_atom_left.offset_cst-1))
                    case ConstrExpr.Kind.EQ:
                        return preprocess_eq_int_atoms(int_atom_left, int_atom_right)
                    case ConstrExpr.Kind.NEQ:
                        return preprocess_eq_int_atoms(int_atom_left, int_atom_right).neg
                    case _:
                        assert False

            case FracAtom(), FracAtom():

                assert constr_expr.terms[0].denom == constr_expr.terms[1].denom
                int_atom_left = constr_expr.terms[0].numer_int_atom
                int_atom_right = constr_expr.terms[1].numer_int_atom

                match constr_expr.kind:

                    case ConstrExpr.Kind.LEQ:
                        return ElemConstrExpr.from_int_atoms_leq(int_atom_left, int_atom_right)
                    case ConstrExpr.Kind.LT:
                        return ElemConstrExpr.from_int_atoms_leq(int_atom_left, IntAtom(int_atom_right.var,
                                                                                        int_atom_right.offset_cst-1))
                    case ConstrExpr.Kind.GEQ:
                        return ElemConstrExpr.from_int_atoms_leq(int_atom_right, int_atom_left)
                    case ConstrExpr.Kind.GT:
                        return ElemConstrExpr.from_int_atoms_leq(int_atom_right, IntAtom(int_atom_left.var,
                                                                                         int_atom_left.offset_cst-1))
                    case ConstrExpr.Kind.EQ:
                        return preprocess_eq_int_atoms(int_atom_left, int_atom_right)
                    case ConstrExpr.Kind.NEQ:
                        return preprocess_eq_int_atoms(int_atom_left, int_atom_right).neg
                    case _:
                        assert False

            case BoolAtom(), BoolAtom():
                bool_atom1, bool_atom2 = constr_expr.terms

                match constr_expr.kind:

                    case ConstrExpr.Kind.EQ:
                        return preprocess_eq_bool_atoms(bool_atom1, bool_atom2)
                    case ConstrExpr.Kind.NEQ:
                        return preprocess_eq_bool_atoms(bool_atom1, bool_atom2).neg
                    case _:
                        assert False

            case [Lit(), *_] as lits: 

                match constr_expr.kind:

                    case ConstrExpr.Kind.OR:
                        return ElemConstrExpr.from_lits_or(lits)
                    case ConstrExpr.Kind.AND:
                        return ElemConstrExpr.from_lits_and(tuple(lit.neg for lit in lits))
                    case ConstrExpr.Kind.IMPLY:
                        if len(lits) != 2:
                            assert False
                        lit_from, lit_to = lits[0], lits[1]
                        return ElemConstrExpr.from_lits_or((lit_from.neg, lit_to))
                    case _:
                        assert False

        raise ValueError("Constraint expression could not be interpreted.")

    #############################################################################
    # CONSTRAINT POSTING TO REASONERS | DOC: OK 23/10/23
    #############################################################################

#    def _actually_post_reified_constraint(self,
    def _post_constraint_to_reasoners(self,
        constraint: Tuple[ElemConstrExpr, Lit],
    ) -> Optional[InvalidBoundUpdate]:
        """
        Preprocesses and posts a low-level, elementary
        `constraint` to the appropriate reasoner.

        Returns:
            A conflict if one was encountered when attempting to post the `constraint`.
        """
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
        def make_safe_for_unit_propag(
            clause: Tuple[Lit,...],
            scope_representative_lit: Lit,
        ) -> Tuple[Tuple[Lit,...], Lit]:
            """
            NOTE: this could be generalized to look at
            literals in the clause as potential scopes
            """

            if scope_representative_lit == TRUE_LIT:
                return (clause, TRUE_LIT)
            
            # The clause can never be true, so it will have to be made absent.
            if len(clause) == 0:
                return ((scope_representative_lit.neg,), TRUE_LIT)

            if all(self.state.entails_implication(self.state.presence_literal_of(lit.signed_var.var),
                                                  scope_representative_lit)
                                                  for lit in clause):
                return (clause, scope_representative_lit)

            return (simplify_lits_disjunction(clause+(scope_representative_lit.neg,)), TRUE_LIT)

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def preprocess_then_add_scoped_clause_to_sat_reasoner(
            clause: Tuple[Lit,...],
            scope_representative_literal: Lit,
            clause_already_in_simplified_form: bool,
        ) -> Optional[InvalidBoundUpdate]:
            """
            Preprocesses the `clause` and the `scope_representative_literal` by:
            - Simplifying the `clause` (if wasn't already).
            - Removing unnecessary (already known to be false) literals from `clause`.
                - If this removes all literals / results in the clause being empty,
                then the clause is false and thus we must leave it scope.
                So `scope_representative_literal` is set to false.
            - Making the literals of `clause` and the `scope_representative_literal`
            "safe" for unit propagation, by (in the general case) adding the negation
            of scope representative literal to the clause, and changing it to TRUE_LIT.
            - Adding the "safe" clause and scope representative literal to the `SATReasoner`
            as a fixed (i.e. non learned) scoped clause.
            """

            if clause_already_in_simplified_form:
                simplified_clause = simplify_lits_disjunction(clause)
            else:
                simplified_clause = clause
                
            # Remove clause literals that are guaranteed to not become true
            # (i.e. whose value is False / whose negation literal is entailed)

            true_or_unbounded_lits = list(simplified_clause)

            n = len(true_or_unbounded_lits)
            i = 0
            j = 0

            while i < n-j:
                if self.state.entails(true_or_unbounded_lits[i].neg):
                    true_or_unbounded_lits.pop(i)
                    j += 1
                else:
                    i += 1

            # If the preprocessing of the clause literals removed all of them,
            # then the scope literal must be enforced to be false.

            if len(true_or_unbounded_lits) == 0:

                res = self.state.set_literal(scope_representative_literal.neg,
                                             Causes.Encoding()) 

                return res if isinstance(res, InvalidBoundUpdate) else None

            # The clause literals may have literals on optional variables.
            # Thus the clause must be made "safe" for unit propagation in the SATReasoner.

            safe_clause, safe_scope_representative_lit = make_safe_for_unit_propag(tuple(true_or_unbounded_lits),
                                                                                   scope_representative_literal)

            assert self.sat_reasoner is not None

            self.sat_reasoner.add_new_fixed_clause_with_scope(safe_clause,
                                                              safe_scope_representative_lit)
            return None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        assert self.state.decision_level == 0

        (elem_constr_expr, constr_lit) = constraint
        scope_representative_lit = self.state.presence_literal_of(constr_lit.signed_var.var)

        # If the scope is False, then the constraint is absent: we thus ignore it.
        if self.state.entails(scope_representative_lit.neg):
            return None

        match elem_constr_expr.kind, elem_constr_expr.terms:

            case ElemConstrExpr.Kind.LIT, Lit() as lit:

                assert self.state.entails_implication(scope_representative_lit,
                                                      self.state.presence_literal_of(lit.signed_var.var))

                preprocess_then_add_scoped_clause_to_sat_reasoner((constr_lit.neg, lit),
                                                                  scope_representative_lit,
                                                                  False)
                preprocess_then_add_scoped_clause_to_sat_reasoner((lit.neg, constr_lit),
                                                                  scope_representative_lit,
                                                                  False)
                return None

            case (ElemConstrExpr.Kind.MAX_DIFFERENCE,
                (Var() as from_var, Var() as to_var, int() as max_diff)
            ):
                assert self.diff_reasoner is not None

                self.diff_reasoner.add_reified_difference_constraint(constr_lit,
                                                                     from_var,
                                                                     to_var,
                                                                     max_diff)
                return None

            case ElemConstrExpr.Kind.OR, [Lit(), *_] as lits:

                if self.state.entails(constr_lit):

                    preprocess_then_add_scoped_clause_to_sat_reasoner(lits, 
                                                                      scope_representative_lit, 
                                                                      False)
                    return None
                
                elif self.state.entails(constr_lit.neg):

                    for lit in lits:

                        res = preprocess_then_add_scoped_clause_to_sat_reasoner((lit.neg,),
                                                                                scope_representative_lit,
                                                                                False)
                        if res is not None:
                            return res

                    return None
                
                else:

                    simplified_clause = simplify_lits_disjunction((constr_lit.neg,)+lits)

                    if is_lits_disjunction_tautological(simplified_clause):

                        res = preprocess_then_add_scoped_clause_to_sat_reasoner(simplified_clause,
                                                                                scope_representative_lit,
                                                                                True)
                        if res is not None:
                            return res
                    
                    for lit in lits:

                        res = preprocess_then_add_scoped_clause_to_sat_reasoner((lit.neg, constr_lit),
                                                                                scope_representative_lit,
                                                                                False)
                        if res is not None:
                            return res

                    return None

            case ElemConstrExpr.Kind.AND, [Lit(), *_]:

                return self._post_constraint_to_reasoners((elem_constr_expr.neg, constr_lit.neg))

            case _:
                assert False

#################################################################################
