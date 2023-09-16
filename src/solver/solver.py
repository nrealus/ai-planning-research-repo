"""
TODO
"""

from __future__ import annotations

#################################################################################

import heapq
from typing import Callable, Dict, List, Optional, Tuple

from src.constraint_expressions import ConstrExpr, ElemConstrExpr
from src.fundamentals import TRUE_LIT, BoundVal, Lit, SignedVar, Var
from src.solver.common import (Causes, ConflictAnalysisResult, Decisions,
                               Event, InvalidBoundUpdateInfo,
                               ReasonerBaseExplanation)
from src.solver.reasoners.reasoner import Reasoner
from src.solver.solver_state import SolverState

#################################################################################
# SOLVER
#################################################################################

class Solver():
    """
    The main solver class.
    """

    def __init__(self):

        self.state: SolverState = SolverState()

    #############################################################################
    # DECISION CHOICE
    #############################################################################

    # TODO
    def choose_next_decision(self) -> Decisions.AnyDecision:
    
        raise NotImplementedError
    
    #############################################################################
    # DECISION LEVEL INCREMENTATION
    #############################################################################

    def increment_one_decision_level(self,
        reasoners: Tuple[Reasoner,...],
    ) -> None:
        """
        Increments the current decision level (by 1).
        
        Invokes all reasoners' `on_solver_increment_decision_level` callbacks, which
        updates them internally to account for the decision level incrementation.

        Args:
            reasoners: The reasoners collaborating with the solver.
        """

        # assert self.curr_dec_lvl == 0 or len(self._events_trail[self.curr_dec_lvl]) > 0

        self.state._dec_lvl += 1

        if len(self.state._events_trail) == self.state.decision_level:
            self.state._events_trail.append([])
        
        for reasoner in reasoners:
            reasoner.on_solver_increment_one_decision_level(self.state)

    #############################################################################
    # BACKTRACKING
    #############################################################################

    def _undo_and_return_latest_event_at_current_decision_level(self) -> Event:
        """
        Reverts the last event (at the current decision level) by:
            - Popping it from the events trail
            - By updating the current and previous bound values, as well as
            the index of its corresponding event.

        Returns:
            The event that was reverted.
        """

        ev = self.state._events_trail[self.state.decision_level].pop()

        self.state._bound_values[ev.signed_var] = ev.previous_bound_value
        self.state._bound_values_event_indices[ev.signed_var] = ev.previous_index

        return ev

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def backtrack_to_decision_level(self,
        target_decision_level: int,
        reasoners: Tuple[Reasoner,...],
    ) -> None:
        """
        Backtracks to the target decision level by reverting all events at all
        decision levels strictly greater than the target one.

        Invokes the reasoners' `on_solver_backtrack_one_level` callbacks, at
        each reverted decision level. This updates the reasoners internally to
        account for the backtracking.

        Args:
            target_decision_level: The target decision level to backtrack to.

            reasoners: The reasoners collaborating with the solver.

        Raises:
            ValueError: If the target decision level was strictly less than 0.
        """

        if target_decision_level < 0:
            raise ValueError("Target decision level must be >= 0.")

        while self.state.decision_level > target_decision_level:

            for _ in range(self.state.num_events_at_current_decision_level):
                self._undo_and_return_latest_event_at_current_decision_level()

            self.state._dec_lvl -= 1

            for reasoner in reasoners:
                reasoner.on_solver_backtrack_one_decision_level(self.state)

    #############################################################################
    # PROPAGATION
    #############################################################################

    def propagate(self,
        reasoners:Tuple[Reasoner,...],
    ) -> Optional[Tuple[InvalidBoundUpdateInfo | ReasonerBaseExplanation, Reasoner]]:
        """
        The propagation method of the solver.
        
        For all reasoners, propagates new events/changes. The propagation
        process stops either when no new bound update can be inferred (success),
        or when a contradiction is detected by one of the reasoners (failure).

        Args:
            reasoners: The reasoners collaborating with the solver.

        Returns:
            None if the propagation was successful, and a tuple if a conflict   \
            is encountered. The tuple is composed of information on the conflict\
            as well as the reasoner that encountered it.
        """

        while True:
            num_events = self.state.num_events_at_current_decision_level

            for reasoner in reasoners:
                conflict_info = reasoner.propagate(self.state)

                if conflict_info is not None:
                    return (conflict_info, reasoner)
        
            if num_events == self.state.num_events_at_current_decision_level:
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
         - `literal` is not entailed in the current state
         - `cause` provides the explanation for asserting
            literal (and is not a decision)

        Args:
            explanation_literals: The list of literals making   \
                up the explanation. Modified by the method.

            literal: The literal whose implying literals we     \
                want to add to the explanation.

            cause: The cause for the event that lead to the     \
                contradiction that we're explaining.

            explain_function: The external function that may participate    \
                in building the explanation (basically the `explain`        \
                function of `Reasoner`)
        """

        # In this function, the literal shouldn't be true yet,
        # but it should be immediately implied.
        assert not self.state.is_entailed(literal)

        match cause:

            case Causes.ReasonerInference():
                # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => literal
                explain_function(explanation_literals, literal, cause, self)

            case Causes.ImplicationPropagation():
                explanation_literals.append(cause.literal)

            case Causes.EmptyDomain():
                explanation_literals.append(cause.literal.negated)

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
            invalid_bound_update_info: The information about the conflict to explain.

            explain_function: The external function that may participate in building the explanation    \
                (basically the `explain` function of `Reasoner`)
        
        Returns:
            The results of conflict analysis.

        """
        
        # Remember that an update is invalid iff its negation holds AND
        # the affected variable is present.

        # The base of the explanation is ('not l' v 'l')
        explanation_starting_literals = [invalid_bound_update_info.literal.negated]

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
            explanation_literals: The list of literals making up the explanation.   \
                Modified by the method.

            explain_function: The external function that may participate in building the explanation    \
                (basically the `explain` function of `Reasoner`)

        Returns:
            The results of conflict analysis.

        Note:
            A partial backtrack (within the current decision level) will occur
            in this function. This is necessary to provide explainers (reasoners)
            with the exact state in which their decisions were made.

            However there is no need to "synchronize"/update the reasoners' earliest
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
        asserting_clause_literals = []

        resolved_literals: Dict[SignedVar, BoundVal] = {}

        while True:

            for lit in explanation_literals:

                if self.state.is_entailed(lit):

                    first_entailing_ev = self.state.first_event_entailing(lit)

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
                        asserting_clause_literals.append(lit.negated)

                    else:
                        assert False
                
                # If lit is is not entailed, it must have been added in
                # an eager propagation. Even if it was not necessary for
                # this propagation to occur, it must be part of the clause
                # for correctness.
                else:
                    asserting_clause_literals.append(lit.negated)
                
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
                asserting_clause_literals.append(lit.negated)
                return ConflictAnalysisResult(tuple(asserting_clause_literals),
                                              resolved_literals)

            # Now, we need to until the latest falsifying event. This
            # will undo some of the changes, but we will remain in the
            # same decision level (see function description for the
            # reason behind this partial backtracking). Indeed, the event
            # cannot be a decision, because otherwise it would have been
            # detected as a UIP earlier.

            cause: Optional[Causes.AnyCause] = None
            while ev_i < self.state.num_events_at_current_decision_level:
                ev = self._undo_and_return_latest_event_at_current_decision_level()
                cause = ev.cause

            assert cause is not None

            if (lit.signed_var not in resolved_literals
                or lit.bound_value.is_stronger_than(resolved_literals[lit.signed_var])
            ):
                resolved_literals[lit.signed_var] = lit.bound_value                

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
        Returns:
            A tuple consisting of the appropriate backtracking level for the \
                clause formed by the given clause literals, the literal that \
                is asserted at that level, and whether the clause is         \
                conflicting at the top decision level (which would prove     \
                unsatisfiability).
        
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

        for literal in asserting_clause_literals:

            if not (self.state.bound_value_of(literal.negated.signed_var)
                    .is_stronger_than(literal.negated.bound_value)
            ):

                first_entailing_ev = self.state.first_event_entailing(literal.negated)

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
    # VARIABLE ADDITION
    #############################################################################

    def add_new_non_optional_variable(self,
        initial_domain: Tuple[int, int],
        controllable: bool,
    ) -> Var:
        """
        Adds a new non-optional variable to the solver and returns it.
        """

        return self.state._add_new_variable(initial_domain, controllable, TRUE_LIT)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_new_optional_variable(self,
        initial_domain: Tuple[int, int],
        controllable: bool,
        presence_literal: Lit,
    ) -> Var:
        """
        Adds a new optional variable to the solver and returns it.
        """

        return self.state._add_new_variable(initial_domain, controllable, presence_literal)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_new_presence_variable(self,
        scope_literal: Lit,
    ) -> Var:
        """
        Adds a new presence variable, defined in the scope corresponding to
        the given scope literal, and returns it.

        A presence variable is simply a non-optional (boolean) variable
        which is used to define presence literals.

        A presence literal, is simply a literal on (the truth value of) a presence
        variable. They are encoded as [presence_variable >= 1].
        """
        
        var = self.add_new_non_optional_variable((0,1), True)
        
        lit = Lit.geq(var, 1)
        self.state._register_new_scope_after_sorting((lit,), lit)
        self.state._register_implication_between_literals_on_non_optional_vars(lit, scope_literal)
        
        return var

    #############################################################################
    # CONSTRAINT ADDITION
    #############################################################################

    def add_constraint(self,
        constr_expr: ConstrExpr,
        scope_as_conjunction: Tuple[Lit,...],
    ) -> Tuple[ElemConstrExpr, Lit]:
        """
        Adds a constraint defined by the given high-level expression,
        in a scope defined by a conjunction of literals.

        In other words, we register the fact that the constraint will have to
        hold / be true / be satisfied iff all of the given literals are entailed.

        Internally, the high-level constraint expression is preprocessed into a
        low-level, "elementary" form. This elementary form could be defined with
        new literals, resulting from "intermediary" reification during the preprocessing.

        Then, this elementary form constraint is reified to an optional literal
        that is true iff the expression is valid/well-defined, and absent otherwise.

        Args:
            constr_expr: The high-level constraint expression defining the constraint to add.
            scope_as_conjunction: The literals whose conjunction defines the scope  \
                in which the constraint will have to hold.

        Returns:
            A reified constraint, formed by the elementary form expression as well \
                as that optional literal (sometimes called the reification literal).
        """

        elem_constr_expr = self._preprocess_constr_expr_into_elem_form(constr_expr)

        scope_tautology_lit = \
            self.state._get_or_make_tautology_of_scope(
                self.state._get_or_make_new_scope_lit_from_conjunction(scope_as_conjunction))

        return self.state._add_elem_constraint(elem_constr_expr, scope_tautology_lit)
    
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
        in two reification literals. Finally, an "AND" elementary constraint
        expression combining these two reification literals is returned.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def get_or_make_reification_of_elem_constr_expr(
            elem_constr_expr: ElemConstrExpr,
        ) -> Lit:

            if elem_constr_expr in self.state._reifications:
                return self.state._reifications[elem_constr_expr]
            
            scope_lit = \
                self.state._get_or_make_new_scope_lit_from_conjunction(
                    self.state._get_scope_as_conjunction(elem_constr_expr))
            
            reif_lit = Lit.geq(self.state._add_new_variable((0,1), True, scope_lit), 1)

            self.state._reifications[elem_constr_expr] = reif_lit
            self.state._reifications[elem_constr_expr.negated] = reif_lit.negated
            self.state._constraints.append((elem_constr_expr, reif_lit))

            return reif_lit

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def preprocess_eq_int_atoms(
            var_left: Var,
            offset_left: int,
            var_right: Var,
            offset_right: int,
        ) -> ElemConstrExpr:

            if var_left == var_right:
                return ElemConstrExpr.from_lit(TRUE_LIT)

            leq12_elem_form = ElemConstrExpr.from_int_atoms_leq(var_left, offset_left,
                                                                var_right, offset_right)
            leq21_elem_form = ElemConstrExpr.from_int_atoms_leq(var_right, offset_right,
                                                                var_left, offset_left)
            leq12_reif_lit = get_or_make_reification_of_elem_constr_expr(leq12_elem_form)
            leq21_reif_lit = get_or_make_reification_of_elem_constr_expr(leq21_elem_form)

            return ElemConstrExpr.from_lits_simplify_and((leq12_reif_lit, leq21_reif_lit))  # FIXME: or of negs ?

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        def preprocess_eq_bool_vars(
            var1: Var,
            var2: Var,
        ) -> ElemConstrExpr:

            if var1 == var2:
                return ElemConstrExpr.from_lit(TRUE_LIT)

            lit1 = Lit.geq(var1, 1)
            lit2 = Lit.geq(var2, 1)

            imply12_elem_form = ElemConstrExpr.from_lits_simplify_or((lit1.negated, lit2))
            imply21_elem_form = ElemConstrExpr.from_lits_simplify_or((lit2.negated, lit1))

            imply12_reif_lit = get_or_make_reification_of_elem_constr_expr(imply12_elem_form)
            imply21_reif_lit = get_or_make_reification_of_elem_constr_expr(imply21_elem_form)

            return ElemConstrExpr.from_lits_simplify_and((imply12_reif_lit, imply21_reif_lit))  # FIXME: or of negs ?

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        match constr_expr.terms:

            case ((Var() as var_left, int() as offset_left), 
                (Var() as var_right, int() as offset_right)
            ):
                match constr_expr.kind:

                    case ConstrExpr.Kind.LEQ:
                        return ElemConstrExpr.from_int_atoms_leq(var_left, offset_left,
                                                                 var_right, offset_right)
                    case ConstrExpr.Kind.LT:
                        return ElemConstrExpr.from_int_atoms_leq(var_left, offset_left,
                                                                 var_right, offset_right-1)
                    case ConstrExpr.Kind.GEQ:
                        return ElemConstrExpr.from_int_atoms_leq(var_right, offset_right,
                                                                 var_left, offset_left)
                    case ConstrExpr.Kind.GT:
                        return ElemConstrExpr.from_int_atoms_leq(var_right, offset_right,
                                                                 var_left, offset_left-1)
                    case ConstrExpr.Kind.EQ:
                        return preprocess_eq_int_atoms(var_left, offset_left,
                                                       var_right, offset_right)
                    case ConstrExpr.Kind.NEQ:
                        return preprocess_eq_int_atoms(var_left, offset_left,
                                                       var_right, offset_right).negated
                    case _:
                        raise ValueError(("Incompatible constraint type and ",
                                          "terms: for pairs of integer atoms ",
                                          "(variable + offset), only LEQ, LT, ",
                                          "GEQ, GT, EQ and NEQ constraints are defined."))

            case Var() as var1, Var() as var2:

                match constr_expr.kind:

                    case ConstrExpr.Kind.EQ:
                        return preprocess_eq_bool_vars(var1, var2)

                    case ConstrExpr.Kind.NEQ:
                        return preprocess_eq_bool_vars(var1, var2).negated

                    case _:
                        raise ValueError(("Incompatible constraint type and ",
                                          "terms: for pairs of boolean variables, ",
                                          "only EQ, and NEQ constraints are defined."))

            case [Lit(), *_] as lits: 

                match constr_expr.kind:

                    case ConstrExpr.Kind.OR:
                        return ElemConstrExpr.from_lits_simplify_or(lits)

                    case ConstrExpr.Kind.AND:
                        return ElemConstrExpr.from_lits_simplify_and(tuple(lit.negated for lit in lits))

                    case ConstrExpr.Kind.IMPLY:
                        if len(lits) == 2:
                            lit_from, lit_to = lits[0], lits[1]
                            return ElemConstrExpr.from_lits_simplify_or((lit_from.negated, lit_to))
                        else:
                            raise ValueError(("Incorrect number of terms: ",
                                              "IMPLY constraints require",
                                              "exactly two literals."))
                    case _:
                        raise ValueError(("Incompatible constraint type and ",
                                          "terms: OR, AND, and IMPLY constraints ",
                                          "require a sequence of literals."))

        raise ValueError("""Constraint expression could not be interpreted.""")
