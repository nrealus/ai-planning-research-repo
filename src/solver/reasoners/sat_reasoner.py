"""
TODO
"""

#################################################################################

from __future__ import annotations

#################################################################################

import typing
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Set

from src.fundamentals import TRUE_LIT, BoundVal, Lit
from src.solver.common import Causes, ReasonerBaseExplanation, SetGuardedByLiterals
from src.solver.reasoners.reasoner import Reasoner
from src.solver.solver_state import SolverState

MAX_INT = 2**64

#################################################################################
# SAT REASONER
#################################################################################

class SATReasoner(Reasoner):
    """
    Also called "Disjunctive Reasoner". It acts as a SAT solver. It
    maintains the database of clauses and performs unit propagation.

    In essence, for each clause in the database, we look for distinct 
    literals that are not falsified by the current domains:

    - If all literals are false, the clause is violated and a conflict
    is reported, which will cause the search to backtrack.
    
    - If all but one literal `l` are false, then the clause is unit
    and `l` is enforced/set.
    
    - Otherwise, two non-false literals are selected and added to a "watch list".
    Once one of these literal is set, the clause will be reevaluated.
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # 

    def _get_literal_value(self,
        literal: Lit,
    ) -> Optional[bool]:
        """
        Syntactic sugar around `self.state.is_entailed`.

        Args:
            literal: A literal.

        Returns:
            True if `literal` is true (i.e. currently entailed). False if   \
                it is false (i.e. its negation is currently entailed).      \
                None otherwise (i.e. `literal` is unbound: it isn't yet     \
                known to be true or false).
        """ 

        if self.state.is_entailed(literal):
            return True
        elif self.state.is_entailed(literal.negated):
            return False
        else:
            return None

    #############################################################################
    # CLAUSE ID, CLAUSE DATA 
    #############################################################################
    
    @dataclass
    class Clause():
        """Keeps the data of a clause registered in the clause database."""
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        literals: Tuple[Lit,...]
        """The literals of the clause (without the scope literal)."""

        scope_literal: Lit
        """
        The literal representing the scope in which the clause
        (or rather its literals' variables) are defined.

        As such, the true "meaning" of the clause can be expressed with the
        following disjunction: `(not scope_literal) | l_1 | ... | l_n`.

        This also means that a clause whose literals are all false is only a
        conflict when we cannot "get out of" its scope (i.e. make
        its `scope_literal` False).
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        learned: bool
        """Whether the clause is learned (i.e. resulting from conflict analysis) or not."""

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        watch1_index: int = field(init=False)
        """Index of the first watched literal of the clause."""

        watch2_index: int = field(init=False)
        """Index of the second watched literal of the clause."""

        unwatched_indices: List[int] = field(init=False)
        """List of the indices of unwatched literals of the clause."""

        @property
        def watch1(self) -> Lit:
            return self.literals[self.watch1_index]

        @property
        def watch2(self) -> Lit:
            return self.literals[self.watch2_index]

        def unwatched(self, i: int) -> Lit:
            return self.literals[self.unwatched_indices[i]]

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        activity: float = field(init=False)
        """
        TODO
        """

        # lbd: float = field(init=False)
        # """
        # TODO
        # """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        def __init__(self,
            literals: Tuple[Lit,...],
            scope_literal: Lit,
            learned: bool,
        ):

            self.literals = literals
            self.scope_literal = scope_literal
            self.learned = learned
            
            self.activity = 0
            # self.lbd = 0

            len_literals = len(self.literals)
            if len_literals == 0:
                raise ValueError(("Empty clauses are not allowed in the ",
                                  "SAT reasoner / clause database"))
            
            self.watch1_index = 0
            self.watch2_index = 1 if len_literals > 1 else 0
            self.unwatched_indices = list(range(2, len_literals)) if len_literals > 2 else []

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ClauseId(int):
        """Represents the ID of a clause in the database."""
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
 
    def __init__(self,
        state: SolverState,
    ):

        self._state: SolverState = state

        self._clauses_id_counter: int = 0
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.clauses_database: Dict[SATReasoner.ClauseId, SATReasoner.Clause] = {}
        """The clauses database."""

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.clause_activity_increase: float = 1

        self.clause_activity_decay: float = 0.999

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.num_fixed_clauses: int = 0

        self.num_learned_clauses: int = 0

        self.num_allowed_learned_clauses: int = 0

        self.num_allowed_learned_clauses_base: int = 1000

        self.num_allowed_learned_clauses_ratio: float = 1/3

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.num_conflicts: int = 0

        self.num_conflicts_at_last_database_expansion: int = 0

        self.num_conflicts_allowed_before_database_expansion: int = 0

        self.database_expansion_ratio: float = 1.05

        self.increase_ratio_of_conflicts_before_db_expansion: float = 1.5

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.locked_clauses: Set[SATReasoner.ClauseId] = set()
        """
        Contains all locked clauses (locked at all previous decision levels).
        A clause that is marked as locked cannot be removed from the clause
        database as part of database rescaling / forgetting of learned clauses.
        
        Marking a clause as locked is necessary when that clause may be needed
        for explanation mechanisms.
        """

        self.locked_clauses_trail: List[List[SATReasoner.ClauseId]] = [[]]
        """
        Trail of locked clauses. Outer list index: decision level.
        Inner list content: clauses locked while at that decision level.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.watchlists: SetGuardedByLiterals[SATReasoner.ClauseId] = SetGuardedByLiterals()
        """
        Represents literals' "watch lists" (lists of clauses where they appear).

        Internally, a literal [signed_var <= val]'s watchlist is represented as:
        { signed_var : { val : [clause1_id, clause2_id, ...] }}
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.pending_clauses_info: List[Tuple[SATReasoner.ClauseId, Optional[Lit]]] = []
        """
        Stores clauses that have been recorded to the database,
        but not processed yet.

        The first element of the tuple is the ID of the clause to propagate.
        
        The second element is either None or a literal that is entailed by
        the clause at the current decision level. This literal MUST be set
        to true, with this clause as its cause, even if the clause is not
        unit.
        
        This situation might happen when the clause was learned from
        a conflict involving eager propagation of optional variables.
        """

        self.next_unprocessed_solver_event_index: int = 0
        """
        The index of the next unprocessed (i.e. not yet propagated) event
        in the main solver's events trail (in the current decision level).
        """
    
    @property
    def state(self) -> SolverState:
        return self._state

    #############################################################################
    # CLAUSE ADDITION / REGISTRATION
    #############################################################################

    def add_new_fixed_clause_with_scope(self,
        clause_literals: Tuple[Lit,...],
        scope_literal: Lit,
    ) -> None:
        """
        Adds a new non-learned clause to the clauses database
        and to the pending clauses queue.

        Args:
            clause_literals: The literals composing the clause.

            scope_literal: The literal representing the scope in which  \
                the clause is defined.

        Returns:
            The ID given to the clause after being registered in the clauses database.
        """

        clause_id = self._add_new_clause(clause_literals, scope_literal, False)
        self.pending_clauses_info.insert(0, (clause_id, None))
        self.num_fixed_clauses += 1

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_new_learned_clause(self,
        asserting_clause_literals: Tuple[Lit,...],
        asserted_literal: Optional[Lit],
    ) -> None:
        """
        Adds a new learned clause to the clauses database
        and to the pending clauses queue.
        
        Args:
            clause_literals: The literals composing the clause.

            scope_literal: The literal representing the scope in which  \
                the clause is defined.

        Returns:
            The ID given to the clause after being registered in the clauses database.
        """

        assert asserted_literal is None or asserted_literal in asserting_clause_literals

        clause_id = self._add_new_clause(asserting_clause_literals, TRUE_LIT, True)
        self.pending_clauses_info.insert(0, (clause_id, asserted_literal))
        self.num_learned_clauses += 1
        self.num_conflicts += 1

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_new_clause(self,
        clause_literals: Tuple[Lit,...],
        scope_literal: Lit,
        learned: bool,
    ) -> SATReasoner.ClauseId:
        """
        Adds a new clause to the clauses database.
        Used by the higher level clause addition functions.
        """

        clause_id = SATReasoner.ClauseId(self._clauses_id_counter)
        self._clauses_id_counter += 1
        self.clauses_database[clause_id] = SATReasoner.Clause(clause_literals,
                                                              scope_literal,
                                                              learned)
        return clause_id

    #############################################################################
    # WATCHES (WATCHED LITERALS & WATCHLISTS)
    #############################################################################

    def _swap_watch1_and_watch2(self,
        clause_id: SATReasoner.ClauseId,
    ) -> None:
        """Swaps the 1st and 2nd watched literals of a clause."""

        clause = self.clauses_database[clause_id]

        clause.watch1_index, clause.watch2_index = \
            clause.watch2_index, clause.watch1_index

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
 
    def _swap_watch2_and_unwatched_i(self,
        clause_id: SATReasoner.ClauseId,
        i: int
    ) -> None:
        """Swaps the 2nd watched literal with the i-th unwatched literal of a clause."""

        clause = self.clauses_database[clause_id]

        clause.watch2_index, clause.unwatched_indices[i] = \
            clause.unwatched_indices[i], clause.watch2_index

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
            
    def _move_watches_front(self,
        clause_id: SATReasoner.ClauseId,
    ) -> None:
        """
        Selects the two (unbound) literals that should be watched
        and make them the watched literals of the clause.

        After the method completion, the 1st watched literal will have the
        highest priority and the 2nd watched literal will have the second highest
        priority. The order of the other (unwatched) literals is undefined.

        The priority rule ordering (from highest to lowest):
        - True literals
        - Undefined literals
        - False literals, prioritizing those with the highest decision level
        - Leftmost literal in the original clause (to avoid swapping two literals with the same priority)
        """

        def priority_of_lit(lit: Lit) -> int:
            match self._get_literal_value(lit):
                case True:
                    return MAX_INT
                case None:
                    return MAX_INT-1
                case False:
                    first_impl_ev = self.state.first_event_entailing(lit.negated)
                    if first_impl_ev is None or first_impl_ev.index[0] == 0:
                        return 0
                    return first_impl_ev.index[0]+first_impl_ev.index[1]

        clause = self.clauses_database[clause_id]

        lvl0 = priority_of_lit(clause.watch1)
        lvl1 = priority_of_lit(clause.watch2)

        if lvl1 > lvl0:
            lvl0, lvl1 = lvl1, lvl0
            self._swap_watch1_and_watch2(clause_id)

        for i in range(len(clause.unwatched_indices)):
            lvl = priority_of_lit(clause.unwatched(i))

            if lvl > lvl1:
                lvl1 = lvl
                self._swap_watch2_and_unwatched_i(clause_id, i)

                if lvl > lvl0:
                    lvl1 = lvl0
                    lvl0 = lvl
                    self._swap_watch1_and_watch2(clause_id)
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_watch(self,
        clause_id: SATReasoner.ClauseId,
        literal: Lit,
    ) -> None:
        """Adds a clause to the watch list of a literal."""
        self.watchlists.add(clause_id, literal)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _remove_watch(self,
        clause_id: SATReasoner.ClauseId,
        literal: Lit,
    ) -> None:
        """Removes a clause from the watch list of a literal."""
        self.watchlists.remove(clause_id, literal)

    #############################################################################
    # MAIN SOLVER DECISION LEVEL INCREASE & DECREASE CALLBACKS
    #############################################################################

    def on_solver_increment_one_decision_level(self) -> None:
        
        self.next_unprocessed_solver_event_index = 0

        if len(self.locked_clauses_trail) == self.state.decision_level:
            self.locked_clauses_trail.append([])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_solver_backtrack_one_decision_level(self) -> None:

        for locked_clause in reversed(self.locked_clauses_trail[self.state.decision_level+1]):
            self.locked_clauses.remove(locked_clause)
        self.locked_clauses_trail[self.state.decision_level+1].clear()

        self.next_unprocessed_solver_event_index = self.state.num_events_at_current_decision_level

    #############################################################################
    # PROPAGATION
    #############################################################################

    def propagate(self) -> Optional[ReasonerBaseExplanation]:
        """
        Main propagation method of the SAT reasoner.
        Performs unit propagation (aka boolean constraint propagation).

        First, processes all pending clauses (i.e. clauses that were
        added to the database since last propagation but weren't processed
        yet), and sets their asserted literal to True (if they have one).

        If none of these clauses is found to be violated, any
        new ("enqueued") "unit information" resulting from
        the processing of pending clauses is propagated.

        If at any point, either during pending clauses processing or propagation,
        a clause is found to be violated, the negation of its literals is
        returned as a base explanation to be refined by the main solver.
        """

        violated_clause_id: Optional[SATReasoner.ClauseId] = None

        # Process pending clauses

        while self.pending_clauses_info:

            clause_id, asserted_literal = self.pending_clauses_info.pop()

            violated_clause_id = self._process_pending_clause(clause_id)

            if violated_clause_id is not None:
                break

            if asserted_literal is not None:

                if not self.state.is_entailed(asserted_literal):
                    self._set_from_unit_propagation(asserted_literal, clause_id)

        # If no violated clause was detected above,
        # process/propagate new events/bound updates.

        if violated_clause_id is None:
            self._scale_database()

            violated_clause_id = self._propagate_enqueued()

            if violated_clause_id is None:
                return None
        
        # If at any point, a clause was found to be violated, return the negation
        # of its literals, to be used to build an explanation / asserting clause

        violated_clause = self.clauses_database[violated_clause_id]
        base_explanation_lits = [lit.negated for lit in violated_clause.literals]

        if violated_clause.scope_literal != TRUE_LIT:
            base_explanation_lits.append(violated_clause.scope_literal)
            self._bump_activity(violated_clause_id)

        return ReasonerBaseExplanation(tuple(base_explanation_lits))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _process_pending_clause(self,
        clause_id: SATReasoner.ClauseId,
    ) -> Optional[SATReasoner.ClauseId]:
        """
        Processes a pending (i.e. newly added and not yet processed)
        clause, making no assumption on its status. The only requirement
        is that the clause should not have been processed yet.
        """

        clause = self.clauses_database[clause_id]

        # If the clause only has 1 literal, the processing is simplified
        if clause.watch1 == clause.watch2:

            self._add_watch(clause_id, clause.watch1.negated)

            match self._get_literal_value(clause.watch1):
                # If the literal is known to be true, the clause is satisfied.
                case True:
                    return None 
                # If the literal is known to be false, the clause is violated.
                case False:
                    return self._process_violated_clause(clause_id)
                # If the literal is unbound, it must be set to true
                # (because it's the only literal of the clause).
                case None:
                    self._set_from_unit_propagation(clause.watch1, clause_id)
                    return None
        
        # If the clause has 2 or more literals

        # Update watched literals (to possibly, but not necessarily new ones).
        self._move_watches_front(clause_id)

        # Determine whether a watch should indeed be set on the new 1st
        # and 2nd watched literals (based on the priority values - see `_move_watches_front()`)

        watch1_value = self._get_literal_value(clause.watch1)
        watch2_value = self._get_literal_value(clause.watch2)

        # If the 1st watched literal is true, the clause is satisfied.
        # The state is unchanged and a watch is set. 
        if watch1_value is True:

            self._add_watch(clause_id, clause.watch1.negated)
            self._add_watch(clause_id, clause.watch2.negated)

            return None

        # If the 1st watched literal is false, then the clause is
        # violated, as all the other literals can only be false as
        # well (because of watched literal selection priorities)
        elif watch1_value is False:

            self._add_watch(clause_id, clause.watch1.negated)
            self._add_watch(clause_id, clause.watch2.negated)

            return self._process_violated_clause(clause_id)

        # If the 1st and 2nd watched literal are unbound,
        # the state is unchanged and a watch is set.
        elif watch2_value is None:

            self._add_watch(clause_id, clause.watch1.negated)
            self._add_watch(clause_id, clause.watch2.negated)

            return None

        # If the 1st watched literal is unbound, and the 2nd one is not, the 2nd and all
        # unwatched literals are then necessarily false, because of the priority order,
        # which means the clause can only be unit (only 1st watched literal is unbound).
        # Set up the watch and (attempt to) set the 1st watched literal to true.
        else:

            self._add_watch(clause_id, clause.watch1.negated)
            self._add_watch(clause_id, clause.watch2.negated)

            self._set_from_unit_propagation(clause.watch1, clause_id)

            return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def _process_violated_clause(self,
        clause_id: SATReasoner.ClauseId,
    ) -> Optional[SATReasoner.ClauseId]:
        """
        Processes a clause that is violated. This is done by deactivating
        the clause if possible (i.e. setting its scope literal to False)
        to avoid a conflict. If it's impossible, we are at conflict.

        Returns None if the clause was made deactivated (or if it already was deactivated),
        or clause_id if the clause is known to be active (i.e. cannot be deactivated).
        """
        
        scope_literal = self.clauses_database[clause_id].scope_literal

        match self._get_literal_value(scope_literal):

            case True:
                return clause_id

            case False:
                return None

            case None:
                self._set_from_unit_propagation(scope_literal.negated, clause_id)
                return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate_enqueued(self) -> Optional[SATReasoner.ClauseId]:
        """
        Propagates enqueued "unit information", notably new events resulting
        from the processing of pending clauses. As such, all clauses must be
        integrated to the database before this method is called (i.e. the queue
        of pending clauses must be empty).
            
        If a clause is found to be violated, returns its ID. Otherwise, returns None.

        This method can be seen as the equivalent of the "enqueued" facts
        to propagate in minisat / sat solvers).
        """

        # Loop through yet unprocessed events, accumulated since the last call to this function.
        while self.next_unprocessed_solver_event_index < self.state.num_events_at_current_decision_level:
            ev = self.state._events_trail[self.state.decision_level][self.next_unprocessed_solver_event_index]
            self.next_unprocessed_solver_event_index += 1

            # Select clauses with a literal that is 
            old_watchlists: Dict[BoundVal, Set[SATReasoner.ClauseId]] = \
                self.watchlists._data.get(ev.signed_var, {})
            
            if self.watchlists.has_elements_guarded_by_literals_on(ev.signed_var):
                self.watchlists.remove_all_on(ev.signed_var)

            contradicting_clause_id: Optional[SATReasoner.ClauseId] = None

            for guard_bound_value, clause_ids in old_watchlists.items():
                watched_literal = Lit(ev.signed_var, guard_bound_value)

                for clause_id in clause_ids:

                    # If we haven't found a contradicting clause yet, and the event
                    # made the watched literal become true, we propagate the clause.
                    if (contradicting_clause_id is None
                        and ev.new_bound_value.is_stronger_than(watched_literal.bound_value)
                        and not ev.previous_bound_value.is_stronger_than(watched_literal.bound_value)
                    ):
                        if (not self._propagate_clause(clause_id,
                                                      Lit(ev.signed_var, ev.new_bound_value))
                        ):
                            contradicting_clause_id = clause_id

                    # Otherwise, the watch must be restored.
                    else:
                        to_restore = Lit(ev.signed_var, guard_bound_value)
                        self._add_watch(clause_id, to_restore)

            return contradicting_clause_id

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate_clause(self, 
        clause_id: SATReasoner.ClauseId,
        lit: Lit,
    ) -> bool:
        """
        Propagates a clause that is watching a literal lit that became true.
        lit should be one of the literals watched by the clause.
        If the clause is:
         - pending: reset another watch and return true
         - unit: reset watch, enqueue the implied literal and return true
         - violated: reset watch and return false

        Counter intuitive: this method is only called after removing the watch
        and we are responsible for resetting a valid watch !
        """

        clause = self.clauses_database[clause_id]

        # If the clause only has one literal and it's false, it is violated
        if clause.watch1 == clause.watch2:

            self._add_watch(clause_id, lit)
            return self._process_violated_clause(clause_id) is None

        if lit.entails(clause.watch1.negated):

            self._swap_watch1_and_watch2(clause_id)
        
        # If the 1st watched literal is true, the clause is satisfied.
        # The watch is restored.
        if self.state.is_entailed(clause.watch1):

            self._add_watch(clause_id, clause.watch2.negated)
            return True

        # Search for a true or unbounded literal in the other literals
        # of the clause to set a watch on it.
        for i in range(len(clause.unwatched_indices)):

            cached_unwatched = clause.unwatched(i)
            if not self.state.is_entailed(cached_unwatched.negated):

                self._swap_watch2_and_unwatched_i(clause_id, i)
                self._add_watch(clause_id, cached_unwatched.negated)
                return True
        
        # If all searched for literals were false, then the clause is unit.
        # The watch must be restored and propagation performed.
        self._add_watch(clause_id, clause.watch2.negated)

        cached_watch1 = clause.watch1

        if self.state.is_entailed(cached_watch1):
            return True

        # If the clause is violated, deactivate it if possible
        elif self.state.is_entailed(cached_watch1.negated):
            return self._process_violated_clause(clause_id) is None

        else:
            self._set_from_unit_propagation(cached_watch1, clause_id)
            return True

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _set_from_unit_propagation(self,
        literal: Lit,
        propagating_clause_id: SATReasoner.ClauseId,
    ) -> None:
        """
        Sets the literal to true, as a result of unit propagation.

        We know that no inconsistency will occur (from the invariants of
        unit propagation). However, it might be the case that nothing
        happens if the literal is already known to be absent.

        Also locks the propagating clause, to prevent it
        from being removed from the database as a result of
        database scaling / learned clause forgetting.
        
        Indeed, this is necessary as the clause
        may be needed to provide an explanation.
        """

        is_bound_changed = self.state.set_literal(literal,
                                             Causes.ReasonerInference(id(self),
                                                                      propagating_clause_id))

        if is_bound_changed is True:
            self.locked_clauses_trail[self.state.decision_level].append(propagating_clause_id)
            self.locked_clauses.add(propagating_clause_id)
            # FIXME:
            # if solver.clauses_db.clauses[propagating_clause_id].learned:
            #     lbd = self.lbd(literal, propagating_clause_id, solver)
            #     solver.clauses_db.set_lbd(propagating_clause_id, lbd)

    #############################################################################
    # EXPLANATION
    #############################################################################

    def explain(self,
        explanation_literals: List[Lit],
        literal: Lit,
        inference_cause: Causes.ReasonerInference,
    ) -> None:
        """
        TODO
        """

        _, inference_info = inference_cause

        clause_id = typing.cast(SATReasoner.ClauseId, inference_info)
        self._bump_activity(clause_id)
        clause = self.clauses_database[clause_id]

        # In a normal SAT solver, we would expect the clause to be unit.
        # However, it is not necessarily the case with eager propagation of optionals.
        for lit in clause.literals:
            if not lit.entails(literal):
                explanation_literals.append(lit.negated)

    #############################################################################
    # CLAUSE DATABASE SCALING, ACTIVITIES
    #############################################################################
    
    def _scale_database(self) -> None:
        """
        Scales the size of the clauses database.

        The clauses database has a limited number of slots for learned clauses.
        When all slots are occupied, this function ca:
        - Expand the database with more slots. This occurs if a certain number of
        conflicts occured since last expansion.
        - Remove learned clauses from the database. This typically removes about half
        of the learned clauses, making sure that clauses that are used to explain the 
        current value of the literal are kept ("locked" clauses). The clauses to be
        removed are those whose "activity" is the lowest.
        """
        
        if self.num_allowed_learned_clauses == 0:

            self.num_allowed_learned_clauses = \
                self.num_allowed_learned_clauses_base \
                + int(self.num_fixed_clauses*self.num_allowed_learned_clauses_ratio)

        if self.num_learned_clauses - len(self.locked_clauses) >= self.num_allowed_learned_clauses:
            
            if (self.num_conflicts - self.num_conflicts_at_last_database_expansion
                >= self.num_conflicts_allowed_before_database_expansion
            ):
                self.num_allowed_learned_clauses = \
                    int(self.num_allowed_learned_clauses * self.database_expansion_ratio)

                self.num_conflicts_at_last_database_expansion = self.num_conflicts

                self.num_conflicts_allowed_before_database_expansion = \
                    int(self.num_conflicts_allowed_before_database_expansion 
                        * self.increase_ratio_of_conflicts_before_db_expansion)

            else:

                clauses_to_remove_ids = [
                    clause_id for clause_id, clause in self.clauses_database.items()
                    if clause.learned and clause_id not in self.locked_clauses]

                clauses_to_remove_ids.sort(key=lambda _: self.clauses_database[_].activity)
                clauses_to_remove_ids = clauses_to_remove_ids[:int(len(clauses_to_remove_ids)/2)]

                for clause_id in clauses_to_remove_ids:
                    clause = self.clauses_database[clause_id]

                    if clause.watch1 == clause.watch2:
                        self._remove_watch(clause_id, clause.watch1.negated)

                    else:
                        self._remove_watch(clause_id, clause.watch1.negated)
                        self._remove_watch(clause_id, clause.watch2.negated)

                    self.clauses_database.pop(clause_id)
                    self.num_learned_clauses -= 1

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _bump_activity(self,
        clause_id: SATReasoner.ClauseId,
    ) -> None:
        
        self.clauses_database[clause_id].activity += self.clause_activity_increase

        if self.clauses_database[clause_id].activity > 1e100:

            for clause in self.clauses_database.values():
                clause.activity *= 1e-100

            self.clause_activity_increase *= 1e-100

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _decay_activities(self) -> None:
        self.clause_activity_increase /= self.clause_activity_decay
    
#################################################################################
