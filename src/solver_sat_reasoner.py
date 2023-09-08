from __future__ import annotations

#################################################################################

import typing
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from fundamentals import TRUE_LIT, BoundVal, Lit, SignedVar
from solver import Causes, Reasoner, ReasonerRawExplanation, Solver

MAX_INT = 2**64

#################################################################################
#################################################################################
#                                   CONTENTS:
# - SAT REASONER
#   - CLAUSES & CLAUSES IDs
#   - CLAUSE ADDITION / REGISTRATION
#   - WATCHES (WATCHED LITERALS & WATCHLISTS)
#   - MAIN SOLVER DECISION LEVEL INCREASE & DECREASE CALLBACKS
#   - PROPAGATION
#   - EXPLANATION
#   - CLAUSE DATABASE SCALING, ACTIVITIES
#################################################################################
#################################################################################

class SATReasoner(Reasoner):
    """
    Also called "Disjunctive Reasoner". It acts as a SAT solver. It
    maintains the database of clauses and performs unit propagation.

    In essence, for each clause in the database, we look for distinct 
    literals that are not falsified by the current domains:

        - If all literals are false, the clause is violated and a conflict is 
        reported, which will cause the search to backtrack
     
        - If all but one literal `l` are false, then the clause is unit and `l` is
        enforced/set
        
        - Otherwise, two non-false literals are selected and added to a watch list.
        Once one of these literal is set, the clause will be reevaluated
    """
    
    #############################################################################
    # CLAUSE ID, CLAUSE DATA 
    #############################################################################
    
    @dataclass
    class Clause():
        """Contains the data of a clause registered in the clause database."""
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        literals: Tuple[Lit,...]
        """
        The literals of the clause (without the scope literal).

        They are sorted and with only one literal per signed variable
        (i.e. they form a "tight" set of literals)
        """

        scope_literal: Lit
        """
        A literal that describes whether the clause is "active" or not.

        As such, the full clause is actually: (not scope_literal) v l_1 v ... v l_n

        Note that a clause that is known to be violated but also inactive is not
        considered to be a conflict.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        learned: bool
        """Whether the clause is learned or not."""

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        watch1_index: int = field(init=False)
        """Index of the first watched literal."""

        watch2_index: int = field(init=False)
        """Index of the second watched literal."""

        unwatched_indices: List[int] = field(init=False)
        """List of the indices of unwatched literals."""

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
            assert len_literals > 0, "Empty clauses are not allowed in the database."
            
            self.watch1_index = 0
            self.watch2_index = 1 if len_literals > 1 else 0
            self.unwatched_indices = list(range(2, len_literals)) if len_literals > 2 else []

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class ClauseId(int):
        """
        Represents the ID of a clause in the database.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
 
    def __init__(self):

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
        All locked clauses (at all decision levels).
        A clause that is marked as locked cannot be removed from the clause database
        as part of database rescaling / forgetting of learned clauses. Marking a
        clause as locked is necessary when that clause may be needed for explanation
        mechanisms.
        """

        self.locked_clauses_trail: List[List[SATReasoner.ClauseId]] = [[]]
        """
        Trail of locked clauses. Outer list index: decision level.
        Inner list content: clauses locked while at that decision level.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.watches: Dict[SignedVar, Dict[BoundVal, List[SATReasoner.ClauseId]]] = {}
        """
        Represents watched literals and their watchlists.

        A watched literal [svar <= u] 's watchlist (of clauses) is represented as:
        { svar : { u : [clause1_id, clause2_id, ...] }}
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.pending_clauses_info: List[Tuple[SATReasoner.ClauseId, Optional[Lit]]] = []
        """
        Stores clauses that have been recorded to the database, but not processed yet.

        The first element of the tuple is the ID of the clause to propagate.
        The second element is either None or a literal that is entailed by
        the clause at the current decision level. This literal MUST be set
        to true, with this clause as its cause, even if the clause is not unit.
        This situation might happen when the clause was learned from a conflict
        involving eager propagation of optional variables.
        """

        self.next_unprocessed_solver_event_index: int = 0
        """
        The index of the next unprocessed (i.e. not yet propagated) event in the
        main solver's events trail (in the current decision level).
        """
        
    #############################################################################
    # CLAUSE ADDITION / REGISTRATION
    #############################################################################

    def add_new_fixed_clause_with_scope(self,
        clause_literals: Tuple[Lit,...],
        scope_literal: Lit,
    ) -> None:
        """
        Adds a new non-learned clause to the clauses database and to the pending clauses queue.

        Returns the ID given to the clause in the clauses database.
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
        Adds a new learned clause to the clauses database and to the pending clauses queue.
        
        Returns the ID given to the clause in the clauses database.
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

        Returns the ID given to the clause in the clause database.
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
        """
        Swaps the 1st and 2nd watched literals.
        """
        clause = self.clauses_database[clause_id]
        clause.watch1_index, clause.watch2_index = clause.watch2_index, clause.watch1_index

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
 
    def _swap_watch2_and_unwatched_i(self,
        clause_id: SATReasoner.ClauseId,
        i: int
    ) -> None:
        """
        Swaps the 2nd watched literal with the i-th unwatched literal.
        """
        clause = self.clauses_database[clause_id]
        clause.watch2_index, clause.unwatched_indices[i] = clause.unwatched_indices[i], clause.watch2_index

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
            
    def _move_watches_front(self,
        clause_id: SATReasoner.ClauseId,
        solver: Solver,
    ) -> None:
        """
        Selects the two (unbound) literals that should be watched and make them
        the watched literals of the clause.

        After the method completion, the 1st watched literal will have the
        highest priority and the 2nd watched literal will have the second highest
        priority. The order of the other (unwatched) literals is undefined.

        The priority rule ordering (from highest to lowest):
            - True literals
            - Undefined literals
            - False literals, prioritizing those with the highest decision level
            - Leftmost literal in the original clause
            (to avoid swapping two literals with the same priority)
        """

        def priority_of_lit(lit: Lit) -> int:
            match solver.get_literal_value(lit):
                case True:
                    return MAX_INT
                case None:
                    return MAX_INT-1
                case False:
                    first_impl_ev = solver.get_first_event_implying_literal(lit.negation())
                    if first_impl_ev is None:
                        return 0
                    return first_impl_ev.index[0]+first_impl_ev.index[1]

        clause = self.clauses_database[clause_id]

        lvl0 = priority_of_lit(clause.literals[clause.watch1_index])
        lvl1 = priority_of_lit(clause.literals[clause.watch2_index])

        if lvl1 > lvl0:
            lvl0, lvl1 = lvl1, lvl0
            self._swap_watch1_and_watch2(clause_id)

        for i in range(len(clause.unwatched_indices)):
            lvl = priority_of_lit(clause.literals[clause.unwatched_indices[i]])

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
        self.watches.setdefault(literal.signed_var, {}).setdefault(literal.bound_value, []).append(clause_id)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _remove_watch(self,
        clause_id: SATReasoner.ClauseId,
        literal: Lit,
    ) -> None:
        self.watches[literal.signed_var][literal.bound_value].remove(clause_id)

    #############################################################################
    # MAIN SOLVER DECISION LEVEL INCREASE & DECREASE CALLBACKS
    #############################################################################

    def on_solver_increment_decision_level(self,
        solver: Solver
    ) -> None:
        
        self.next_unprocessed_solver_event_index = 0

        if len(self.locked_clauses_trail) == solver.decision_level:
            self.locked_clauses_trail.append([])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_solver_backtrack_one_level(self,
        solver: Solver
    ) -> None:

        for locked_clause in reversed(self.locked_clauses_trail[solver.decision_level]):
            self.locked_clauses.remove(locked_clause)
        self.locked_clauses_trail[solver.decision_level].clear()

        self.next_unprocessed_solver_event_index = len(solver.events_trail[solver.decision_level-1])

    #############################################################################
    # PROPAGATION
    #############################################################################

    def propagate(self,
        solver:Solver,
    ) -> Optional[ReasonerRawExplanation]:
        """
        Main propagation method of the SAT reasoner.
        Performs unit propagation (aka boolean constraint propagation).

        First, processes all pending clauses (i.e. clauses that were added to the
        database since last propagation but weren't processed yet), and sets their
        asserted literal to True (if they have one).

        If none of these clauses is found to be violated, any new ("enqueued")
        "unit information" resulting from the processing of pending clauses is
        propagated.

        If at any point, either during pending clauses processing or propagation,
        a clause is found to be violated, the negation of its literals is returned
        as a reasoner explanation for the main solver to be refined.
        """

        violated_clause_id: Optional[SATReasoner.ClauseId] = None

        # Process pending clauses

        while self.pending_clauses_info:
            (clause_id, asserted_literal) = self.pending_clauses_info.pop()

            violated_clause_id = self._process_pending_clause(clause_id, solver)
            if violated_clause_id is not None:
                break

            if asserted_literal is not None:
                if not solver.is_literal_entailed(asserted_literal):
                    self._set_from_unit_propagation(asserted_literal, clause_id, solver)

        # If no violated clause was detected above, process/propagate new events/bound updates.

        if violated_clause_id is None:
            self._scale_database()
            violated_clause_id = self._propagate_enqueued(solver)
            if violated_clause_id is None:
                return None
        
        # If at any point, a clause was found to be violated, return the negation
        # of its literals, to be used to build an explanation / asserting clause

        violated_clause = self.clauses_database[violated_clause_id]
        explanation_literals = [lit.negation() for lit in violated_clause.literals]

        if violated_clause.scope_literal != TRUE_LIT:
            explanation_literals.append(violated_clause.scope_literal)
            self._bump_activity(violated_clause_id)

        return ReasonerRawExplanation(tuple(explanation_literals))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _process_pending_clause(self,
        clause_id: SATReasoner.ClauseId,
        solver: Solver,
    ) -> Optional[SATReasoner.ClauseId]:
        """
        Processes a pending (i.e. newly added and not yet processed) clause,
        making no assumption on its status. The only requirement is that the clause
        should not have been processed yet.
        """

        clause = self.clauses_database[clause_id]

        # If the clause only has 1 literal, the processing is simplified
        if clause.watch1_index == clause.watch2_index:

            lit = clause.literals[clause.watch1_index]
            self._add_watch(clause_id, lit.negation())

            match solver.get_literal_value(lit):
                # If the literal is known to be true, the clause is satisfied.
                case True:
                    return None 
                # If the literal is known to be false, the clause is violated.
                case False:
                    return self._process_violated_clause(clause_id, solver)
                # If the literal is unbound, it must be set to true
                # (because it's the only literal of the clause).
                case None:
                    self._set_from_unit_propagation(lit, clause_id, solver)
                    return None
        
        # If the clause has 2 or more literals

        # Update watched literals (to possibly, but not necessarily new ones).
        self._move_watches_front(clause_id, solver)

        # Determine whether a watch should indeed be set on the new 1st
        # and 2nd watched literals (based on the priority values - see `_move_watches_front()`)

        lit1_value: Optional[bool] = solver.get_literal_value(
            clause.literals[clause.watch1_index])
        lit2_value: Optional[bool] = solver.get_literal_value(
            clause.literals[clause.watch2_index])

        # If the 1st watched literal is true, the clause is satisfied.
        # The state is unchanged and a watch is set. 
        if lit1_value is True:
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return None

        # If the 1st watched literal is false, then the clause is violated, as all the
        # other literals can only be false as well (because of watched literal selection priorities)
        elif lit1_value is False:
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return self._process_violated_clause(clause_id, solver)

        # If the 1st and 2nd watched literal are unbound, the state is unchanged and a watch is set.
        elif lit2_value is None:
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return None

        # If the 1st watched literal is unbound, and the 2nd one is not, the 2nd and all
        # unwatched literals are then necessarily false, because of the priority order,
        # which means the clause can only be unit (only 1st watched literal is unbound).
        # Set up the watch and (attempt to) set the 1st watched literal to true.
        else:
#            self._move_watches_front(clause_id, solver)
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            self._set_from_unit_propagation(clause.literals[clause.watch1_index], clause_id, solver)
            # self._process_unit_clause(clause_id, solver)
            return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def _process_violated_clause(self,
        clause_id: SATReasoner.ClauseId,
        solver: Solver,
    ) -> Optional[SATReasoner.ClauseId]:
        """
        Processes a clause that is violated. This is done by deactivating the clause
        if possible (i.e. setting its scope literal to False) to avoid a conflict.
        If it's impossible, we are at conflict.

        Returns None if the clause was made deactivated (or if it already was deactivated),
        or clause_id if the clause is known to be active (i.e. cannot be deactivated).
        """
        
        scope_literal = self.clauses_database[clause_id].scope_literal
        match solver.get_literal_value(scope_literal):
            case True:
                return clause_id
            case False:
                return None
            case None:
                self._set_from_unit_propagation(scope_literal.negation(), clause_id, solver)
                return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate_enqueued(self,
        solver: Solver,
    ) -> Optional[SATReasoner.ClauseId]:
        """
        Propagates "enqueued" "unit information", notably new events resulting from
        the processing of pending clauses. As such, all clauses must be integrated
        to the database before this method is called (i.e. the queue of pending
        clauses must be empty).
            
        If a clause is found to be violated, returns its ID. Otherwise, returns None.

        This method can be seen as the equivalent of the "enqueued" facts to propagate in minisat / sat solvers).
        """

        working_watches: Dict[BoundVal, List[SATReasoner.ClauseId]] = {}

        # Loop through yet unprocessed events, accumulated since the last call to this function.
        while self.next_unprocessed_solver_event_index < len(solver.events_trail[solver.decision_level]):
            ev = solver.events_trail[solver.decision_level][self.next_unprocessed_solver_event_index]
            self.next_unprocessed_solver_event_index += 1

            # Select clauses with a literal that is 
            working_watches = self.watches.get(ev.signed_var, {})
            if ev.signed_var in self.watches:
                self.watches.pop(ev.signed_var)

            contradicting_clause_id: Optional[SATReasoner.ClauseId] = None

            for guard_bound_value, clauses_id_list in working_watches.items():
                watched_literal = Lit(ev.signed_var, guard_bound_value)
                for clause_id in clauses_id_list:

                    # If we haven't found a contradicting clause yet, and the event
                    # made the watched literal become true, we propagate the clause.
                    if (contradicting_clause_id is None
                        and ev.new_bound_value.is_stronger_than(watched_literal.bound_value)
                        and not ev.previous_bound_value.is_stronger_than(watched_literal.bound_value)
                    ):
                        if not self._propagate_clause(clause_id,
                                                      Lit(ev.signed_var, ev.new_bound_value),
                                                      solver):
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
        solver: Solver,
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
        if clause.watch1_index == clause.watch2_index:
            self._add_watch(clause_id, lit)
            return self._process_violated_clause(clause_id, solver) is None

        if lit.entails(clause.literals[clause.watch1_index].negation()):
            self._swap_watch1_and_watch2(clause_id)
        
        # If the 1st watched literal is true, the clause is satisfied. The watch is restored.
        if solver.is_literal_entailed(clause.literals[clause.watch1_index]):
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return True

        # Search for a true or unbounded literal in the other literals of the clause to set a watch on it.
        for i in range(len(clause.unwatched_indices)):
            lit_neg = clause.literals[clause.unwatched_indices[i]].negation()
            if not solver.is_literal_entailed(lit_neg):
                self._swap_watch2_and_unwatched_i(clause_id, i)
                self._add_watch(clause_id, lit_neg)
                return True
        
        # If all searched for literals were false, then the clause is unit.
        # The watch must be restored and propagation performed.
        self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())

        watch1 = clause.literals[clause.watch1_index]

        if solver.is_literal_entailed(watch1):
            return True

        # If the clause is violated, deactivate it if possible
        elif solver.is_literal_entailed(watch1.negation()):
            return self._process_violated_clause(clause_id, solver) is None

        else:
            self._set_from_unit_propagation(watch1, clause_id, solver)
            return True

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _set_from_unit_propagation(self,
        literal: Lit,
        propagating_clause_id: SATReasoner.ClauseId,
        solver: Solver,
    ) -> None:
        """
        Sets the literal to true, as a result of unit propagation.   #NOTE: in Aries it says "false" (????)

        We know that no inconsistency will occur (from the invariants of unit
        propagation). However, it might be the case that nothing happens if the
        literal is already known to be absent.

        Also locks the propagating clause, to prevent it from being removed
        from the database as a result of database scaling / learned clause forgetting.
        Indeed, this is necessary as the clause may be needed to provide an explanation.
        """

        is_bound_changed = solver.set_bound_value(literal.signed_var,
                                                  literal.bound_value,
                                                  Causes.ReasonerInference(self, propagating_clause_id))

        if is_bound_changed is True:
            self.locked_clauses_trail[solver.decision_level].append(propagating_clause_id)
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
        inference_cause_data: Tuple[Reasoner, object],
        solver: Solver,
    ) -> None:
        """
        TODO
        """

        _, inference_info = inference_cause_data

        clause_id = typing.cast(SATReasoner.ClauseId, inference_info)
        self._bump_activity(clause_id)
        clause = self.clauses_database[clause_id]

        # In a normal SAT solver, we would expect the clause to be unit.
        # However, it is not necessarily the case with eager propagation of optionals.
        for lit in clause.literals:
            if not lit.entails(literal):
                explanation_literals.append(lit)

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
            self.num_allowed_learned_clauses = (self.num_allowed_learned_clauses_base
                + int(self.num_fixed_clauses*self.num_allowed_learned_clauses_ratio))

        if self.num_learned_clauses - len(self.locked_clauses) >= self.num_allowed_learned_clauses:
            
            if (self.num_conflicts - self.num_conflicts_at_last_database_expansion
                >= self.num_conflicts_allowed_before_database_expansion
            ):
                self.num_allowed_learned_clauses = int(self.num_allowed_learned_clauses*self.database_expansion_ratio)
                self.num_conflicts_at_last_database_expansion = self.num_conflicts
                self.num_conflicts_allowed_before_database_expansion = int(
                    self.num_conflicts_allowed_before_database_expansion*self.increase_ratio_of_conflicts_before_db_expansion)

            else:

                clauses_to_remove_ids = [clause_id for clause_id, clause in self.clauses_database.items()
                    if clause.learned and clause_id not in self.locked_clauses]
                clauses_to_remove_ids.sort(key=lambda _: self.clauses_database[_].activity)
                clauses_to_remove_ids = clauses_to_remove_ids[:int(len(clauses_to_remove_ids)/2)]

                for clause_id in clauses_to_remove_ids:
                    clause = self.clauses_database[clause_id]
                    if clause.watch1_index == clause.watch2_index:
                        self._remove_watch(clause_id, clause.literals[clause.watch1_index].negation())
                    else:
                        self._remove_watch(clause_id, clause.literals[clause.watch1_index].negation())
                        self._remove_watch(clause_id, clause.literals[clause.watch2_index].negation())
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
