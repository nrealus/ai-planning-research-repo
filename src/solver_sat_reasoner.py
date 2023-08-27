from __future__ import annotations

#################################################################################

import typing
from typing import Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, field

from fundamentals import (
    SignedVar, BoundVal, Lit, TRUE_LIT
)

from solver import SolverCauses, SolverConflictInfo, SolverReasoner, Solver

#################################################################################
#################################################################################
#                                   CONTENTS:
# - SAT REASONER
#################################################################################
#################################################################################

class SATReasoner(SolverReasoner):
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
    
    class ClauseId(int):
        """
        Represents the ID of a clause in the database.
        """
        pass

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @dataclass
    class Clause():
        """
        Represents a clause registered in a clause database (i.e. an already known
        or learned clause) for disjunctive/SAT reasoning.
        TODO
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        literals: Tuple[Lit,...]
        """
        The literals of the clause (without the scope literal).

        They are sorted and with only one literal per signed variable
        (i.e. they form a "tight" set of literals)
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        scope_literal: Lit
        """
        A literal that describes whether the clause is "active" or not.

        As such, the full clause is actually: (not scope_literal) v l_1 v ... v l_n

        Note that a clause that is known to be violated but also inactive is not
        considered to be a conflict.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        learned: bool
        """
        Whether the clause is learned or not.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        watch1_index: int = field(init=False)
        """
        Index of the first watched literal.
        """        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        watch2_index: int = field(init=False)
        """
        Index of the second watched literal.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        unwatched_indices: List[int] = field(init=False)
        """
        List of the indices of unwatched literals.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        activity: float = field(init=False)
        """
        TODO
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        def __init__(self,
            literals: Tuple[Lit,...],
            scope_literal: Lit,
            learned: bool,
        ):

            self.literals = literals
            self.scope_literal = scope_literal
            self.learned = learned
            
            self.activity = 0 # FIXME

            len_literals = len(self.literals)
            assert len_literals > 0, "Empty clauses are not allowed in the database."
            
            self.watch1_index = 0
            self.watch2_index = 1 if len_literals > 1 else 0
            self.unwatched_indices = list(range(2, len_literals)) if len_literals > 2 else []

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def swap_watch1_and_watch2(self) -> None:
            self.watch1_index, self.watch2_index = self.watch2_index, self.watch1_index        

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def swap_watch2_and_unwatched_i(self,
            i: int
        ) -> None:
            self.watch2_index, self.unwatched_indices[i] = self.unwatched_indices[i], self.watch2_index

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def __init__(self):

        self._clauses_id_counter: int = 0
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.clauses_database: Dict[SATReasoner.ClauseId, SATReasoner.Clause] = {}
        """
        The clauses database.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        # num_clauses_total: int
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        # num_clauses_fixed: int
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
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.earliest_unprocessed_solver_event_index: int = 0
        """
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.locked_clauses_trail: List[List[SATReasoner.ClauseId]] = [[]]
        """
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.locked_clauses: Set[SATReasoner.ClauseId] = set()
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.watches: Dict[SignedVar, Dict[BoundVal, List[SATReasoner.ClauseId]]] = {}
        """
        Represents watched literals and their watch lists.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

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
        self.clauses_database[clause_id] = SATReasoner.Clause(
            clause_literals,
            scope_literal,
            learned)
        # self.clauses_db.clauses_activities[clause_id] = 0
        return clause_id

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def explain(self,
        explanation_literals_list: List[Lit],
        literal: Lit,
        inference_cause: SolverCauses.ReasonerInference,
        solver: Solver,
    ) -> None:
        """
        TODO
        """

        clause_id = typing.cast(SATReasoner.ClauseId, inference_cause.inference_info)
# FIXME        self._bump_activity(clause_id)
        clause = self.clauses_database[clause_id]

        # In a normal SAT solver, we would expect the clause to be unit.
        # However, it is not necessarily the case with eager propagation of optionals.
        for lit in clause.literals:
            if lit.entails(literal):
                # Comment kept from Aries: "debug_assert_eq!(model.value(l), None) Todo"
                continue
            else:
                explanation_literals_list.append(lit)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_solver_new_set_literal_decision(self,
        solver: Solver
    ) -> None:
        
        self.earliest_unprocessed_solver_event_index = 0
        if len(self.locked_clauses_trail) == solver.dec_level:
            self.locked_clauses_trail.append([])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_solver_backtrack_one_level(self,
        solver: Solver
    ) -> None:

        for locked_clause in self.locked_clauses_trail[solver.dec_level]:
            self.locked_clauses.remove(locked_clause)
        self.locked_clauses_trail[solver.dec_level].clear()
        self.earliest_unprocessed_solver_event_index = len(solver.events_trail[solver.dec_level-1])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def propagate(self,
        solver:Solver,
    )-> Optional[SolverConflictInfo.InvalidBoundUpdate | SolverConflictInfo.ReasonerExplanation]:
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

        if violated_clause_id is None:
# FIXME            self._scale_database()
            violated_clause_id = self._propagate_enqueued(solver)
            if violated_clause_id is None:
                return None
        
        # If at any point, a clause was found to be violated, return the negation
        # of its literals, to be used to build an explanation / asserting clause
        violated_clause = self.clauses_database[violated_clause_id]
        explanation_literals_list = [lit.negation() for lit in violated_clause.literals]
        if violated_clause.scope_literal != TRUE_LIT:
            explanation_literals_list.append(violated_clause.scope_literal)
# FIXME        self._bump_activity(violated_clause_id)
        return SolverConflictInfo.ReasonerExplanation(tuple(explanation_literals_list))

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

        # If the clause only has one literal (i.e. both watched literals are the same)
        if clause.watch1_index == clause.watch2_index:

            lit = clause.literals[clause.watch1_index]
            self._add_watch(clause_id, lit.negation())

            lit_value: Optional[bool] = solver.get_literal_current_value(lit)
            
            # If the literal is entailed, then the clause is satisfied.
            # There is no need to do anything.
            if lit_value is True:
                pass

            # Otherwise, if the literal's negation is entailed (i.e. the literal is false),
            # then the clause is violated (since this is its only literal).
            elif lit_value is False:
                return self._process_violated_clause(clause_id, solver)

            # Otherwise, if the literal's status/value is yet unknown, it must be set
            # to true because it is the only literal in the clause anyway.
            elif lit_value is None:
                self._set_from_unit_propagation(lit, clause_id, solver)
                return None
            
            else:
                assert False

        # If the clause has at least two literals
        
        # Move watches to front: select the two (unbound/non-false) literals that
        # should be watched and place them in the watch1 and watch2 attributes
        # of the clause. (making them the "first" two literals).
        # Note that watch1 and/or watch2 could also stay the same, if they already
        # comply with the priority rules.
        self._move_watches_front(clause_id, solver)

        # We now must determine whether a watch should indeed be set on the
        # new first and second literal (watch1 and watch2). I.e. 

        lit1_value: Optional[bool] = solver.get_literal_current_value(
            clause.literals[clause.watch1_index])
        lit2_value: Optional[bool] = solver.get_literal_current_value(
            clause.literals[clause.watch2_index])

        # If the first literal is entailed, then the clause is satisfied.
        # So we set the watch and leave the state unchanged.
        if lit1_value is True:
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return None

        # Otherwise, if the first literal is false, then (because of how watched literals
        # work / are chose / because of the priority of watched literals selection)
        # the other ones can only be false as well. So the clause is violated.
        elif lit1_value is False:
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return self._process_violated_clause(clause_id, solver)

        # Otherwise, if the second literal's status is unknown yet, we set the
        # watch and leave state unchanged.
        elif lit2_value is None:
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return None

        # Otherwise, the clause can only be unit (the first literal's status is yet
        # unknown, and the second one is false, which means all other literals
        # are false as well, because of watched literals selection priorities).
        else:
            self._process_unit_clause(clause_id, solver)
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

        Returns None if the clause was made deactivated (or if it already was
        deactivated), or clause_id if the clause is known to be active (i.e. cannot be deactivated).
        """
        
        scope_literal = self.clauses_database[clause_id].scope_literal
        scope_literal_value: Optional[bool] = solver.get_literal_current_value(scope_literal)

        if scope_literal_value is True:
            return clause_id

        elif scope_literal_value is False:
            return None
        
        elif scope_literal_value is None:
            self._set_from_unit_propagation(scope_literal.negation(), clause_id, solver)
            return None

        else:
            assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _process_unit_clause(self,
        clause_id: SATReasoner.ClauseId,
        solver: Solver,
    ) -> None:
        """
        Processes a clause that is unit (i.e. all its literals except one are known
        to be false, i.e. its first watched literal (watch1) is unbound / has None value).
        """

        clause = self.clauses_database[clause_id]

        if clause.watch1_index == clause.watch2_index:

            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())

            self._set_from_unit_propagation(clause.literals[clause.watch1_index], clause_id, solver)

        else:

            # Set up watch, the first literal must be undefined and the others violated
            self._move_watches_front(clause_id, solver)

            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())

            self._set_from_unit_propagation(clause.literals[clause.watch1_index], clause_id, solver)

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

        # self.earliest_unprocessed_solver_event_index = min(
        #     self.earliest_unprocessed_solver_event_index,
        #     len(solver.events_trail[solver.dec_level]))
        # NOTE: The code above was placed here to "synchronize" the earliest unprocessed solver event index,
        # making sure its almost equal to the index of the last event + 1. Indeed, the earliest unprocessed
        # solver event index is only updated in two ways: when getting to a new decision level, it is set to 0
        # (i.e. to the first event of the decision, i.e. the "decision itself"), and when backtracking (one level)
        # it is set to the number of events in the decision level we backtracked to, which corresponds to the 
        # index of the *next* event that will be posted in this decision level. However, there is also a possible
        # partial backtrack (in the same decision level) that can happen during explanation refining in the main
        # solver. As it is part of one same decision level, the events reverted there do not trigger
        # on_solver_backtrack_one_level, which means the earliest unprocessed solver event index is not
        # updated and "still" points to events that have been removed...
        # So the reasoning behind the code above was to remove this problem. *HOWEVER...* This isn't actually a
        # problem ! Indeed, this partial backtrack happens during EXPLANATION... which is part of conflict analysis
        # and is followed right away by "true" backtracking to an earlier decision level. As such, it means that
        # the earliest unprocessed solver event index will be necessarily updated to a correct value before it
        # needs to be used again ! So this problem was actually a false alarm.

        while self.earliest_unprocessed_solver_event_index < len(solver.events_trail[solver.dec_level]):
            ev = solver.events_trail[solver.dec_level][self.earliest_unprocessed_solver_event_index]
            self.earliest_unprocessed_solver_event_index += 1

            working_watches = self.watches.get(ev.signed_var, {})
            if ev.signed_var in self.watches:
                self.watches.pop(ev.signed_var)

            contradicting_clause_id: Optional[SATReasoner.ClauseId] = None

            for guard_bound_value, clauses_id_list in working_watches.items():
                watched_literal = Lit(ev.signed_var, guard_bound_value)
                for clause_id in clauses_id_list:

                    if (contradicting_clause_id is None
                        and ev.new_bound_value.is_stronger_than(watched_literal.bound_value)
                        and not ev.previous_bound_value.is_stronger_than(watched_literal.bound_value)
                    ):
                        if not self._propagate_clause(clause_id, Lit(ev.signed_var, ev.new_bound_value), solver):
                            contradicting_clause_id = clause_id
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

        # If the clause only has one literal and it's false, the clause is violated
        if clause.watch1_index == clause.watch2_index:
            self._add_watch(clause_id, lit)
            return self._process_violated_clause(clause_id, solver) is None

        # If the first watched literal is false, then only the second watched literal
        # could be the one that became true.
        # To maintain the priority order of watched literals, we swap them.
        if lit.entails(clause.literals[clause.watch1_index].negation()):
            clause.swap_watch1_and_watch2()
        
        if solver.is_literal_entailed(clause.literals[clause.watch1_index]):
            # Clause satisfied, restore the watch and exit
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return True

        # Look for replacement for lits[1]: a literal that is not false.
        # We look for them in the unwatched literals.
        for i in range(len(clause.unwatched_indices)):
            lit_neg = clause.literals[clause.unwatched_indices[i]].negation()
            if not solver.is_literal_entailed(lit_neg):
                clause.swap_watch2_and_unwatched_i(i)
                self._add_watch(clause_id, lit_neg)
                return True
        
        # No replacement found, clause is unit, restore watch and propagate
        self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())

        watch1 = clause.literals[clause.watch1_index]

        # Clause is true
        if solver.is_literal_entailed(watch1):
            return True

        # The clause is violated, deactivate it if possible
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

        is_bound_changed = solver.set_bound_value(
            literal.signed_var,
            literal.bound_value,
            SolverCauses.ReasonerInference(self, propagating_clause_id))

        if is_bound_changed is True:
            self.locked_clauses_trail[solver.dec_level].append(propagating_clause_id)
            self.locked_clauses.add(propagating_clause_id)
            # FIXME:
            # if solver.clauses_db.clauses[propagating_clause_id].learned:
            #     lbd = self.lbd(literal, propagating_clause_id, solver)
            #     solver.clauses_db.set_lbd(propagating_clause_id, lbd)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _move_watches_front(self,
        clause_id: SATReasoner.ClauseId,
        solver: Solver,
    ) -> None:
        """
        Selects the two literals that should be watched and move them
        to the first 2 literals of the clause.

        After the method completion, watch1 will be the element
        with highest priority and watch2 the one with the second highest
        priority. Order of the other elements is undefined.

        Priority is defined as follows:
            - True literals
            - Undefined literals
            - False literals, prioritizing those with the highest decision level
            - Leftmost literal in the original clause
              (to avoid swapping two literals with the same priority)
        """

        def priority_of_lit(lit: Lit) -> int:
            val = solver.get_literal_current_value(lit)
            if val is True:
                return 1000 # FIXME: should be max int
            elif val is None:
                return 999  # FIXME: should be max int - 1
            elif val is False:
                first_impl_ev_index = solver.get_index_of_first_event_implying_literal(lit.negation())
                if first_impl_ev_index is None:
                    return 0
                (_p1, _p2) = first_impl_ev_index
                return _p1+_p2
            else:
                assert False
        
        clause = self.clauses_database[clause_id]
        
        lvl0 = priority_of_lit(clause.literals[clause.watch1_index])
        lvl1 = priority_of_lit(clause.literals[clause.watch2_index])

        if lvl1 > lvl0:
            lvl0, lvl1 = lvl1, lvl0
            clause.swap_watch1_and_watch2()

        for i in range(len(clause.unwatched_indices)):
            lvl = priority_of_lit(clause.literals[clause.unwatched_indices[i]])
            if lvl > lvl1:
                lvl1 = lvl
                clause.swap_watch2_and_unwatched_i(i)
                if lvl > lvl0:
                    lvl1 = lvl0
                    lvl0 = lvl
                    clause.swap_watch1_and_watch2()

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_watch(self,
        clause_id: SATReasoner.ClauseId,
        literal: Lit,
    ) -> None:
        self.watches.setdefault(literal.signed_var, {}).setdefault(literal.bound_value, []).append(clause_id)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _bump_activity(self,
        clause_id: SATReasoner.ClauseId,
    ) -> None:
        # TODO
        raise NotImplemented

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _scale_database(self) -> None:
        # TODO
        raise NotImplemented

#################################################################################
