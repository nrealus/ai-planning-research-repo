from __future__ import annotations

#################################################################################

import typing
from typing import Tuple, Dict, List, Set, Optional, Union

from fundamentals import *
from solver import *

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
    # CLAUSES DATABASE 
    #############################################################################
    
#    @dataclass
    class ClausesDB():
        """
        A database of clauses, maintained by the solver.

        TODO
        """

        class ClauseId(int):
            """
            Represents the ID of a clause in the database.
            """
            pass

        def __init__(self):

            self._clauses_id_counter: int = 0

            self.clauses: Dict[SATReasoner.ClausesDB.ClauseId, Clause] = {}
            # num_clauses_total: int
            # num_clauses_fixed: int
            self.clauses_activities: Dict[SATReasoner.ClausesDB.ClauseId, float] = {}

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def register_new_clause(self,
            clause: Clause,
        ) -> SATReasoner.ClausesDB.ClauseId:
            """
            Register a new clause to the clauses database.

            Args:
                clause (Clause): The clause to register.

            Returns:
                ClausesDB.ClauseID: The ID given to the added clause it in the database.
            
            Side effects:
                Updates the collection of clauses of the clauses database.
            """

            clause_id = SATReasoner.ClausesDB.ClauseId(self._clauses_id_counter)
            self._clauses_id_counter += 1
            self.clauses[clause_id] = clause
            # self.clauses_db.clauses_activities[clause_id] = 0
            return clause_id

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_clause_fixed(self,
        clause: Clause,
    ):

        assert not clause.learned

        clause_id = self.clauses_db.register_new_clause(clause)
        self.pending_clauses_info.insert(0, (clause_id, None))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_clause_learned(self,
        asserting_clause: Clause,
        asserted_literal: Optional[Literal],
    ) -> None:
        """
        TODO
        """

        assert asserting_clause.learned

        assert asserted_literal is None or asserted_literal in asserting_clause.literals

        clause_id = self.clauses_db.register_new_clause(asserting_clause)
        self.pending_clauses_info.insert(0, (clause_id, asserted_literal))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def __init__(self):

        self.clauses_db: SATReasoner.ClausesDB = SATReasoner.ClausesDB()
        """
        The clauses database.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.pending_clauses_info: List[Tuple[SATReasoner.ClausesDB.ClauseId, Optional[Literal]]] = []
        """
        Stores clauses that have been recorded, but not propagated yet.

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
        self.locked_clauses_trail: List[List[SATReasoner.ClausesDB.ClauseId]] = [[]]
        """
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.locked_clauses: Set[SATReasoner.ClausesDB.ClauseId] = set()
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#        self.watches: Dict[SignedVar, List[Tuple[BoundValue, Solver.ClausesDB.ClauseId]]] = {}
        self.watches: Dict[SignedVar, Dict[BoundValue, List[SATReasoner.ClausesDB.ClauseId]]] = {}
        """
        Represents watched literals and their watch lists.

        A watched literal is stored "in two parts": as a dictionary key (its
        signed variable) and ... TODO/FIXME
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def explain(self,
        explanation_literals_list: List[Literal],
        literal: Literal,
        inference_cause: SolverCause.ReasonerInference,
        solver: Solver,
    ) -> None:
        """
        TODO
        """

        clause_id = typing.cast(SATReasoner.ClausesDB.ClauseId, inference_cause.inference_info)
        # FIXME/TODO: bump the activity of any clause used in an explanation
        clause = self.clauses_db.clauses[clause_id]

        # In a normal SAT solver, we would expect the clause to be unit.
        # However, it is not necessarily the case with eager propagation of optionals.
        for lit in clause.literals:
            if lit.entails(literal):
                # Comment kept from Aries: "debug_assert_eq!(model.value(l), None) Todo"
                continue
            else:
                explanation_literals_list.append(lit)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_solver_new_decision(self,
        solver: Solver
    ) -> None:
        
        self.earliest_unprocessed_solver_event_index = 0
        if len(self.locked_clauses_trail) == solver.dec_level:
            self.locked_clauses_trail.append([])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_solver_backtrack_one_level(self,
        solver: Solver
    ) -> None:

        self.earliest_unprocessed_solver_event_index = len(solver.events_trail[solver.dec_level])
        for locked_clause in self.locked_clauses_trail[solver.dec_level]:
            self.locked_clauses.remove(locked_clause)
        self.locked_clauses_trail[solver.dec_level].clear()

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def propagate(self,
        solver:Solver,
    )-> Optional[Union[SolverConflictInfo.InvalidBoundUpdate, SolverConflictInfo.ReasonerExplanation]]:
        """
        Propagate method of the SAT reasoner.

        Performs unit propagation (aka boolean constraint propagation).
        """

        violated_clause_id: Optional[SATReasoner.ClausesDB.ClauseId] = None
        
        # Process all clauses newly added/registered since last propagation.
        # The asserted literal of a clause needs to be set to true, with that
        # clause as it cause, even if it (the clause) isn't unit.
        while self.pending_clauses_info:
            (clause_id, asserted_literal) = self.pending_clauses_info.pop()

            violated_clause_id = self._process_arbitrary_clause(clause_id, solver)   # NOTE: possibly move this to clausesDB ?
            if violated_clause_id is not None:
                break

            if asserted_literal is not None:
                if not solver.is_literal_entailed(asserted_literal):
                    self._set_from_unit_propagation(asserted_literal, clause_id, solver)

        # If no violated clause was detected during processing of pending clauses
        if violated_clause_id is None:
    #        self.scale_database();
            violated_clause_id = self._propagate_enqueued(solver)

        # If, at last, there is no violated clause detected, then propagation is successful.
        if violated_clause_id is None:
            return None
        
        # However, if a violated clause is detected at any point (including during
        # the loop above), return the negation of its literals. They will be used
        # to build an explanation / asserting clause.
        clause_id = self.clauses_db.clauses[violated_clause_id]
        explanation_literals_list = [lit.negation() for lit in clause_id.literals]
        if clause_id.scope != TrueLiteral:
            explanation_literals_list.append(clause_id.scope)
        # FIXME/TODO: bump the activity of clause (violated_clause_id)
        return SolverConflictInfo.ReasonerExplanation(tuple(explanation_literals_list))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _process_arbitrary_clause(self,
        clause_id: SATReasoner.ClausesDB.ClauseId,
        solver: Solver,
    ) -> Optional[SATReasoner.ClausesDB.ClauseId]:
        """
        Process a newly added/registered clause, making no assumption on its status.
        
        The only requirement is that the clause should not have been processed yet.
        """

        clause = self.clauses_db.clauses[clause_id]

# NOTE: useless in practice
#        # If the clause is empty, it is always violated
#        if clause.watch1_index is None:
#            return self._process_violated_clause(clause_id, solver)

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

        clause = self.clauses_db.clauses[clause_id]

        # We now must determine whether a watch should indeed be set on the
        # new first and second literal (watch1 and watch2). I.e. 

        lit0_value: Optional[bool] = solver.get_literal_current_value(
            clause.literals[clause.watch1_index])
        lit1_value: Optional[bool] = solver.get_literal_current_value(
            clause.literals[clause.watch2_index])

        # If the first literal is entailed, then the clause is satisfied.
        # So we set the watch and leave the state unchanged.
        if lit0_value is True:
            self._set_watch_on_first_literals(clause_id, solver)
            return None

        # Otherwise, if the first literal is false, then (because of how watched literals
        # work / are chose / because of the priority of watched literals selection)
        # the other ones can only be false as well. So the clause is violated.
        elif lit0_value is False:
            self._set_watch_on_first_literals(clause_id, solver)
            return self._process_violated_clause(clause_id, solver)

        # Otherwise, if the second literal's status is unknown yet, we set the
        # watch and leave state unchanged.
        elif lit1_value is None:
            self._set_watch_on_first_literals(clause_id, solver)
            return None

        # Otherwise, the clause can only be unit (the first literal's status is yet
        # unknown, and the second one is false, which means all other literals
        # are false as well, because of watched literals selection priorities).
        else:
            self._process_unit_clause(clause_id, solver)
            return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def _process_violated_clause(self,
        clause_id: SATReasoner.ClausesDB.ClauseId,
        solver: Solver,
    ) -> Optional[SATReasoner.ClausesDB.ClauseId]:
        """
        Process a clause that is violated. This means that the clause will be
        deactivated if possible. Otherwise, it means, we are in a conflict state.

        Returns:
            None: If we are *not* in a conflict (i.e. has been deactivated or was already inactive)

            Solver.ClausesDB.ClauseId: If we are in a conflict state (the clause could not be
        deactivated), the same violated clause id passed as parameter to this method.
        """
        
        is_clause_active_literal = self.clauses_db.clauses[clause_id].scope
        is_clause_active_literal_value: Optional[bool] = solver.get_literal_current_value(is_clause_active_literal)

        # If the clause is active and violated, it means we have a conflict.
        if is_clause_active_literal_value is True:
            return clause_id

        # Otherwise, if the clause is inactive, it (this violated
        # clause) isn't actually a conflict.
        elif is_clause_active_literal_value is False:
            return None
        
        # Otherwise, if the clause is undefined: deactivate the clause to avoid a conflict
        elif is_clause_active_literal_value is None:
            self._set_from_unit_propagation(is_clause_active_literal.negation(), clause_id, solver)
            return None

        else:
            assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _process_unit_clause(self,
        clause_id: SATReasoner.ClausesDB.ClauseId,
        solver: Solver,
    ) -> None:
        """
        Processes a clause that is unit (i.e. all its literals except one are known
        to be false, i.e. its first watched literal (watch1) is unbound / has None value)
        """
        clause = self.clauses_db.clauses[clause_id]

        # FIXME: it's weird... in the only function where this function is used, there is already
        # a special case for literals that only have one literal. So why would this be needed ?
        # Need to look at the aries code again, to see what this really is about.
        if clause.watch1_index == clause.watch2_index:

            lit = clause.literals[clause.watch1_index]
            # Set watch on this only literal
            self._add_watch(clause_id, lit.negation())
            self._set_from_unit_propagation(lit, clause_id, solver)

        # FIXME: so... should we just simply use this code block directly in process_arbitrary_clause,
        # instead of calling this function ? (it happens only once at the end, too)
        else:

            # Set up watch, the first literal must be undefined and the others violated
            self._move_watches_front(clause_id, solver)
            clause = self.clauses_db.clauses[clause_id]

            lit = clause.literals[clause.watch1_index]

            self._set_watch_on_first_literals(clause_id, solver)
            self._set_from_unit_propagation(lit, clause_id, solver)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate_enqueued(self,
        solver: Solver,
    ) -> Optional[SATReasoner.ClausesDB.ClauseId]:
        """
        Returns the id of a violated clause, if there is a conflict.
        Otherwise, returns None.

        When this method is called, all clauses must be fully integrated in
        the database (not just registered).
        In other words, solver.pending_clauses_info must be empty.
        """

#        working_watches: Dict[SignedVar, List[Tuple[BoundValue, Solver.ClausesDB.ClauseId]]] = {}
        working_watches: Dict[SignedVar, Dict[BoundValue, List[SATReasoner.ClausesDB.ClauseId]]] = {}

        # We loop through new "(unit) information" (events / literals / bound updates) resulting
        # from processing of pending clauses to learn (+initial/fixed clauses). It can be seen as
        # the equivalent of the "enqueued" facts to propagate in minisat / sat solvers.
        while self.earliest_unprocessed_solver_event_index < len(solver.events_trail[solver.dec_level]):
            ev = solver.events_trail[solver.dec_level][self.earliest_unprocessed_solver_event_index]
            self.earliest_unprocessed_solver_event_index += 1

            new_lit = Literal(ev.signed_var, ev.new_bound_value)

            # Remove all watches (on new_lit) and place them in working_watches
            self._move_watches_to(new_lit, working_watches)

            # When propagation encounters a contradicting clause, it will be put here.
            contradicting_clause_id: Optional[SATReasoner.ClausesDB.ClauseId] = None

            for signed_var in working_watches:
#                for (guard_bound_value, clause_id) in working_watches[signed_var]:
                watch_lists_dict = working_watches[signed_var]
                for guard_bound_value in watch_lists_dict:
                    watched_literal = Literal(signed_var, guard_bound_value)

                    for clause_id in watch_lists_dict[guard_bound_value]:
#                        clause = solver.clauses_db.clauses[clause_id]
                        # We propagate unless:
                        # - We found a contradicting clause earlier
                        # - The event does not make the watched literal true
                        #   (meaning it was already true before this event)
#                        if (clause.watch1 is None   # FIXME WTF ?
                        if (ev.new_bound_value.is_stronger_than(watched_literal.bound_value)
                            and not ev.previous_bound_value.is_stronger_than(watched_literal.bound_value)
                        ):
                            if not self._propagate_clause(clause_id, new_lit, solver):
                                # Propagation found a contradiction
                                contradicting_clause_id = clause_id
                            else:
                                # We encountered a contradicting clause or the event
                                # is not triggering, we need to restore the watch
                                to_restore = Literal(signed_var, guard_bound_value)
    #                            self.watches.setdefault(to_restore.signed_var, []).append((to_restore.bound_value, clause_id))
                                self.watches.setdefault(to_restore.signed_var, {}).setdefault(to_restore.bound_value, []).append(clause_id)

            if contradicting_clause_id is not None:
                return contradicting_clause_id

        return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate_clause(self, 
        clause_id: SATReasoner.ClausesDB.ClauseId,
        lit: Literal,
        solver: Solver,
    ) -> bool:
        """
        Propagate a clause that is watching a literal lit that became true.
        lit should be one of the literals watched by the clause.
        If the clause is:
         - pending: reset another watch and return true
         - unit: reset watch, enqueue the implied literal and return true
         - violated: reset watch and return false

        Counter intuitive: this method is only called after removing the watch
        and we are responsible for resetting a valid watch !
        """

        clause = self.clauses_db.clauses[clause_id]

# FIXME: something missing in condition... check aries code
        # If the clause only has one literal and it's false, the clause is violated
        if clause.watch1_index == clause.watch2_index:
#            self.watches.setdefault(lit.signed_var, []).append((lit.bound_value, clause_id))
            self.watches.setdefault(lit.signed_var, {}).setdefault(lit.bound_value, []).append(clause_id)
            return self._process_violated_clause(clause_id, solver) is None

        # If the first watched literal is false, then only the second watched literal
        # could be the one that became true.
        # To maintain the priority order of watched literals, we swap them.
        watch1 = clause.literals[clause.watch1_index]
        watch1_neg = watch1.negation()
        if lit.entails(watch1_neg):
            clause.watch1_index, clause.watch2_index = clause.watch2_index, clause.watch1_index
        
        if solver.is_literal_entailed(watch1):
            # Clause satisfied, restore the watch and exit
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return True

        # Look for replacement for lits[1]: a literal that is not false.
        # We look for them in the unwatched literals.
        for i in range(len(clause.unwatched_indices)):
            lit_neg = clause.literals[clause.unwatched_indices[i]].negation()
            if not solver.is_literal_entailed(lit_neg):
                clause.watch2_index, clause.unwatched_indices[i] = clause.unwatched_indices[i], clause.watch2_index
                self._add_watch(clause_id, lit_neg)
                return True
        
        # No replacement found, clause is unit, restore watch and propagate
        self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
        first_lit = clause.literals[clause.watch1_index]
        if solver.is_literal_entailed(first_lit):
            # Clause is true
            return True
        elif solver.is_literal_entailed(first_lit.negation()):
            # The clause is violated, deactivate it if possible
            return self._process_violated_clause(clause_id, solver) is None
        else:
            self._set_from_unit_propagation(first_lit, clause_id, solver)
            return True

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _set_from_unit_propagation(self,
        literal: Literal,
        propagating_clause_id: SATReasoner.ClausesDB.ClauseId,
        solver: Solver,
    ) -> None:
        """
        Sets the literal to true.   #NOTE: in Aries it says "false" (????)

        We know that no inconsistency will occur (from the invariants of unit
        propagation). However, it might be the case that nothing happens if the
        literal is already known to be absent.
        """

        is_bound_changed = solver.set_bound_value(
            literal.signed_var,
            literal.bound_value,
            SolverCause.ReasonerInference(self, propagating_clause_id)
        )
        if isinstance(is_bound_changed, bool) and is_bound_changed:
            # Lock clause to ensure it will not be removed from the database.
            # This is necessary as we might need this clause to provide an explanation.
            self.locked_clauses_trail[solver.dec_level].append(propagating_clause_id)
            self.locked_clauses.add(propagating_clause_id)
            # if solver.clauses_db.clauses[propagating_clause_id].learned:
            #     lbd = self.lbd(literal, propagating_clause_id, solver)
            #     solver.clauses_db.set_lbd(propagating_clause_id, lbd)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _move_watches_front(self,
        clause_id: SATReasoner.ClausesDB.ClauseId,
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

        # def value_of_lit(lit: Literal) -> Optional[bool]:
        #     lit_neg = lit.negation()
        #     if solver.is_literal_entailed(lit):
        #         return True
        #     elif solver.is_literal_entailed(lit_neg):
        #         return False
        #     else:
        #         return None

        def priority_of_lit(lit: Literal) -> int:
        #    val = value_of_lit(lit)
            val = solver.get_literal_current_value(lit)
            if val is True:
                return 1000 # FIXME: should be max int
            elif val is None:
                return 999  # FIXME: should be max int - 1
            elif val is False:
                (_p1, _p2) = solver.get_index_of_first_event_implying_literal(lit.negation())
                return _p1+_p2+1 if _p1 != 0 else 0
            else:
                assert False
        
        clause = self.clauses_db.clauses[clause_id]
        
        lvl0 = priority_of_lit(clause.literals[clause.watch1_index])
        lvl1 = priority_of_lit(clause.literals[clause.watch2_index])

        if lvl1 > lvl0:
            lvl0, lvl1 = lvl1, lvl0
            clause.watch1_index, clause.watch2_index = clause.watch2_index, clause.watch1_index

        for i in range(len(clause.unwatched_indices)):
            lvl = priority_of_lit(clause.literals[clause.unwatched_indices[i]])
            if lvl > lvl1:
                lvl1 = lvl
                clause.watch2_index, clause.unwatched_indices[i] = clause.unwatched_indices[i], clause.watch2_index
                if lvl > lvl0:
                    lvl1 = lvl0
                    lvl0 = lvl1
                    clause.watch1_index, clause.watch2_index = clause.watch2_index, clause.watch1_index

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _set_watch_on_first_literals(self,
        clause_id: SATReasoner.ClausesDB.ClauseId,
        solver: Solver,
    ) -> None:
        """
        Set the watch on the first two literals of the clause (without any check).
        One should typically call move_watches_front on the clause beforehand.
        """
        clause = self.clauses_db.clauses[clause_id]

        self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
        self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _move_watches_to(self,
        literal: Literal,
#        out_watches: Dict[SignedVar, List[Tuple[BoundValue, Solver.ClausesDB.ClauseId]]],
        out_watches: Dict[SignedVar, Dict[BoundValue, List[SATReasoner.ClausesDB.ClauseId]]],
    ) -> None:
        """

        """
        if not literal.signed_var in self.watches:
            pass #return
        else:
#            watch = self.watches[literal.signed_var]
#            i = 0
#            while i < len(watch):
#                (guard_bound_value, _) = watch[i]
#                if literal.bound_value.is_stronger_than(guard_bound_value):
#                    watch.pop(i)
#                    out_watches.setdefault(literal.signed_var, []).append(watch[i])
#                else:
#                    i += 1
            watch = self.watches[literal.signed_var]
            for guard_bound_value in watch:
                if literal.bound_value.is_stronger_than(guard_bound_value):
                    watch.pop(guard_bound_value)
                    _list = out_watches.setdefault(literal.signed_var, {}).setdefault(guard_bound_value, [])
                    for clause_id in watch[guard_bound_value]:
                        if not clause_id in _list:
                            _list.append(clause_id)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_watch(self,
        clause_id: SATReasoner.ClausesDB.ClauseId,
        literal: Literal,
    ):
        self.watches.setdefault(literal.signed_var, {}).setdefault(literal.bound_value, []).append(clause_id)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#################################################################################
