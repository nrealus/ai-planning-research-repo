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
        TODO
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
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        # num_clauses_total: int
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        # num_clauses_fixed: int
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.pending_clauses_info: List[Tuple[SATReasoner.ClauseId, Optional[Lit]]] = []
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
        self.locked_clauses_trail: List[List[SATReasoner.ClauseId]] = [[]]
        """
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.locked_clauses: Set[SATReasoner.ClauseId] = set()
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.watches: Dict[SignedVar, Dict[BoundVal, List[SATReasoner.ClauseId]]] = {}
        """
        Represents watched literals and their watch lists.

        A watched literal is stored "in two parts": as a dictionary key (its
        signed variable) and ... TODO/FIXME
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_new_fixed_clause_with_scope(self,
        clause_literals: Tuple[Lit,...],
        scope_literal: Lit,
    ):

        clause_id = self._register_new_clause(clause_literals, scope_literal, False)
        self.pending_clauses_info.insert(0, (clause_id, None))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_new_learned_clause(self,
        asserting_clause_literals: Tuple[Lit,...],
        asserted_literal: Optional[Lit],
    ) -> None:
        """
        TODO
        """

        assert asserted_literal is None or asserted_literal in asserting_clause_literals

        clause_id = self._register_new_clause(asserting_clause_literals, TRUE_LIT, True)
        self.pending_clauses_info.insert(0, (clause_id, asserted_literal))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _register_new_clause(self,
        clause_literals: Tuple[Lit,...],
        scope_literal: Lit,
        learned: bool,
    ) -> SATReasoner.ClauseId:
        """
        Register a new clause to the clauses database.

        Args:
            clause (Clause): The clause to register.

        Returns:
            ClausesDB.ClauseID: The ID given to the added clause it in the database.
        
        Side effects:
            Updates the collection of clauses of the clauses database.
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
        # FIXME/TODO: bump the activity of any clause used in an explanation
#        clause = self.clauses_db.clauses[clause_id]
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

        violated_clause_id: Optional[SATReasoner.ClauseId] = None
        
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
        clause = self.clauses_database[violated_clause_id]
        explanation_literals_list = [lit.negation() for lit in clause.literals]
        if clause.scope_literal != TRUE_LIT:
            explanation_literals_list.append(clause.scope_literal)
        # FIXME/TODO: bump the activity of clause (violated_clause_id)
        return SolverConflictInfo.ReasonerExplanation(tuple(explanation_literals_list))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _process_arbitrary_clause(self,
        clause_id: SATReasoner.ClauseId,
        solver: Solver,
    ) -> Optional[SATReasoner.ClauseId]:
        """
        Process a newly added/registered clause, making no assumption on its status.
        
        The only requirement is that the clause should not have been processed yet.
        """

        clause = self.clauses_database[clause_id]

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

        # We now must determine whether a watch should indeed be set on the
        # new first and second literal (watch1 and watch2). I.e. 

        lit1_value: Optional[bool] = solver.get_literal_current_value(
            clause.literals[clause.watch1_index])
        lit2_value: Optional[bool] = solver.get_literal_current_value(
            clause.literals[clause.watch2_index])

        # If the first literal is entailed, then the clause is satisfied.
        # So we set the watch and leave the state unchanged.
        if lit1_value is True:
#            self._set_watch_on_first_literals(clause_id, solver)
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return None

        # Otherwise, if the first literal is false, then (because of how watched literals
        # work / are chose / because of the priority of watched literals selection)
        # the other ones can only be false as well. So the clause is violated.
        elif lit1_value is False:
#            self._set_watch_on_first_literals(clause_id, solver)
            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
            return self._process_violated_clause(clause_id, solver)

        # Otherwise, if the second literal's status is unknown yet, we set the
        # watch and leave state unchanged.
        elif lit2_value is None:
#            self._set_watch_on_first_literals(clause_id, solver)
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
        Process a clause that is violated. This means that the clause will be
        deactivated if possible. Otherwise, it means, we are in a conflict state.

        Returns:
            None: If we are *not* in a conflict (i.e. has been deactivated or was already inactive)

            Solver.ClausesDB.ClauseId: If we are in a conflict state (the clause could not be
        deactivated), the same violated clause id passed as parameter to this method.
        """
        
        scope_literal = self.clauses_database[clause_id].scope_literal
        scope_literal_value: Optional[bool] = solver.get_literal_current_value(scope_literal)

        # If the clause is active and violated, it means we have a conflict.
        if scope_literal_value is True:
            return clause_id

        # Otherwise, if the clause is inactive, it (this violated
        # clause) isn't actually a conflict.
        elif scope_literal_value is False:
            return None
        
        # Otherwise, if the clause is undefined: deactivate the clause to avoid a conflict
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
        to be false, i.e. its first watched literal (watch1) is unbound / has None value)
        """
        clause = self.clauses_database[clause_id]

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

#            lit = clause.literals[clause.watch1_index]

            self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
            self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
#            self._set_watch_on_first_literals(clause_id, solver)
#            self._set_from_unit_propagation(lit, clause_id, solver)
            self._set_from_unit_propagation(clause.literals[clause.watch1_index], clause_id, solver)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate_enqueued(self,
        solver: Solver,
    ) -> Optional[SATReasoner.ClauseId]:
        """
        Returns the id of a violated clause, if there is a conflict.
        Otherwise, returns None.

        When this method is called, all clauses must be fully integrated in
        the database (not just registered).
        In other words, solver.pending_clauses_info must be empty.
        """

#        working_watches: Dict[SignedVar, List[Tuple[BoundValue, Solver.ClausesDB.ClauseId]]] = {}
        working_watches: Dict[SignedVar, Dict[BoundVal, List[SATReasoner.ClauseId]]] = {}

        # We loop through new "(unit) information" (events / literals / bound updates) resulting
        # from processing of pending clauses to learn (+initial/fixed clauses). It can be seen as
        # the equivalent of the "enqueued" facts to propagate in minisat / sat solvers.
        while self.earliest_unprocessed_solver_event_index < len(solver.events_trail[solver.dec_level]):
            ev = solver.events_trail[solver.dec_level][self.earliest_unprocessed_solver_event_index]
            self.earliest_unprocessed_solver_event_index += 1

            new_lit = Lit(ev.signed_var, ev.new_bound_value)

            # Remove all watches (on new_lit) and place them in working_watches
            self._move_watches_to(new_lit, working_watches)

            # When propagation encounters a contradicting clause, it will be put here.
            contradicting_clause_id: Optional[SATReasoner.ClauseId] = None

            for signed_var in working_watches:
#                for (guard_bound_value, clause_id) in working_watches[signed_var]:
                watch_lists_dict = working_watches[signed_var]
                for guard_bound_value in watch_lists_dict:
                    watched_literal = Lit(signed_var, guard_bound_value)

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
                                to_restore = Lit(signed_var, guard_bound_value)
    #                            self.watches.setdefault(to_restore.signed_var, []).append((to_restore.bound_value, clause_id))
                                self._add_watch(clause_id, to_restore)

            if contradicting_clause_id is not None:
                return contradicting_clause_id

        return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate_clause(self, 
        clause_id: SATReasoner.ClauseId,
        lit: Lit,
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

        clause = self.clauses_database[clause_id]

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
            clause.swap_watch1_and_watch2()
        
        if solver.is_literal_entailed(watch1):
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
        literal: Lit,
        propagating_clause_id: SATReasoner.ClauseId,
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
            SolverCauses.ReasonerInference(self, propagating_clause_id)
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

        # def value_of_lit(lit: Literal) -> Optional[bool]:
        #     lit_neg = lit.negation()
        #     if solver.is_literal_entailed(lit):
        #         return True
        #     elif solver.is_literal_entailed(lit_neg):
        #         return False
        #     else:
        #         return None

        def priority_of_lit(lit: Lit) -> int:
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
                clause.swap_watch1_and_watch2()
                if lvl > lvl0:
                    lvl1 = lvl0
                    lvl0 = lvl1
                    clause.swap_watch1_and_watch2()

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#    def _set_watch_on_first_literals(self,
#        clause_id: SATReasoner.ClauseId,
#        solver: Solver,
#    ) -> None:
#        """
#        Set the watch on the first two literals of the clause (without any check).
#        One should typically call move_watches_front on the clause beforehand.
#        """
#        clause = self.clauses_database[clause_id]
#
#        self._add_watch(clause_id, clause.literals[clause.watch1_index].negation())
#        self._add_watch(clause_id, clause.literals[clause.watch2_index].negation())
#
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _move_watches_to(self,
        literal: Lit,
#        out_watches: Dict[SignedVar, List[Tuple[BoundValue, Solver.ClausesDB.ClauseId]]],
        out_watches: Dict[SignedVar, Dict[BoundVal, List[SATReasoner.ClauseId]]],
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
        clause_id: SATReasoner.ClauseId,
        literal: Lit,
    ) -> None:
        self.watches.setdefault(literal.signed_var, {}).setdefault(literal.bound_value, []).append(clause_id)

#################################################################################
