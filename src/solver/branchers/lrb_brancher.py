"""
TODO
"""

#################################################################################

from __future__ import annotations

#################################################################################

import heapq
from typing import Callable, Dict, List, Set, Tuple

from src.fundamentals import Lit, Var
from src.solver.common import Causes, Decisions, SetGuardedByLiterals
from src.solver.branchers.brancher import Brancher
from src.solver.solver_state import SolverState

#################################################################################
# BRANCHER
#################################################################################

class LRBBrancher(Brancher):
    """
    TODO
    """

    def __init__(self):
        
        self.choosable_decision_vars: Set[Var] = set()

        self.pending_vars_prio_queue: List[Tuple[int, Var]] = []    # priority: ema (exponential moving average)
        heapq.heapify(self.pending_vars_prio_queue)

        self._prio_queue_helper_dict: Dict[Var, int] = {}

        self.processed_pending_vars_trail: List[List[Var]] = [[]]
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        # self.unprocessed_vars: Set[Var] = set()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.watches_presence_vars: SetGuardedByLiterals[Var] = SetGuardedByLiterals()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.next_unprocessed_solver_event_index: int = 0

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.num_conflicts: int = 0

        self.num_conflicts_at_var_assignment: Dict[Var, int] = {}       # i.e. "assigned" in LRB paper

        self.num_conflicts_since_var_assignment: Dict[Var, int] = {}    # i.e. "participated" in LRB paper

        self.var_assignments_trail: List[List[Var]] = [[]]

        
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    # i.e. import vars
    def initialize(self,
        state: SolverState,
    ) -> None:
        
        #self.unprocessed_vars = state._vars[True].copy()

        for var in state._vars[True].copy():

            self.choosable_decision_vars.add(var)

            # remember, when the presence literal of a var becomes true,
            # the var must be enqueued
            self.watches_presence_vars.add(var, state.presence_literal_of(var))

            # if presence literal is already true, enqueue the var immediately
            if state.is_entailed(state.presence_literal_of(var)):
                heapq.heappush(self.pending_vars_prio_queue, (0, var))
                self._prio_queue_helper_dict[var] = 0
                self.num_conflicts_at_var_assignment[var] = 0
                self.num_conflicts_since_var_assignment[var] = 0
        
        # self.on_after_assignments_at_current_decision_level(state) # ??????        

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_after_assignments_at_current_decision_level(self,
        state: SolverState,
    ) -> None:
        """
        TODO
        """
        n = len(self.var_assignments_trail)
        if state.decision_level > n:
            for _ in range(n):
                self.var_assignments_trail.append([])

        while self.next_unprocessed_solver_event_index < state.num_events_at_current_decision_level:
            ev = state._events_trail[state.decision_level][self.next_unprocessed_solver_event_index]
            self.next_unprocessed_solver_event_index += 1

            for prez_var in self.watches_presence_vars.elements_guarded_by(Lit(ev.signed_var,
                                                                                  ev.new_bound_value)):
                if prez_var not in self._prio_queue_helper_dict:
                    heapq.heappush(self.pending_vars_prio_queue, (0, prez_var))
                    self._prio_queue_helper_dict[prez_var] = 0
                    

            var = ev.signed_var.var

            if var in self.choosable_decision_vars:

                self.var_assignments_trail[state.decision_level].append(var)
                self.num_conflicts_at_var_assignment[var] = self.num_conflicts
                self.num_conflicts_since_var_assignment[var] = 0
                # TODO/FIXME: this all assumed that the variable is binary / can only have 1 or 2 values
                # i.e. is set on the first event concerning it.... TODO/FIXME

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_before_backtracking(self,
        target_decision_level: int,
        state: SolverState,
    ) -> None:
        """
        TODO
        """
        dec_lvl = state.decision_level

        while dec_lvl > target_decision_level:

            for v in self.var_assignments_trail[dec_lvl]:

                interval = self.num_conflicts - self.num_conflicts_at_var_assignment[v]
                participated = self.num_conflicts_since_var_assignment[v]
                self.num_conflicts_at_var_assignment.pop(v)
                
                if interval != 0:
                    lr = participated / interval
                    self._lit_update_activity(Lit.geq(v, 1), lr, 0.05, interval)

            self.var_assignments_trail[dec_lvl].clear()

            for var in self.processed_pending_vars_trail[dec_lvl]:

                if var not in self._prio_queue_helper_dict:
                    heapq.heappush(self.pending_vars_prio_queue, (0, var))
                    self._prio_queue_helper_dict[var] = 0

            self.processed_pending_vars_trail[dec_lvl].clear()

            dec_lvl -= 1

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_after_conflict_analysis(self,
        asserting_clause_literals: Tuple[Lit,...],
        explain_function: Callable[[List[Lit], Lit, Causes.ReasonerInference], None],
        state: SolverState,
    ) -> None:
        """
        TODO
        """

        self.num_conflicts += 1
        # TODO

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def choose_next_decision(self,
        num_conflicts: int,
        state: SolverState,
    ) -> Decisions.AnyDecision:
        """
        TODO
        """
        pass
