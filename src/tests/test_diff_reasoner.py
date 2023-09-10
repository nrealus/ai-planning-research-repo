from __future__ import annotations

#################################################################################

import unittest
from typing import Optional, Tuple

from src.fundamentals import TRUE_LIT, BoundVal, Lit, SignedVar, Var
from src.solver import Causes, InvalidBoundUpdateInfo, ReasonerBaseExplanation, Solver
from src.solver_api import (_flatten_scope_to_lits_conj,
                            _get_or_make_new_scope_lit_from_scope_as_lits_conj,
                            _get_or_make_tautology_of_scope_from_scope_lit,
                            add_new_non_optional_variable,
                            add_new_optional_variable,
                            add_new_presence_variable)
from src.solver_diff_reasoner import DiffReasoner

#################################################################################

class TestDiffReasonerBasics(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_active_edge(self, 
        src: Var,
        tgt: Var,
        weight: int,
        solver: Solver,
        diff_reasoner: DiffReasoner
    ) -> Lit:
        psrc, ptgt = solver.presence_literals[src], solver.presence_literals[tgt]
        valid_edge = _get_or_make_new_scope_lit_from_scope_as_lits_conj(
            (psrc,ptgt),
            #_flatten_scope_to_lits_conj(({ psrc.signed_var: psrc.bound_value,
            #                               ptgt.signed_var: ptgt.bound_value },
            #                             ()),
            #                            True, solver), 
            solver)
        active_edge = _get_or_make_tautology_of_scope_from_scope_lit(valid_edge, solver)
        diff_reasoner.add_reified_difference_constraint(active_edge, src, tgt, weight, solver)
        return active_edge

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_inactive_edge(self,
        src: Var,
        tgt: Var,
        weight: int,
        solver: Solver,
        diff_reasoner: DiffReasoner
    ) -> Lit:
        psrc, ptgt = solver.presence_literals[src], solver.presence_literals[tgt]
        valid_edge = _get_or_make_new_scope_lit_from_scope_as_lits_conj(
            (psrc,ptgt),
            #_flatten_scope_to_lits_conj(({ psrc.signed_var: psrc.bound_value,
            #                               ptgt.signed_var: ptgt.bound_value },
            #                             ()),
            #                            True, solver), 
            solver)
        active_edge = Lit.geq(add_new_optional_variable((0, 1), True, valid_edge, solver), 1)
        diff_reasoner.add_reified_difference_constraint(active_edge, src, tgt, weight, solver)
        return active_edge

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_delay(self, var1, var2, delay, solver, diff_reasoner):
        self._add_active_edge(var2, var1, -delay, solver, diff_reasoner)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _mark_edge_active(self, edge: Lit, solver: Solver):
        return solver.set_bound_value(edge.signed_var, edge.bound_value, Causes.Decision())

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation(self):

        solver = Solver()
        diff_reasoner = DiffReasoner()

        A = add_new_non_optional_variable((0,10), True, solver)
        B = add_new_non_optional_variable((0,10), True, solver)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.bound_values[SignedVar.minus(A)], solver.bound_values[SignedVar.plus(A)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.bound_values[SignedVar.minus(B)], solver.bound_values[SignedVar.plus(B)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        check_bounds(0, 10, 0, 10)

        solver.set_bound_value(SignedVar.plus(A), BoundVal(3), Causes.Decision())

        self._add_active_edge(A, B, 5, solver, diff_reasoner)

        diff_reasoner.propagate(solver)

        check_bounds(0, 3, 0, 8)

        solver.set_bound_value(SignedVar.plus(A), BoundVal(1), Causes.Decision())

        diff_reasoner.propagate(solver)

        check_bounds(0, 1, 0, 6)

        x = self._add_inactive_edge(A, B, 3, solver, diff_reasoner)
        self._mark_edge_active(x, solver)

        diff_reasoner.propagate(solver)

        check_bounds(0, 1, 0, 4)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_backtracking(self):

        solver = Solver()
        diff_reasoner = DiffReasoner()

        A = add_new_non_optional_variable((0,10), True, solver)
        B = add_new_non_optional_variable((0,10), True, solver)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.bound_values[SignedVar.minus(A)], solver.bound_values[SignedVar.plus(A)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.bound_values[SignedVar.minus(B)], solver.bound_values[SignedVar.plus(B)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        check_bounds(0, 10, 0, 10)

        solver.set_bound_value(SignedVar(A, True), BoundVal(1), Causes.Decision())

        diff_reasoner.propagate(solver)

        check_bounds(0, 1, 0, 10)
        
        solver.increment_decision_level((diff_reasoner,))

        self._add_active_edge(A, B, 5, solver, diff_reasoner)

        diff_reasoner.propagate(solver)

        check_bounds(0, 1, 0, 6)

        solver.increment_decision_level((diff_reasoner,))

        self._add_active_edge(B, A, -6, solver, diff_reasoner)

        self.assertIsInstance(diff_reasoner.propagate(solver), InvalidBoundUpdateInfo)

        solver.backtrack_to_decision_level(solver.decision_level-1,
                                           (diff_reasoner,))
        check_bounds(0, 1, 0, 6)
 
        solver.backtrack_to_decision_level(solver.decision_level-1,
                                           (diff_reasoner,))
        check_bounds(0, 1, 0, 10)

        x = self._add_inactive_edge(A, B, 5, solver, diff_reasoner)
        self._mark_edge_active(x, solver)

        diff_reasoner.propagate(solver)

        check_bounds(0, 1, 0, 6)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_explanation(self):

        solver = Solver()
        diff_reasoner = DiffReasoner()

        A = add_new_non_optional_variable((0,10), True, solver)
        B = add_new_non_optional_variable((0,10), True, solver)
        C = add_new_non_optional_variable((0,10), True, solver)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.bound_values[SignedVar.minus(A)], solver.bound_values[SignedVar.plus(A)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.bound_values[SignedVar.minus(B)], solver.bound_values[SignedVar.plus(B)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        diff_reasoner.propagate(solver)

        solver.increment_decision_level((diff_reasoner,))

        x = self._add_inactive_edge(A, A, -1, solver, diff_reasoner)
        self._mark_edge_active(x, solver)

        self.assertIsInstance(diff_reasoner.propagate(solver), ReasonerBaseExplanation)

        solver.backtrack_to_decision_level(solver.decision_level-1,
                                           (diff_reasoner,))

        solver.increment_decision_level((diff_reasoner,))

        self._add_active_edge(A, B, 2, solver, diff_reasoner)
        self._add_active_edge(B, A, -3, solver, diff_reasoner)

        self.assertIsInstance(diff_reasoner.propagate(solver), ReasonerBaseExplanation)
        
        solver.backtrack_to_decision_level(solver.decision_level-1,
                                           (diff_reasoner,))

        solver.increment_decision_level((diff_reasoner,))

        self._add_active_edge(A, B, 2, solver, diff_reasoner)
        self._add_active_edge(B, A, -2, solver, diff_reasoner)

        diff_reasoner.propagate(solver)

        self._add_active_edge(B, A, -3, solver, diff_reasoner)

        self.assertIsInstance(diff_reasoner.propagate(solver), ReasonerBaseExplanation)
        
        solver.backtrack_to_decision_level(solver.decision_level-1,
                                           (diff_reasoner,))

        solver.increment_decision_level((diff_reasoner,))

        self._add_active_edge(A, B, 2, solver, diff_reasoner)
        self._add_active_edge(B, C, 2, solver, diff_reasoner)
        self._add_active_edge(C, A, -4, solver, diff_reasoner)

        diff_reasoner.propagate(solver)

        self._add_active_edge(C, A, -5, solver, diff_reasoner)

        self.assertIsInstance(diff_reasoner.propagate(solver), ReasonerBaseExplanation)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_optionals(self):

        solver = Solver()
        diff_reasoner = DiffReasoner()

        PA = Lit.geq(add_new_non_optional_variable((0, 1), True, solver), BoundVal(1))
        A = add_new_optional_variable((0,10), True, PA, solver)

        PB = Lit.geq(add_new_presence_variable(PA, solver), BoundVal(1))
        B = add_new_optional_variable((0,10), True, PB, solver)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.bound_values[SignedVar.minus(A)], solver.bound_values[SignedVar.plus(A)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.bound_values[SignedVar.minus(B)], solver.bound_values[SignedVar.plus(B)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self._add_delay(A, B, 0, solver, diff_reasoner)

        diff_reasoner.propagate(solver)

        solver.set_bound_value(SignedVar.minus(B), BoundVal(-1), Causes.Decision())
        solver.set_bound_value(SignedVar.plus(B), BoundVal(9), Causes.Decision())

        diff_reasoner.propagate(solver)

        check_bounds(0, 10, 1, 9)

        solver.set_bound_value(SignedVar(A, False), BoundVal(-2), Causes.Decision())

        diff_reasoner.propagate(solver)

        check_bounds(2, 10, 2, 9)

        solver.set_bound_value(PB.signed_var, PB.bound_value, Causes.Decision())

        diff_reasoner.propagate(solver)

        check_bounds(2, 9, 2, 9)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_optional_chain(self):

        solver = Solver()
        diff_reasoner = DiffReasoner()

        vars = []
        context = TRUE_LIT

        for i in range(10):
            prez = Lit.geq(add_new_presence_variable(context, solver), 1)
            var = add_new_optional_variable((0, 20), True, prez, solver)
            if i > 0:
                self._add_delay(vars[i-1][1], var, 1, solver, diff_reasoner)
            vars.append((prez, var))
            context = prez
        
        diff_reasoner.propagate(solver)

        for i, (_, var) in enumerate(vars):
            print((-solver.bound_values[SignedVar.minus(var)], solver.bound_values[SignedVar.plus(var)]))
            self.assertEqual((-solver.bound_values[SignedVar.minus(var)], solver.bound_values[SignedVar.plus(var)]), 
                             (i, 20))
        
        self.assertEqual(solver.set_bound_value(SignedVar.plus(vars[5][1]), BoundVal(4), Causes.Decision()),
                         True)

        diff_reasoner.propagate(solver)

        for i, (_, var) in enumerate(vars):
            if i <= 4:
                self.assertEqual((-solver.bound_values[SignedVar.minus(var)], solver.bound_values[SignedVar.plus(var)]), 
                                (i, 20))
            else:
                self.assertTrue(solver.is_entailed(solver.presence_literals[var].negation()))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#################################################################################
