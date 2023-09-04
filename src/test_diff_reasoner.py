from __future__ import annotations

#################################################################################

from typing import Optional, Tuple

from fundamentals import (
    Var, SignedVar, BoundVal, Lit, TRUE_LIT,
    ConstraintExpression,
    tighten_literals,
)

from solver import SolverCauses, SolverDecisions, SolverConflictInfo, Solver
from solver_diff_reasoner import DiffReasoner

from solver_api import (
    add_new_non_optional_variable,
    add_new_optional_variable,
    _flatten_conjunctive_scope_into_conjunctive_scope_literals,
    _get_or_make_new_scope_literal_from_conjunctive_scope_literals,
    _get_tautology_of_scope
)

import unittest

#################################################################################

class TestDiffReasoner(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_edge(self, src: Var, tgt: Var, weight: int, solver: Solver, diff_reasoner: DiffReasoner):
        psrc, ptgt = solver.vars_presence_literals[src], solver.vars_presence_literals[tgt]
        valid_edge = _get_or_make_new_scope_literal_from_conjunctive_scope_literals(
            _flatten_conjunctive_scope_into_conjunctive_scope_literals(
                ({ psrc.signed_var: psrc.bound_value,
                    ptgt.signed_var: ptgt.bound_value },
                ()),
                True, solver), solver)
        active_edge = _get_tautology_of_scope(valid_edge, solver)
        diff_reasoner.add_reified_difference_constraint(active_edge, src, tgt, weight, solver)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _add_inactive_edge(self, src: Var, tgt: Var, weight: int, solver: Solver, diff_reasoner: DiffReasoner) -> Lit:
        psrc, ptgt = solver.vars_presence_literals[src], solver.vars_presence_literals[tgt]
        valid_edge = _get_or_make_new_scope_literal_from_conjunctive_scope_literals(
            _flatten_conjunctive_scope_into_conjunctive_scope_literals(
                ({ psrc.signed_var: psrc.bound_value,
                    ptgt.signed_var: ptgt.bound_value },
                ()),
                True, solver), solver)
        active_edge = Lit.geq(add_new_optional_variable(solver, (0, 1), True, valid_edge), 1)
        diff_reasoner.add_reified_difference_constraint(active_edge, src, tgt, weight, solver)
        return active_edge

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _mark_edge_active(self, edge: Lit, solver: Solver):
        return solver.set_bound_value(edge.signed_var, edge.bound_value, SolverCauses.Decision())

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation(self):
        pass
        solver = Solver()
        diff_reasoner = DiffReasoner()

        A = add_new_non_optional_variable(solver, (0,10), True)
        B = add_new_non_optional_variable(solver, (0,10), True)
        
        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.bound_values[SignedVar(A, False)], solver.bound_values[SignedVar(A, True)]), (a_lb, a_ub))
            self.assertEqual((-solver.bound_values[SignedVar(B, False)], solver.bound_values[SignedVar(B, True)]), (b_lb, b_ub))

        check_bounds(0, 10, 0, 10)

        solver.set_bound_value(SignedVar(A, True), BoundVal(3), SolverCauses.Decision())

        self._add_edge(A, B, 5, solver, diff_reasoner)
        self.assertIsNone(diff_reasoner.propagate(solver))

        check_bounds(0, 3, 0, 8)

        solver.set_bound_value(SignedVar(A, True), BoundVal(1), SolverCauses.Decision())
        self.assertIsNone(diff_reasoner.propagate(solver))

        check_bounds(0, 1, 0, 6)

        x = self._add_inactive_edge(A, B, 3, solver, diff_reasoner)
        self._mark_edge_active(x, solver)
        self.assertIsNone(diff_reasoner.propagate(solver))

        check_bounds(0, 1, 0, 4)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#################################################################################

if __name__ == '__main__':
    unittest.main()
