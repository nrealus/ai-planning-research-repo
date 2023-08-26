from __future__ import annotations

#################################################################################

from typing import Optional, Tuple

from fundamentals import (
    SignedVar, BoundVal, Lit, TRUE_LIT,
    TightDisjunction,
)

from solver import SolverCauses, SolverDecisions, SolverConflictInfo, Solver
from solver_sat_reasoner import SATReasoner

from solver_api import (
    add_new_non_optional_variable,
    add_new_optional_variable,
    add_new_presence_variable,
    _insert_implication_between_literals_on_non_optional_vars
)

import unittest

#################################################################################

class TestSATReasonerPropagation(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_simple(self):
        solver = Solver()
        sat_reasoner = SATReasoner()

        def value_of(var) -> Optional[int]:
            if solver.bound_values[SignedVar(var,True)] == -solver.bound_values[SignedVar(var,False)]:
                return solver.bound_values[SignedVar(var,True)]
            else:
                return None            

        A = add_new_non_optional_variable(solver, (0,1), True)
        B = add_new_non_optional_variable(solver, (0,1), True)

        self.assertEqual(value_of(A), None)
        self.assertEqual(value_of(B), None)

        A_or_B = TightDisjunction((Lit.geq(A, 1), Lit.geq(B, 1))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B, TRUE_LIT)

        sat_reasoner.propagate(solver)

        self.assertEqual(value_of(A), None)
        self.assertEqual(value_of(B), None)

        solver.set_bound_value(SignedVar(A, True), BoundVal(0), SolverCauses.Decision())

        self.assertEqual(value_of(A), 0)
        self.assertEqual(value_of(B), None)

        sat_reasoner.propagate(solver)

        self.assertEqual(value_of(A), 0)
        self.assertEqual(value_of(B), 1)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_complex(self):
        solver = Solver()
        sat_reasoner = SATReasoner()

        def value_of(var) -> Optional[int]:
            if solver.bound_values[SignedVar(var,True)] == -solver.bound_values[SignedVar(var,False)]:
                return solver.bound_values[SignedVar(var,True)]
            else:
                return None            

        A = add_new_non_optional_variable(solver, (0,1), True)
        B = add_new_non_optional_variable(solver, (0,1), True)
        C = add_new_non_optional_variable(solver, (0,1), True)
        D = add_new_non_optional_variable(solver, (0,1), True)

        self.assertEqual([value_of(v) for v in (A,B,C,D)], [None, None, None, None])

        clause_literals = TightDisjunction((
            Lit.geq(A, 1),
            Lit.geq(B, 1),
            Lit.geq(C, 1),
            Lit.geq(D, 1),
            )).literals
        sat_reasoner.add_new_fixed_clause_with_scope(clause_literals, TRUE_LIT)

        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [None, None, None, None])

        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(Lit.leq(A, 0)),
            (sat_reasoner,))
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, None, None, None])
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, None, None, None])

        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(Lit.leq(B, 0)),
            (sat_reasoner,))
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, None, None])
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, None, None])

        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(Lit.geq(C, 1)),
            (sat_reasoner,))
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 1, None])
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 1, None])

        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(Lit.leq(D, 0)),
            (sat_reasoner,))
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 1, 0])
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 1, 0])

        solver.backtrack_to_decision_level(
            solver.dec_level-1,
            (sat_reasoner,))
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 1, None])
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 1, None])

        solver.backtrack_to_decision_level(
            solver.dec_level-1,
            (sat_reasoner,))
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, None, None])
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, None, None])

        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(Lit.leq(C, 0)),
            (sat_reasoner,))
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 0, None])
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 0, 1])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_failure(self):
        solver = Solver()
        sat_reasoner = SATReasoner()

        def value_of(var) -> Optional[int]:
            if solver.bound_values[SignedVar(var,True)] == -solver.bound_values[SignedVar(var,False)]:
                return solver.bound_values[SignedVar(var,True)]
            else:
                return None            

        A = add_new_non_optional_variable(solver, (0,1), True)
        B = add_new_non_optional_variable(solver, (0,1), True)

        self.assertEqual(value_of(A), None)
        self.assertEqual(value_of(B), None)

        A_or_B = TightDisjunction((Lit.geq(A, 1), Lit.geq(B, 1))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B, TRUE_LIT)

        sat_reasoner.propagate(solver)

        self.assertEqual(value_of(A), None)
        self.assertEqual(value_of(B), None)

#        solver.increment_decision_level_and_perform_set_literal_decision(
#            SolverDecisions.SetLiteral(Lit.leq(A, 0)),
#            (sat_reasoner,))
        solver.set_bound_value(SignedVar(A, True), BoundVal(0), SolverCauses.Decision())
#        solver.increment_decision_level_and_perform_set_literal_decision(
#            SolverDecisions.SetLiteral(Lit.leq(B, 0)),
#            (sat_reasoner,))
        solver.set_bound_value(SignedVar(B, True), BoundVal(0), SolverCauses.Decision())

        self.assertEqual(value_of(A), False)
        self.assertEqual(value_of(B), False)

        self.assertNotEqual(sat_reasoner.propagate(solver), None)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_int_propagation(self):
        solver = Solver()
        sat_reasoner = SATReasoner()

        def value_of(var) -> Tuple[int, int]:
            return (-solver.bound_values[SignedVar(var, False)],
                solver.bound_values[SignedVar(var, True)])

        A = add_new_non_optional_variable(solver, (0,10), True)
        B = add_new_non_optional_variable(solver, (0,10), True)
        C = add_new_non_optional_variable(solver, (0,10), True)
        D = add_new_non_optional_variable(solver, (0,10), True)

        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(0,10), (0,10), (0,10), (0,10)])

        clause1_literals = TightDisjunction((Lit.leq(A, 5), Lit.leq(B, 5))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(clause1_literals, TRUE_LIT)
        clause2_literals = TightDisjunction((Lit.geq(C, 5), Lit.geq(D, 5))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(clause2_literals, TRUE_LIT)

        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(0,10), (0,10), (0,10), (0,10)])

        # Lower bound changes

        solver.set_bound_value(SignedVar(A, False), BoundVal(-4), SolverCauses.Decision())
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(4,10), (0,10), (0,10), (0,10)])
        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(4,10), (0,10), (0,10), (0,10)])

        solver.set_bound_value(SignedVar(A, False), BoundVal(-5), SolverCauses.Decision())
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(5,10), (0,10), (0,10), (0,10)])
        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(5,10), (0,10), (0,10), (0,10)])

        # Trigger first clause

        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(Lit.geq(A, 6)),
            (sat_reasoner,))
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(6,10), (0,10), (0,10), (0,10)])
        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(6,10), (0,5), (0,10), (0,10)])

        # Retrigger first clause with stronger literal

        solver.backtrack_to_decision_level(solver.dec_level-1, (sat_reasoner,))
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(5,10), (0,10), (0,10), (0,10)])
        solver.set_bound_value(SignedVar(A, False), BoundVal(-8), SolverCauses.Decision())
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,10), (0,10), (0,10)])
        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,10), (0,10)])

        # Upper bound changes

        solver.set_bound_value(SignedVar(C, True), BoundVal(6), SolverCauses.Decision())
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,6), (0,10)])
        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,6), (0,10)])

        solver.set_bound_value(SignedVar(C, True), BoundVal(5), SolverCauses.Decision())
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,5), (0,10)])
        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,5), (0,10)])

        # Should trigger second clause
        
        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(Lit.leq(C, 4)),
            (sat_reasoner,))
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,4), (0,10)])
        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,4), (5,10)])

        # Retrigger second clause with stronger literal

        solver.backtrack_to_decision_level(solver.dec_level-1, (sat_reasoner,))
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,5), (0,10)])
        solver.set_bound_value(SignedVar(C, True), BoundVal(2), SolverCauses.Decision())
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,2), (0,10)])
        sat_reasoner.propagate(solver)
        self.assertListEqual([value_of(v) for v in (A,B,C,D)], [(8,10), (0,5), (0,2), (5,10)])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#################################################################################

class TestSATReasonerClauses(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_online_clause_insertion(self):
        solver = Solver()
        sat_reasoner = SATReasoner()

        def value_of(var) -> Optional[int]:
            if solver.bound_values[SignedVar(var,True)] == -solver.bound_values[SignedVar(var,False)]:
                return solver.bound_values[SignedVar(var,True)]
            else:
                return None            

        A = add_new_non_optional_variable(solver, (0,1), True)
        B = add_new_non_optional_variable(solver, (0,1), True)
        C = add_new_non_optional_variable(solver, (0,1), True)
        D = add_new_non_optional_variable(solver, (0,1), True)

        self.assertEqual(value_of(A), None)
        self.assertEqual(value_of(B), None)
        self.assertEqual(value_of(C), None)
        self.assertEqual(value_of(D), None)

        # not A and not B
        solver.set_bound_value(SignedVar(A, True), BoundVal(0), SolverCauses.Decision())
        solver.set_bound_value(SignedVar(B, True), BoundVal(0), SolverCauses.Decision())
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, None, None])

        A_or_B_or_C_or_D = TightDisjunction((Lit.geq(A, 1), Lit.geq(B, 1), Lit.geq(C, 1), Lit.geq(D, 1))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B_or_C_or_D, TRUE_LIT)
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, None, None])

        notA_or_notB = TightDisjunction((Lit.leq(A, 0), Lit.leq(B, 0))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(notA_or_notB, TRUE_LIT)
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, None, None])

        notA_or_B = TightDisjunction((Lit.leq(A, 0), Lit.geq(B, 1))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(notA_or_B, TRUE_LIT)
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, None, None])

        A_or_B_or_notC = TightDisjunction((Lit.geq(A, 1), Lit.geq(B, 1), Lit.leq(C, 0))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B_or_notC, TRUE_LIT)
        sat_reasoner.propagate(solver)
        self.assertEqual([value_of(v) for v in (A,B,C,D)], [0, 0, 0, 1])

        A_or_B_or_C_or_notD = TightDisjunction((Lit.geq(A, 1), Lit.geq(B, 1), Lit.geq(C, 1), Lit.leq(D, 0))).literals
        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B_or_C_or_notD, TRUE_LIT)

        self.assertNotEqual(sat_reasoner.propagate(solver), None)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# TODO....    def test_scoped_clauses(self):


#################################################################################

if __name__ == '__main__':
    unittest.main()
