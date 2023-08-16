from __future__ import annotations

#################################################################################

from fundamentals import *

from solver import *
from solver_api import *

import unittest

#################################################################################

class TestSolverImplications(unittest.TestCase):
   
    def test_direct_implications(self):
        solver = Solver()

        # We don't care for domains of variables
        # for this implication test
        A = add_new_non_optional_variable(solver, (0,0), True)
        B = add_new_non_optional_variable(solver, (0,0), True)
        C = add_new_non_optional_variable(solver, (0,0), True)

        Aleq1 = Literal(SignedVar(A, True), BoundValue(1))

        Bleq1 = Literal(SignedVar(B, True), BoundValue(1))

        Cleq1 = Literal(SignedVar(C, True), BoundValue(1))

        add_implication(solver, Aleq1, Bleq1)
        self.assertEqual(
            solver.get_literals_directly_implied_by(Aleq1),
            [Bleq1]
        )
        add_implication(solver, Bleq1, Cleq1)
        self.assertEqual(
            solver.get_literals_directly_implied_by(Bleq1),
            [Cleq1]
        )
        # We have Aleq1 => Bleq1 and Bleq1 => Cleq1,
        # so we also have Aleq1 => Cleq1. However, this is 
        # not a "direct" implication, as Cleq1 isn't explicitly
        # added to the adjacency set "guarded" by 1 of signed
        # variable A-.
        self.assertNotIn(
            Cleq1,
            solver.get_literals_directly_implied_by(Aleq1),
        )
        # However, solver.is_literal_implying(Aleq1, Cleq1)
        # returns True, as it should.
        self.assertEqual(
            solver.is_implication_true(Aleq1, Cleq1),
            True,
        )

    def test_full_implications(self):
        solver = Solver()

        # We don't care for domains of variables
        # for this implication test
        A = add_new_non_optional_variable(solver, (0,0), True)
        B = add_new_non_optional_variable(solver, (0,0), True)
        C = add_new_non_optional_variable(solver, (0,0), True)

        Aleq0 = Literal(SignedVar(A, True), BoundValue(0))
        Aleq1 = Literal(SignedVar(A, True), BoundValue(1))
        Aleq2 = Literal(SignedVar(A, True), BoundValue(2))
        AleqM1 = Literal(SignedVar(A, True), BoundValue(-1))

        Bleq0 = Literal(SignedVar(B, True), BoundValue(0))
        Bleq1 = Literal(SignedVar(B, True), BoundValue(1))
        Bleq2 = Literal(SignedVar(B, True), BoundValue(2))

        Cleq1 = Literal(SignedVar(C, True), BoundValue(1))
        Cleq2 = Literal(SignedVar(C, True), BoundValue(2))
        Cleq3 = Literal(SignedVar(C, True), BoundValue(3))

        self.assertTrue(solver.is_implication_true(Aleq0, Aleq0))
        self.assertTrue(solver.is_implication_true(Aleq0, Aleq1))
        self.assertFalse(solver.is_implication_true(Aleq0, Bleq0))
        self.assertFalse(solver.is_implication_true(Aleq0, AleqM1))

        add_implication(solver, Aleq1, Bleq1)

        self.assertTrue(solver.is_implication_true(Aleq1, Bleq1))
        self.assertTrue(solver.is_implication_true(Aleq0, Bleq1))
        self.assertTrue(solver.is_implication_true(Aleq1, Bleq2))
        self.assertTrue(solver.is_implication_true(Aleq0, Bleq2))
        self.assertFalse(solver.is_implication_true(Aleq1, Bleq0))
        self.assertFalse(solver.is_implication_true(Aleq1, Bleq0))

        add_implication(solver, Bleq2, Cleq2)

        self.assertTrue(solver.is_implication_true(Aleq1, Bleq1))
        self.assertTrue(solver.is_implication_true(Aleq1, Cleq2))
        self.assertTrue(solver.is_implication_true(Aleq1, Cleq3))
        self.assertFalse(solver.is_implication_true(Aleq1, Cleq1))
        self.assertTrue(solver.is_implication_true(Aleq0, Cleq2))
        self.assertFalse(solver.is_implication_true(Aleq2, Cleq2))

    def test_implication_cycle(self):
        solver = Solver()

        # We don't care for domains of variables
        # for this implication test
        A = add_new_non_optional_variable(solver, (0,0), True)
        B = add_new_non_optional_variable(solver, (0,0), True)
        C = add_new_non_optional_variable(solver, (0,0), True)
        D = add_new_non_optional_variable(solver, (0,0), True)

        Aleq0 = Literal(SignedVar(A, True), BoundValue(0))
        Bleq0 = Literal(SignedVar(B, True), BoundValue(0))
        Cleq0 = Literal(SignedVar(C, True), BoundValue(0))
        Dleq0 = Literal(SignedVar(D, True), BoundValue(0))

        add_implication(solver, Aleq0, Bleq0)
        add_implication(solver, Bleq0, Aleq0)

        add_implication(solver, Cleq0, Dleq0)
        add_implication(solver, Dleq0, Cleq0)

        self.assertFalse(solver.is_implication_true(Aleq0, Cleq0))

#################################################################################

class TestSolverSetBounds(unittest.TestCase):

    def test_non_optional_variables(self):
        solver = Solver()

        A = add_new_non_optional_variable(solver, (0, 10), True)
        AP, AM = SignedVar(A, True), SignedVar(A, False)

        self.assertEqual(
            solver.set_bound_value(AM, BoundValue(1), SolverCause.Decision()),
            False,
        )
        self.assertEqual(
            solver.set_bound_value(AM, BoundValue(0), SolverCause.Decision()),
            False,
        )
        self.assertEqual(
            solver.set_bound_value(AM, BoundValue(-1), SolverCause.Decision()),
            True,
        )
        self.assertEqual(
            solver.set_bound_value(AP, BoundValue(11), SolverCause.Decision()),
            False,
        )
        self.assertEqual(
            solver.set_bound_value(AP, BoundValue(10), SolverCause.Decision()),
            False,
        )
        self.assertEqual(
            solver.set_bound_value(AP, BoundValue(9), SolverCause.Decision()),
            True,
        )

        self.assertEqual(
            solver.set_bound_value(AM, BoundValue(-9), SolverCause.Decision()),
            True,
        )

        self.assertEqual(
            solver.set_bound_value(AM, BoundValue(-10), SolverCause.Decision()),
            SolverConflictInfo.InvalidBoundUpdate(Literal(AM, BoundValue(-10)), SolverCause.Decision()),
        )

        solver.undo_and_return_last_event_at_current_decision_level()

        self.assertEqual(
            solver.set_bound_value(AP, BoundValue(1), SolverCause.Decision()),
            True,
        )

        self.assertEqual(
            solver.set_bound_value(AP, BoundValue(0), SolverCause.Decision()),
            SolverConflictInfo.InvalidBoundUpdate(Literal(AP, BoundValue(0)), SolverCause.Decision()),
        )

    def test_optional_variables(self):
        solver = Solver()

        # P1 is always present
        P1 = add_new_non_optional_variable(solver, (0, 1), True)
        P1_lit = Literal(SignedVar(P1, False), BoundValue(-1))
        add_implication(solver, P1_lit, TrueLiteral)

        # P2 is present if P1 is true / P1_lit is entailed
        P2 = add_new_non_optional_variable(solver, (0, 1), True)
        P2_lit = Literal(SignedVar(P2, False), BoundValue(-1))
        add_implication(solver, P2_lit, P1_lit)

        # A is present if P2 is true / P3_lit is entailed
        A = add_new_optional_variable(solver, (0, 10), True, P2_lit)
        AP, AM = SignedVar(A, True), SignedVar(A, False)

        # Reduce the domain of A equal to [5, 5].
        # This should have no consequences on P2 and P1
        self.assertEqual(
            solver.set_bound_value(AP, BoundValue(5), SolverCause.Decision()),
            True,
        )
        self.assertEqual(
            solver.set_bound_value(AM, BoundValue(-5), SolverCause.Decision()),
            True,
        )
        self.assertEqual(solver.bound_values[SignedVar(A, False)], -5)
        self.assertEqual(solver.bound_values[SignedVar(A, True)], 5)
        self.assertEqual(solver.bound_values[SignedVar(P1, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P1, True)], 1)
        self.assertEqual(solver.bound_values[SignedVar(P2, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P2, True)], 1)

        # Make the domain of A empty, this shuold imply that P2 is false
        solver.set_bound_value(AM, BoundValue(-6), SolverCause.Decision())

        self.assertEqual(solver.bound_values[SignedVar(A, False)], -5)
        self.assertEqual(solver.bound_values[SignedVar(A, True)], 5)
        self.assertEqual(solver.bound_values[SignedVar(P1, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P1, True)], 1)
        self.assertEqual(solver.bound_values[SignedVar(P2, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P2, True)], 0)

        # Make P1 true, this should have no impact
        solver.set_bound_value(SignedVar(P1, False), BoundValue(-1), SolverCause.Decision())

        self.assertEqual(solver.bound_values[SignedVar(A, False)], -5)
        self.assertEqual(solver.bound_values[SignedVar(A, True)], 5)
        self.assertEqual(solver.bound_values[SignedVar(P1, False)], -1)
        self.assertEqual(solver.bound_values[SignedVar(P1, True)], 1)
        self.assertEqual(solver.bound_values[SignedVar(P2, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P2, True)], 0)

        # Make P2 have an empty domain, this should imply that P1
        # is false, which is a contradiction with out previous decision
        self.assertIsInstance(
            solver.set_bound_value(SignedVar(P2, True), BoundValue(-1), SolverCause.Decision()),
            SolverConflictInfo.InvalidBoundUpdate,
        )

#################################################################################

class TestSolverEntails(unittest.TestCase):

    def test_is_literal_entailed(self):
        solver = Solver()

        A = add_new_non_optional_variable(solver, (0, 10), True)
        AP, AM = SignedVar(A, True), SignedVar(A, False)

        self.assertTrue(solver.is_literal_entailed(Literal(AM, BoundValue(2))))
        self.assertTrue(solver.is_literal_entailed(Literal(AM, BoundValue(1))))
        self.assertTrue(solver.is_literal_entailed(Literal(AM, BoundValue(0))))

        self.assertFalse(solver.is_literal_entailed(Literal(AM, BoundValue(-1))))
        self.assertFalse(solver.is_literal_entailed(Literal(AM, BoundValue(-2))))
        self.assertFalse(solver.is_literal_entailed(Literal(AM, BoundValue(-10))))

        self.assertTrue(solver.is_literal_entailed(Literal(AP, BoundValue(12))))
        self.assertTrue(solver.is_literal_entailed(Literal(AP, BoundValue(11))))
        self.assertTrue(solver.is_literal_entailed(Literal(AP, BoundValue(10))))

        self.assertFalse(solver.is_literal_entailed(Literal(AP, BoundValue(9))))
        self.assertFalse(solver.is_literal_entailed(Literal(AP, BoundValue(8))))
        self.assertFalse(solver.is_literal_entailed(Literal(AP, BoundValue(0))))

#################################################################################
#################################################################################

if __name__ == '__main__':
    unittest.main()
