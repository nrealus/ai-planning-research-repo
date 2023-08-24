from __future__ import annotations

#################################################################################

from fundamentals import *

from solver import *
from solver_api import *
from solver_api import _insert_implication_between_literals_on_non_optional_vars

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

        Aleq1 = Lit.leq(A, 1)
        
        Bleq1 = Lit.leq(B, 1)
        
        Cleq1 = Lit.leq(C, 1)

        _insert_implication_between_literals_on_non_optional_vars(solver, Aleq1, Bleq1)
        self.assertEqual(
            solver.get_literals_directly_implied_by(Aleq1),
            [Bleq1]
        )
        _insert_implication_between_literals_on_non_optional_vars(solver, Bleq1, Cleq1)
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
        # However, solver.is_Lit_implying(Aleq1, Cleq1)
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

        Aleq0 = Lit.leq(A, 0)
        Aleq1 = Lit.leq(A, 1)
        Aleq2 = Lit.leq(A, 2)
        AleqM1 = Lit.leq(A, -1)

        Bleq0 = Lit.leq(B, 0)
        Bleq1 = Lit.leq(B, 1)
        Bleq2 = Lit.leq(B, 2)

        Cleq1 = Lit.leq(C, 1)
        Cleq2 = Lit.leq(C, 2)
        Cleq3 = Lit.leq(C, 3)

        self.assertTrue(solver.is_implication_true(Aleq0, Aleq0))
        self.assertTrue(solver.is_implication_true(Aleq0, Aleq1))
        self.assertFalse(solver.is_implication_true(Aleq0, Bleq0))
        self.assertFalse(solver.is_implication_true(Aleq0, AleqM1))

        _insert_implication_between_literals_on_non_optional_vars(solver, Aleq1, Bleq1)

        self.assertTrue(solver.is_implication_true(Aleq1, Bleq1))
        self.assertTrue(solver.is_implication_true(Aleq0, Bleq1))
        self.assertTrue(solver.is_implication_true(Aleq1, Bleq2))
        self.assertTrue(solver.is_implication_true(Aleq0, Bleq2))
        self.assertFalse(solver.is_implication_true(Aleq1, Bleq0))
        self.assertFalse(solver.is_implication_true(Aleq1, Bleq0))

        _insert_implication_between_literals_on_non_optional_vars(solver, Bleq2, Cleq2)

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

        Aleq0 = Lit.leq(A, 0)
        Bleq0 = Lit.leq(B, 0)
        Cleq0 = Lit.leq(C, 0)
        Dleq0 = Lit.leq(D, 0)

        _insert_implication_between_literals_on_non_optional_vars(solver, Aleq0, Bleq0)
        _insert_implication_between_literals_on_non_optional_vars(solver, Bleq0, Aleq0)

        _insert_implication_between_literals_on_non_optional_vars(solver, Cleq0, Dleq0)
        _insert_implication_between_literals_on_non_optional_vars(solver, Dleq0, Cleq0)

        self.assertFalse(solver.is_implication_true(Aleq0, Cleq0))

#################################################################################

class TestSolverSetBounds(unittest.TestCase):

    def test_non_optional_variables(self):
        solver = Solver()

        A = add_new_non_optional_variable(solver, (0, 10), True)
        AP, AM = SignedVar(A, True), SignedVar(A, False)

        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(1), SolverCauses.Decision()),
            False,
        )
        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(0), SolverCauses.Decision()),
            False,
        )
        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(-1), SolverCauses.Decision()),
            True,
        )
        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(11), SolverCauses.Decision()),
            False,
        )
        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(10), SolverCauses.Decision()),
            False,
        )
        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(9), SolverCauses.Decision()),
            True,
        )

        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(-9), SolverCauses.Decision()),
            True,
        )

        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(-10), SolverCauses.Decision()),
            SolverConflictInfo.InvalidBoundUpdate(Lit(AM, BoundVal(-10)), SolverCauses.Decision()),
        )

        solver.undo_and_return_last_event_at_current_decision_level()

        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(1), SolverCauses.Decision()),
            True,
        )

        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(0), SolverCauses.Decision()),
            SolverConflictInfo.InvalidBoundUpdate(Lit(AP, BoundVal(0)), SolverCauses.Decision()),
        )

    def test_optional_variables(self):
        solver = Solver()

        # P1 is always present
        P1 = add_new_non_optional_variable(solver, (0, 1), True)
        P1_lit = Lit.geq(P1, 1)
        _insert_implication_between_literals_on_non_optional_vars(solver, P1_lit, TRUE_LIT)

        # P2 is present if P1 is true / P1_lit is entailed
        P2 = add_new_non_optional_variable(solver, (0, 1), True)
        P2_lit = Lit.geq(P2, 1)
        _insert_implication_between_literals_on_non_optional_vars(solver, P2_lit, P1_lit)

        # A is present if P2 is true / P3_lit is entailed
        A = add_new_optional_variable(solver, (0, 10), True, P2_lit)
        AP, AM = SignedVar(A, True), SignedVar(A, False)

        # Reduce the domain of A equal to [5, 5].
        # This should have no consequences on P2 and P1
        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(5), SolverCauses.Decision()),
            True,
        )
        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(-5), SolverCauses.Decision()),
            True,
        )
        self.assertEqual(solver.bound_values[SignedVar(A, False)], -5)
        self.assertEqual(solver.bound_values[SignedVar(A, True)], 5)
        self.assertEqual(solver.bound_values[SignedVar(P1, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P1, True)], 1)
        self.assertEqual(solver.bound_values[SignedVar(P2, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P2, True)], 1)

        # Make the domain of A empty, this shuold imply that P2 is false
        solver.set_bound_value(AM, BoundVal(-6), SolverCauses.Decision())

        self.assertEqual(solver.bound_values[SignedVar(A, False)], -5)
        self.assertEqual(solver.bound_values[SignedVar(A, True)], 5)
        self.assertEqual(solver.bound_values[SignedVar(P1, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P1, True)], 1)
        self.assertEqual(solver.bound_values[SignedVar(P2, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P2, True)], 0)

        # Make P1 true, this should have no impact
        solver.set_bound_value(SignedVar(P1, False), BoundVal(-1), SolverCauses.Decision())

        self.assertEqual(solver.bound_values[SignedVar(A, False)], -5)
        self.assertEqual(solver.bound_values[SignedVar(A, True)], 5)
        self.assertEqual(solver.bound_values[SignedVar(P1, False)], -1)
        self.assertEqual(solver.bound_values[SignedVar(P1, True)], 1)
        self.assertEqual(solver.bound_values[SignedVar(P2, False)], 0)
        self.assertEqual(solver.bound_values[SignedVar(P2, True)], 0)

        # Make P2 have an empty domain, this should imply that P1
        # is false, which is a contradiction with out previous decision
        self.assertIsInstance(
            solver.set_bound_value(SignedVar(P2, True), BoundVal(-1), SolverCauses.Decision()),
            SolverConflictInfo.InvalidBoundUpdate,
        )

#################################################################################

class TestSolverEntails(unittest.TestCase):

    def test_is_literal_entailed(self):
        solver = Solver()

        A = add_new_non_optional_variable(solver, (0, 10), True)
        AP, AM = SignedVar(A, True), SignedVar(A, False)

        self.assertTrue(solver.is_literal_entailed(Lit(AM, BoundVal(2))))
        self.assertTrue(solver.is_literal_entailed(Lit(AM, BoundVal(1))))
        self.assertTrue(solver.is_literal_entailed(Lit(AM, BoundVal(0))))

        self.assertFalse(solver.is_literal_entailed(Lit(AM, BoundVal(-1))))
        self.assertFalse(solver.is_literal_entailed(Lit(AM, BoundVal(-2))))
        self.assertFalse(solver.is_literal_entailed(Lit(AM, BoundVal(-10))))

        self.assertTrue(solver.is_literal_entailed(Lit(AP, BoundVal(12))))
        self.assertTrue(solver.is_literal_entailed(Lit(AP, BoundVal(11))))
        self.assertTrue(solver.is_literal_entailed(Lit(AP, BoundVal(10))))

        self.assertFalse(solver.is_literal_entailed(Lit(AP, BoundVal(9))))
        self.assertFalse(solver.is_literal_entailed(Lit(AP, BoundVal(8))))
        self.assertFalse(solver.is_literal_entailed(Lit(AP, BoundVal(0))))

#################################################################################
#################################################################################

if __name__ == '__main__':
    unittest.main()
