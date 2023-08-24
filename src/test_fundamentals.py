from __future__ import annotations

#################################################################################

from fundamentals import (
    Var,
    SignedVar, BoundVal, Lit,
    TightDisjunction,
)

import unittest

#################################################################################

class TestFundamentals(unittest.TestCase):

    def test_opposite_signed_var(self):
        self.assertEqual(
            SignedVar(Var(1), True),
            SignedVar(Var(1), False).opposite_signed_var(),
        )

    def test_literal_negation(self):
        self.assertEqual(
            Lit(SignedVar(Var(1), True), BoundVal(2)).negation(),
            Lit(SignedVar(Var(1), False), BoundVal(-3)),
        )

    def test_is_bound_value_stronger_than(self):
        self.assertTrue(BoundVal(2).is_stronger_than(BoundVal(3)))
        self.assertTrue(BoundVal(2).is_stronger_than(BoundVal(2)))
        self.assertFalse(BoundVal(2).is_stronger_than(BoundVal(1)))

    def test_tight_disjunction_construction(self):
        A = Var(1)
        B = Var(2)

        self.assertEqual(
            TightDisjunction([Lit.geq(A, 0), Lit.geq(A, 1)]).literals,
            (Lit.geq(A, 0),))

        self.assertEqual(
            TightDisjunction([Lit.leq(A, 0), Lit.leq(A, 1)]).literals,
            (Lit.leq(A, 1),))
        self.assertEqual(
            TightDisjunction([Lit.leq(A, 1), Lit.leq(A, 0)]).literals,
            (Lit.leq(A, 1),))
        self.assertEqual(
            TightDisjunction([Lit.leq(A, 0), Lit.leq(A, 0)]).literals,
            (Lit.leq(A, 0),))
        self.assertEqual(
            TightDisjunction([Lit.leq(A, 0), Lit.leq(A, 1), Lit.leq(A,1), Lit.leq(A,0)]).literals,
            (Lit.leq(A, 1),))

        self.assertEqual(
            TightDisjunction([Lit.leq(A, 0), Lit.leq(A, 0).negation()]).literals,
            (Lit.leq(A, 0).negation(), Lit.leq(A, 0)))

        self.assertEqual(
            TightDisjunction([Lit.leq(A, 0), Lit.leq(B, 1), Lit.leq(A, 1), Lit.leq(B, 0)]).literals,
            (Lit.leq(A, 1), Lit.leq(B, 1)))

        self.assertEqual(
            TightDisjunction([Lit.geq(A, 0), Lit.geq(B, 1), Lit.geq(A, 1), Lit.geq(B, 0)]).literals,
            (Lit.geq(A, 0), Lit.geq(B, 0)))

        self.assertEqual(
            TightDisjunction([
                Lit.leq(A, 0),
                Lit.leq(B, 1),
                Lit.leq(A, 1),
                Lit.leq(B, 0),
                Lit.geq(A, 0),
                Lit.geq(B, 1),
                Lit.geq(A, 1),
                Lit.geq(B, 0)]).literals,
            (Lit.geq(A, 0), Lit.leq(A, 1), Lit.geq(B, 0), Lit.leq(B, 1)))

    def test_tight_disjunction_tautology(self):
        A = Var(1)
        B = Var(2)
        self.assertTrue(TightDisjunction((Lit.leq(A, 0), Lit.leq(A, 0).negation())).is_tautological())
        self.assertTrue(TightDisjunction((Lit.leq(A, 0), Lit.geq(A, 0))).is_tautological())
        self.assertTrue(TightDisjunction((Lit.leq(A, 0), Lit.geq(A, 1))).is_tautological())
        self.assertTrue(TightDisjunction((Lit.leq(A, 0), Lit.leq(B, 0), Lit.leq(B, 2), Lit.leq(A, 0).negation())).is_tautological())

#################################################################################

if __name__ == '__main__':
    unittest.main()
