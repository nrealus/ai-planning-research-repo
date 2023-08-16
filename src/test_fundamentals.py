from __future__ import annotations

#################################################################################

from fundamentals import *

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
            Literal(SignedVar(Var(1), True), BoundValue(2)).negation(),
            Literal(SignedVar(Var(1), False), BoundValue(-3)),
        )

    def test_is_bound_value_stronger_than(self):
        self.assertTrue(BoundValue(2).is_stronger_than(BoundValue(3)))
        self.assertTrue(BoundValue(2).is_stronger_than(BoundValue(2)))
        self.assertFalse(BoundValue(2).is_stronger_than(BoundValue(1)))

#################################################################################

if __name__ == '__main__':
    unittest.main()
