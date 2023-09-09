from __future__ import annotations

#################################################################################

import unittest

from src.fundamentals import (Lit, Var,
                            are_tightened_disj_literals_tautological,
                            tighten_disj_literals)

#################################################################################

class TestFundamentals(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_tighten_literals(self):

        A = Var(1)
        B = Var(2)

        self.assertEqual(tighten_disj_literals([Lit.geq(A, 0), Lit.geq(A, 1)]),
                         (Lit.geq(A, 0),))

        self.assertEqual(tighten_disj_literals([Lit.leq(A, 0), Lit.leq(A, 1)]),
                         (Lit.leq(A, 1),))

        self.assertEqual(tighten_disj_literals([Lit.leq(A, 1), Lit.leq(A, 0)]),
                         (Lit.leq(A, 1),))

        self.assertEqual(tighten_disj_literals([Lit.leq(A, 0), Lit.leq(A, 0)]),
                         (Lit.leq(A, 0),))

        self.assertEqual(tighten_disj_literals([Lit.leq(A, 0), Lit.leq(A, 1), Lit.leq(A,1), Lit.leq(A,0)]),
                         (Lit.leq(A, 1),))

        self.assertEqual(tighten_disj_literals([Lit.leq(A, 0), Lit.leq(A, 0).negation()]),
                         (Lit.leq(A, 0).negation(), Lit.leq(A, 0)))

        self.assertEqual(tighten_disj_literals([Lit.leq(A, 0), Lit.leq(B, 1), Lit.leq(A, 1), Lit.leq(B, 0)]),
                         (Lit.leq(A, 1), Lit.leq(B, 1)))

        self.assertEqual(tighten_disj_literals([Lit.geq(A, 0), Lit.geq(B, 1), Lit.geq(A, 1), Lit.geq(B, 0)]),
                         (Lit.geq(A, 0), Lit.geq(B, 0)))

        self.assertEqual(tighten_disj_literals([Lit.leq(A, 0),
                                           Lit.leq(B, 1),
                                           Lit.leq(A, 1),
                                           Lit.leq(B, 0),
                                           Lit.geq(A, 0),
                                           Lit.geq(B, 1),
                                           Lit.geq(A, 1),
                                           Lit.geq(B, 0)]),
                        (Lit.geq(A, 0), Lit.leq(A, 1), Lit.geq(B, 0), Lit.leq(B, 1)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_are_tightened_literals_tautological(self):

        A = Var(1)
        B = Var(2)

        self.assertTrue(are_tightened_disj_literals_tautological(tighten_disj_literals((Lit.leq(A, 0), 
                                                                              Lit.leq(A, 0).negation()))))

        self.assertTrue(are_tightened_disj_literals_tautological(tighten_disj_literals((Lit.leq(A, 0), 
                                                                              Lit.geq(A, 0)))))

        self.assertTrue(are_tightened_disj_literals_tautological(tighten_disj_literals((Lit.leq(A, 0), 
                                                                              Lit.geq(A, 1)))))

        self.assertTrue(are_tightened_disj_literals_tautological(tighten_disj_literals((Lit.leq(A, 0), 
                                                                              Lit.leq(B, 0), 
                                                                              Lit.leq(B, 2), 
                                                                              Lit.leq(A, 0).negation()))))
        self.assertRaisesRegex(ValueError, ".* is not tightened.",
                               are_tightened_disj_literals_tautological,(Lit.leq(A, 0), Lit.leq(B, 0), Lit.leq(B, 2)))

        self.assertRaisesRegex(ValueError, ".* empty set of literals is indeed tautological. However.*",
                               are_tightened_disj_literals_tautological,())

#################################################################################
