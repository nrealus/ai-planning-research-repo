from __future__ import annotations

#################################################################################

import unittest

from src.fundamentals import (Lit, Var,
                              simplify_lits_disjunction, is_lits_disjunction_tautological)

#################################################################################

class TestLitsDisjunctionSimplification(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_simplify_lits_disjunction(self):

        A = Var(1)
        B = Var(2)

        self.assertEqual(simplify_lits_disjunction([Lit.geq(A, 0),
                                                    Lit.geq(A, 1)]),
                         (Lit.geq(A, 0),))

        self.assertEqual(simplify_lits_disjunction([Lit.leq(A, 0), 
                                                    Lit.leq(A, 1)]),
                         (Lit.leq(A, 1),))

        self.assertEqual(simplify_lits_disjunction([Lit.leq(A, 1), 
                                                    Lit.leq(A, 0)]),
                         (Lit.leq(A, 1),))

        self.assertEqual(simplify_lits_disjunction([Lit.leq(A, 0),
                                                    Lit.leq(A, 0)]),
                         (Lit.leq(A, 0),))

        self.assertEqual(simplify_lits_disjunction([Lit.leq(A, 0),
                                                    Lit.leq(A, 1),
                                                    Lit.leq(A, 1),
                                                    Lit.leq(A, 0)]),
                         (Lit.leq(A, 1),))

        self.assertEqual(simplify_lits_disjunction([Lit.leq(A, 0), 
                                                    Lit.leq(A, 0).neg]),
                         (Lit.leq(A, 0).neg,
                          Lit.leq(A, 0)))

        self.assertEqual(simplify_lits_disjunction([Lit.leq(A, 0), 
                                                    Lit.leq(B, 1), 
                                                    Lit.leq(A, 1), 
                                                    Lit.leq(B, 0)]),
                         (Lit.leq(A, 1), 
                          Lit.leq(B, 1)))

        self.assertEqual(simplify_lits_disjunction([Lit.geq(A, 0), 
                                                    Lit.geq(B, 1), 
                                                    Lit.geq(A, 1), 
                                                    Lit.geq(B, 0)]),
                         (Lit.geq(A, 0), 
                          Lit.geq(B, 0)))

        self.assertEqual(simplify_lits_disjunction([Lit.leq(A, 0),
                                                    Lit.leq(B, 1),
                                                    Lit.leq(A, 1),
                                                    Lit.leq(B, 0),
                                                    Lit.geq(A, 0),
                                                    Lit.geq(B, 1),
                                                    Lit.geq(A, 1),
                                                    Lit.geq(B, 0)]),
                        (Lit.geq(A, 0),
                         Lit.leq(A, 1),
                         Lit.geq(B, 0),
                         Lit.leq(B, 1)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_are_tightened_literals_tautological(self):

        A = Var(1)
        B = Var(2)

        self.assertTrue(is_lits_disjunction_tautological(simplify_lits_disjunction((Lit.leq(A, 0), 
                                                                                    Lit.leq(A, 0).neg))))

        self.assertTrue(is_lits_disjunction_tautological(simplify_lits_disjunction((Lit.leq(A, 0),
                                                                                    Lit.geq(A, 0)))))

        self.assertTrue(is_lits_disjunction_tautological(simplify_lits_disjunction((Lit.leq(A, 0),
                                                                                    Lit.geq(A, 1)))))

        self.assertTrue(is_lits_disjunction_tautological(simplify_lits_disjunction((Lit.leq(A, 0),
                                                                                    Lit.leq(B, 0), 
                                                                                    Lit.leq(B, 2), 
                                                                                    Lit.leq(A, 0).neg))))
        self.assertRaises(ValueError,
                          is_lits_disjunction_tautological,(Lit.leq(A, 0),
                                                            Lit.leq(B, 0),
                                                            Lit.leq(B, 2)))

        self.assertRaises(ValueError,
                          is_lits_disjunction_tautological,())

#################################################################################
