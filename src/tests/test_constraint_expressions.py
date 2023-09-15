from __future__ import annotations

#################################################################################

import unittest

from src.fundamentals import FALSE_LIT, TRUE_LIT, ZERO_VAR, Lit, Var
from src.constraint_expressions import ElemConstrExpr

#################################################################################

class TestElemConstrExpr(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_from_int_atoms_leq(self):

        A = Var(1)
        B = Var(2)

        self.assertEqual(ElemConstrExpr.from_int_atoms_leq(A, 0, A, 0),
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, TRUE_LIT))

        self.assertEqual(ElemConstrExpr.from_int_atoms_leq(A, 0, A, 1),
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, TRUE_LIT))

        self.assertEqual(ElemConstrExpr.from_int_atoms_leq(A, 1, A, 0),
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, FALSE_LIT))

        self.assertEqual(ElemConstrExpr.from_int_atoms_leq(A, -1, ZERO_VAR, 0),
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, Lit.leq(A, 1)))

        self.assertEqual(ElemConstrExpr.from_int_atoms_leq(ZERO_VAR, 0, A, -1),
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, Lit.geq(A, 1)))

        self.assertEqual(ElemConstrExpr.from_int_atoms_leq(A, 3, B, 5),
                         ElemConstrExpr(ElemConstrExpr.Kind.MAX_DIFFERENCE, (A, B, 2)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_from_lits_simplify_or(self):

        A = Var(1)
        B = Var(2)

        self.assertEqual(ElemConstrExpr.from_lits_simplify_or((Lit.leq(A, 1),
                                                              Lit.leq(B, 1))), 
                         ElemConstrExpr(ElemConstrExpr.Kind.OR, (Lit.leq(A,1),
                                                                 Lit.leq(B,1))))

        self.assertEqual(ElemConstrExpr.from_lits_simplify_or((Lit.leq(A, 1),)), 
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, Lit.leq(A,1)))

        self.assertEqual(ElemConstrExpr.from_lits_simplify_or((Lit.leq(A, 1),
                                                               Lit.leq(A, 2))), 
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, Lit.leq(A,2)))
        
        self.assertEqual(ElemConstrExpr.from_lits_simplify_or((Lit.leq(A, 1),
                                                               Lit.leq(A, 2),
                                                               Lit.leq(B, 1))), 
                         ElemConstrExpr(ElemConstrExpr.Kind.OR, (Lit.leq(A,2),
                                                                 Lit.leq(B,1))))

        self.assertEqual(ElemConstrExpr.from_lits_simplify_or((Lit.leq(A, 1),
                                                               Lit.geq(A, 0),
                                                               Lit.leq(B, 1))), 
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, TRUE_LIT))

        self.assertEqual(ElemConstrExpr.from_lits_simplify_or(()), 
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, FALSE_LIT))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_negated(self):

        A = Var(1)
        B = Var(2)

        self.assertEqual(ElemConstrExpr.from_lit(Lit.leq(A, 1)).negated,
                         ElemConstrExpr.from_lit(Lit.geq(A, 2)))

        self.assertEqual(ElemConstrExpr.from_max_diff(A, B, 2).negated,
                         ElemConstrExpr.from_max_diff(B, A, -3))

        self.assertEqual(ElemConstrExpr.from_lits_simplify_or((Lit.leq(A, 1),
                                                               Lit.leq(A, 2),
                                                               Lit.leq(B, 1))).negated,
                        ElemConstrExpr(ElemConstrExpr.Kind.AND,(Lit.geq(A,3), Lit.geq(B,2)))) 

        self.assertEqual(ElemConstrExpr.from_lits_simplify_and((Lit.leq(A, 1),
                                                                Lit.leq(A, 2),
                                                                Lit.leq(B, 1))).negated,
                        ElemConstrExpr(ElemConstrExpr.Kind.OR,(Lit.geq(A,2), Lit.geq(B,2)))) 

        self.assertEqual(ElemConstrExpr.from_lits_simplify_or((Lit.leq(A, 1),
                                                               Lit.geq(A, 0),
                                                               Lit.leq(B, 1))).negated, 
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, FALSE_LIT))

        self.assertEqual(ElemConstrExpr.from_lits_simplify_and((Lit.leq(A, 1),
                                                                Lit.geq(A, 0),
                                                                Lit.leq(B, 1))).negated, 
                         ElemConstrExpr(ElemConstrExpr.Kind.LIT, TRUE_LIT))

#################################################################################
