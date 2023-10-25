from __future__ import annotations

#################################################################################

import unittest

from src.fundamentals import SignedVar, Bound, Lit, TRUE_LIT
from src.solver.common import Causes, InvalidBoundUpdate
from src.solver.solver import Solver

#################################################################################

class TestSolverBasics(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_non_optional_vars_set_literal(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=False)

        A = solver.add_new_non_optional_variable((0, 10), True)

        self.assertFalse(solver.state.set_literal(Lit.geq(A, -1),
                                                  Causes.Decision()))        

        self.assertFalse(solver.state.set_literal(Lit.geq(A, 0),
                                                  Causes.Decision()))        
        
        self.assertTrue(solver.state.set_literal(Lit.geq(A, 1),
                                                 Causes.Decision()))        

        self.assertFalse(solver.state.set_literal(Lit.leq(A, 11),
                                                  Causes.Decision()))        

        self.assertFalse(solver.state.set_literal(Lit.leq(A, 10),
                                                  Causes.Decision()))        

        self.assertTrue(solver.state.set_literal(Lit.leq(A, 9),
                                                 Causes.Decision()))        

        self.assertTrue(solver.state.set_literal(Lit.geq(A, 9),
                                                 Causes.Decision()))        

        self.assertEqual(solver.state.set_literal(Lit.geq(A, 10),
                                                  Causes.Decision()),
                         InvalidBoundUpdate(Lit.geq(A, 10),
                                            Causes.Decision()))

        solver._undo_and_return_latest_event_at_current_decision_level()

        self.assertTrue(solver.state.set_literal(Lit.leq(A, 1),
                                                 Causes.Decision()))        

        self.assertEqual(solver.state.set_literal(Lit.leq(A, 0),
                                                  Causes.Decision()),
                         InvalidBoundUpdate(Lit.leq(A, 0),
                                            Causes.Decision()))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_optional_vars_set_literal(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=False)

        # NOTE: we do not use `add_new_presence_variable` because we
        # do not need "advanced" scope managemenet for the purposes of
        # this test. (we're testing things by hand here).

        P1 = solver.add_new_non_optional_variable((0, 1), True)
        P1lit = Lit.geq(P1, 1)
        solver.state.register_non_optional_vars_literals_implication(P1lit, TRUE_LIT)
        # The variable of P1 is always present.

        P2 = solver.add_new_non_optional_variable((0, 1), True)
        P2lit = Lit.geq(P2, 1)
        solver.state.register_non_optional_vars_literals_implication(P2lit, P1lit)
        # The variable of P2 is present when P1 is true (P1 acts as a scope literal)

        # A is present if P2 is true
        A = solver.add_new_optional_variable((0, 10), True, P2lit)

        # Reduce the domain of A equal to [5, 5].
        # This should have no consequences on P2 and P1
        self.assertEqual(solver.state.set_literal(Lit.leq(A, 5),
                                                  Causes.Decision()),
                         True)

        self.assertEqual(solver.state.set_literal(Lit.geq(A, 5),
                                                  Causes.Decision()),
                         True)

        self.assertEqual(solver.state.bound_of(SignedVar.minus(A)), -5)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(A)), 5)
        self.assertEqual(solver.state.bound_of(SignedVar.minus(P1)), 0)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(P1)), 1)
        self.assertEqual(solver.state.bound_of(SignedVar.minus(P2)), 0)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(P2)), 1)

        # Make the domain of A empty, this shuold imply that P2 is false
        solver.state.set_literal(Lit.geq(A, 6),
                                 Causes.Decision())

        self.assertEqual(solver.state.bound_of(SignedVar.minus(A)), -5)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(A)), 5)
        self.assertEqual(solver.state.bound_of(SignedVar.minus(P1)), 0)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(P1)), 1)
        self.assertEqual(solver.state.bound_of(SignedVar.minus(P2)), 0)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(P2)), 0)

        # Make P1 true, this should have no impact
        solver.state.set_literal(Lit.geq(P1, 1),
                                 Causes.Decision())

        self.assertEqual(solver.state.bound_of(SignedVar.minus(A)), -5)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(A)), 5)
        self.assertEqual(solver.state.bound_of(SignedVar.minus(P1)), -1)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(P1)), 1)
        self.assertEqual(solver.state.bound_of(SignedVar.minus(P2)), 0)
        self.assertEqual(solver.state.bound_of(SignedVar.plus(P2)), 0)

        # Make P2 have an empty domain, this should imply that P1
        # is false, which is a contradiction with out previous decision


        self.assertEqual(solver.state.set_literal(Lit.leq(P2, -1),
                                                  Causes.Decision()),
                        InvalidBoundUpdate(Lit.leq(P2, -1),
                                           Causes.Decision()))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_presence_relations(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=False)

        def always_present_together(A, B):
            return solver.state.presence_literal_of(A) == solver.state.presence_literal_of(B)

        # returns true if presence(A) => presence(B)
        def only_present_with(A, B):
            return solver.state.entails_implication(solver.state.presence_literal_of(A),
                                                    solver.state.presence_literal_of(B))

        P = solver.add_new_non_optional_variable((0,1), True)
        P1 = solver.add_new_optional_variable((0,1), True, Lit.geq(P, 1))
        P2 = solver.add_new_optional_variable((0,1), True, Lit.geq(P, 1))

        self.assertTrue(always_present_together(P1, P2))
        self.assertFalse(always_present_together(P, P1))
        self.assertFalse(always_present_together(P, P2))

        self.assertTrue(always_present_together(P, P))
        self.assertTrue(only_present_with(P, P))
        self.assertTrue(always_present_together(P1, P1))
        self.assertTrue(only_present_with(P1, P1))

        self.assertTrue(only_present_with(P1, P))
        self.assertTrue(only_present_with(P2, P))
        self.assertTrue(only_present_with(P1, P2))
        self.assertTrue(only_present_with(P2, P1))
        self.assertFalse(only_present_with(P, P1))
        self.assertFalse(only_present_with(P, P2))

        X = solver.add_new_non_optional_variable((0,1), True)
        X1 = solver.add_new_optional_variable((0,1), True, Lit.geq(X, 1))

        self.assertTrue(only_present_with(X1, X))
        self.assertFalse(only_present_with(X, X1))

        self.assertTrue(always_present_together(P, X))
        self.assertTrue(only_present_with(P1, X))
        self.assertTrue(only_present_with(X1, P))

        self.assertFalse(only_present_with(P1, X1))
        self.assertFalse(only_present_with(X1, P1))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_implications(self):
        
        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=False)

        A = solver.add_new_non_optional_variable((-10,10), True)
        B = solver.add_new_non_optional_variable((-10,10), True)
        C = solver.add_new_non_optional_variable((-10,10), True)

        # Part 1 : checking "obvious" implications, due to the current values of variables)

        self.assertTrue(solver.state.entails_implication(Lit.leq(A, 10), Lit.leq(B, 10)))
        self.assertFalse(solver.state.entails_implication(Lit.leq(A, 10), Lit.leq(B, 9)))
        self.assertTrue(solver.state.entails_implication(Lit.geq(A, 11), Lit.leq(B, 9)))
        self.assertFalse(solver.state.entails_implication(Lit.leq(A, 9), Lit.leq(B, 9)))

        # Part 2 : checking "obvious" "implicit" implications (like [A<=0] => [A<=1]).

        self.assertTrue(solver.state.entails_implication(Lit.leq(A,0), Lit.leq(A,0)))
        self.assertTrue(solver.state.entails_implication(Lit.leq(A,0), Lit.leq(A,1)))
        self.assertFalse(solver.state.entails_implication(Lit.leq(A,0), Lit.leq(B,0)))
        self.assertFalse(solver.state.entails_implication(Lit.leq(A,0), Lit.leq(A,-1)))

        # Part 3 : checking "unobvious" implications (both "explicit" and "implicit",
        # related to the "explicit" ones)

        solver.state.register_non_optional_vars_literals_implication(Lit.leq(A,1), Lit.leq(B,1))

        self.assertTrue(solver.state.entails_implication(Lit.leq(A,1), Lit.leq(B,1)))
        self.assertTrue(solver.state.entails_implication(Lit.leq(A,0), Lit.leq(B,1)))
        self.assertTrue(solver.state.entails_implication(Lit.leq(A,1), Lit.leq(B,2)))
        self.assertTrue(solver.state.entails_implication(Lit.leq(A,0), Lit.leq(B,2)))
        self.assertFalse(solver.state.entails_implication(Lit.leq(A,1), Lit.leq(B,0)))
        self.assertFalse(solver.state.entails_implication(Lit.leq(A,1), Lit.leq(B,0)))

        solver.state.register_non_optional_vars_literals_implication(Lit.leq(B,2), Lit.leq(C,2))

        self.assertTrue(solver.state.entails_implication(Lit.leq(A,1), Lit.leq(B,1)))
        self.assertTrue(solver.state.entails_implication(Lit.leq(A,1), Lit.leq(C,2)))
        self.assertTrue(solver.state.entails_implication(Lit.leq(A,1), Lit.leq(C,3)))
        self.assertFalse(solver.state.entails_implication(Lit.leq(A,1), Lit.leq(C,1)))
        self.assertTrue(solver.state.entails_implication(Lit.leq(A,0), Lit.leq(C,2)))
        self.assertFalse(solver.state.entails_implication(Lit.leq(A,2), Lit.leq(C,2)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_explanation(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=False)

        a = Lit.geq(solver.add_new_non_optional_variable((0,1), True), 1)
        b = Lit.geq(solver.add_new_non_optional_variable((0,1), True), 1)
        n = solver.add_new_non_optional_variable((0,10), True)

        # constraint 0: "a => (n <= 4)"
        # constraint 1: "b => (n >= 5)"
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
        def optional_domain(v):
            lb = -solver.state.bound_of(SignedVar.minus(v))
            ub = solver.state.bound_of(SignedVar.plus(v))

            if solver.state.entails(solver.state.presence_literal_of(v)):
                return (True, (lb, ub))
            elif solver.state.entails(solver.state.presence_literal_of(v).neg):
                return None
            else:
                return (False, (lb, ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def dummy_reasoner_explain(expl, lit, cause: Causes.ReasonerInference) -> None:
            if cause.inference_info == 0:
                self.assertEqual(lit, Lit.leq(n, 4))
                expl.append(a)
            elif cause.inference_info == 1:
                self.assertEqual(lit, Lit.geq(n, 5))
                expl.append(b)
            else:
                assert False

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        def propag():
            if solver.state.entails(a):
                res = solver.state.set_literal(Lit.leq(n, 4), Causes.ReasonerInference(0, 0))
                if isinstance(res, InvalidBoundUpdate):
                    return res
            if solver.state.entails(b):
                res = solver.state.set_literal(Lit.geq(n, 5), Causes.ReasonerInference(0, 1))
                if isinstance(res, InvalidBoundUpdate):
                    return res
            return None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        propag()

        solver.increment_decision_level_by_one()
        solver.state.set_literal(a, Causes.Decision())

        self.assertEqual((-solver.state.bound_of(SignedVar.minus(a.signed_var.var)),
                          solver.state.bound_of(SignedVar.plus(a.signed_var.var))),
                         (1, 1))

        propag()

        self.assertEqual(optional_domain(n), (True, (0,4)))

        solver.state.set_literal(Lit.geq(n, 1), Causes.Decision())

        solver.increment_decision_level_by_one()
        solver.state.set_literal(b, Causes.Decision())

        err = propag()
        if err is not None:
            clause_literals = \
                solver.explain_invalid_bound_update(err, dummy_reasoner_explain)    \
                    .asserting_clause
            # we have three rules
            #  -  !(n <= 4) || !(n >= 5)   (conflict)
            #  -  !a || (n <= 4)           (clause a)
            #  -  !b || (n >= 5)           (clause b)
            # Explanation should perform resolution of the first
            # and last rules for the literal (n >= 5):
            #   !(n <= 4) || !b
            #   !b || (n > 4)      (equivalent to previous)
            self.assertEqual(clause_literals, (Lit.geq(n, 5), b.neg))

        else:
            self.assertFalse(True)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_scoped_disjunction(self):
    # TODO: should be removed: we should test constraint addition and posting instead

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=False)

        def scoped_disj(clause_lits, scope_representative_lit):

            if scope_representative_lit == TRUE_LIT:
                return (clause_lits, scope_representative_lit)

            if len(clause_lits) == 0:
                return ((scope_representative_lit.neg,), TRUE_LIT)

            if all(solver.state.entails_implication(
                solver.state.presence_literal_of(l.signed_var.var), scope_representative_lit)
                for l in clause_lits
            ):
                return (clause_lits, scope_representative_lit)

            return (clause_lits+(scope_representative_lit.neg,), TRUE_LIT)
            
        PX = Lit.geq(solver.add_new_presence_variable(TRUE_LIT), 1)
        X1 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PX), 1)
        X2 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PX), 1)

        PY = Lit.geq(solver.add_new_presence_variable(TRUE_LIT), 1)

        PXY = \
            solver.state.get_scope_representative_literal( \
                solver.state._process_raw_required_presences_and_guards((PX, PY), (), True))
        XY = Lit.geq(solver.add_new_optional_variable((0, 1), True, PXY), 1)

        self.assertEqual(scoped_disj((X1,), PX), ((X1,), PX))

        self.assertEqual(scoped_disj((X1, X2), PX), ((X1, X2), PX))

        self.assertEqual(scoped_disj((XY,), PX), ((XY,), PX))

        self.assertEqual(scoped_disj((XY,), PY), ((XY,), PY))

        self.assertEqual(scoped_disj((XY,), PXY), ((XY,), PXY))

        self.assertEqual(scoped_disj((X1,), PXY), ((X1, PXY.neg), TRUE_LIT))

#################################################################################
