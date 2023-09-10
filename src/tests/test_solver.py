from __future__ import annotations

#################################################################################

import unittest

from src.fundamentals import SignedVar, BoundVal, Lit, TRUE_LIT
from src.solver import Solver, Causes, InvalidBoundUpdateInfo, Reasoner

#################################################################################

from src.solver_api import (
    _insert_implication_between_literals_on_non_optional_vars,
    _get_or_make_new_scope_lit_from_scope_as_lits_conj,
    add_new_non_optional_variable,
    add_new_optional_variable,
    add_new_presence_variable,
)

#################################################################################

class TestSolverBasics(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_non_optional_vars_set_bound_values(self):

        solver = Solver()

        A = add_new_non_optional_variable((0, 10), True, solver)

        self.assertFalse(solver.set_bound_value(SignedVar.minus(A),
                                                BoundVal(1),
                                                Causes.Decision()))        

        self.assertFalse(solver.set_bound_value(SignedVar.minus(A),
                                                BoundVal(0),
                                                Causes.Decision()))
        
        self.assertTrue(solver.set_bound_value(SignedVar.minus(A),
                                               BoundVal(-1),
                                               Causes.Decision()))

        self.assertFalse(solver.set_bound_value(SignedVar.plus(A),
                                                BoundVal(11),
                                                Causes.Decision()))

        self.assertFalse(solver.set_bound_value(SignedVar.plus(A),
                                                BoundVal(10),
                                                Causes.Decision()))

        self.assertTrue(solver.set_bound_value(SignedVar.plus(A),
                                               BoundVal(9),
                                               Causes.Decision()))

        self.assertTrue(solver.set_bound_value(SignedVar.minus(A),
                                               BoundVal(-9),
                                               Causes.Decision()))

        self.assertEqual(solver.set_bound_value(SignedVar.minus(A),
                                               BoundVal(-10),
                                               Causes.Decision()),
                         InvalidBoundUpdateInfo(Lit.geq(A, 10), 
                                                Causes.Decision()))

        solver._undo_and_return_last_event_at_current_decision_level()

        self.assertTrue(solver.set_bound_value(SignedVar.plus(A),
                                               BoundVal(1),
                                               Causes.Decision()))

        self.assertEqual(solver.set_bound_value(SignedVar.plus(A),
                                               BoundVal(0),
                                               Causes.Decision()),
                         InvalidBoundUpdateInfo(Lit.leq(A, 0), 
                                                Causes.Decision()))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_optional_vars_set_bound_values(self):

        solver = Solver()

        # NOTE: we do not use `add_new_presence_variable` because we
        # do not need "advanced" scope managemenet for the purposes of
        # this test. (we're testing things by hand here).

        P1 = add_new_non_optional_variable((0, 1), True, solver)
        P1lit = Lit.geq(P1, 1)
        _insert_implication_between_literals_on_non_optional_vars(P1lit, TRUE_LIT, solver)
        # The variable of P1 is always present.

        P2 = add_new_non_optional_variable((0, 1), True, solver)
        P2lit = Lit.geq(P2, 1)
        _insert_implication_between_literals_on_non_optional_vars(P2lit, P1lit, solver)
        # The variable of P2 is present when P1 is true (P1 acts as a scope literal)

        # A is present if P2 is true
        A = add_new_optional_variable((0, 10), True, P2lit, solver)

        # Reduce the domain of A equal to [5, 5].
        # This should have no consequences on P2 and P1
        self.assertEqual(solver.set_bound_value(SignedVar.plus(A), 
                                                BoundVal(5), 
                                                Causes.Decision()),
                         True)

        self.assertEqual(solver.set_bound_value(SignedVar.minus(A), 
                                                BoundVal(-5), 
                                                Causes.Decision()),
                         True)

        self.assertEqual(solver.bound_values[SignedVar.minus(A)], -5)
        self.assertEqual(solver.bound_values[SignedVar.plus(A)], 5)
        self.assertEqual(solver.bound_values[SignedVar.minus(P1)], 0)
        self.assertEqual(solver.bound_values[SignedVar.plus(P1)], 1)
        self.assertEqual(solver.bound_values[SignedVar.minus(P2)], 0)
        self.assertEqual(solver.bound_values[SignedVar.plus(P2)], 1)

        # Make the domain of A empty, this shuold imply that P2 is false
        solver.set_bound_value(SignedVar.minus(A),
                               BoundVal(-6),
                               Causes.Decision())

        self.assertEqual(solver.bound_values[SignedVar.minus(A)], -5)
        self.assertEqual(solver.bound_values[SignedVar.plus(A)], 5)
        self.assertEqual(solver.bound_values[SignedVar.minus(P1)], 0)
        self.assertEqual(solver.bound_values[SignedVar.plus(P1)], 1)
        self.assertEqual(solver.bound_values[SignedVar.minus(P2)], 0)
        self.assertEqual(solver.bound_values[SignedVar.plus(P2)], 0)

        # Make P1 true, this should have no impact
        solver.set_bound_value(SignedVar.minus(P1),
                               BoundVal(-1),
                               Causes.Decision())

        self.assertEqual(solver.bound_values[SignedVar.minus(A)], -5)
        self.assertEqual(solver.bound_values[SignedVar.plus(A)], 5)
        self.assertEqual(solver.bound_values[SignedVar.minus(P1)], -1)
        self.assertEqual(solver.bound_values[SignedVar.plus(P1)], 1)
        self.assertEqual(solver.bound_values[SignedVar.minus(P2)], 0)
        self.assertEqual(solver.bound_values[SignedVar.plus(P2)], 0)

        # Make P2 have an empty domain, this should imply that P1
        # is false, which is a contradiction with out previous decision
        self.assertEqual(solver.set_bound_value(SignedVar.plus(P2),
                                                BoundVal(-1),
                                                Causes.Decision()),
                        InvalidBoundUpdateInfo(Lit.leq(P2,-1),
                                               Causes.Decision()))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_presence_relations(self):

        solver = Solver()

        def always_present_together(A, B):
            return solver.presence_literals[A] == solver.presence_literals[B]

        # returns true if presence(A) => presence(B)
        def only_present_with(A, B):
            return solver.is_implication_true(solver.presence_literals[A], solver.presence_literals[B])

        P = add_new_non_optional_variable((0,1), True, solver)
        P1 = add_new_optional_variable((0,1), True, Lit.geq(P, 1), solver)
        P2 = add_new_optional_variable((0,1), True, Lit.geq(P, 1), solver)

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

        X = add_new_non_optional_variable((0,1), True, solver)
        X1 = add_new_optional_variable((0,1), True, Lit.geq(X, 1), solver)

        self.assertTrue(only_present_with(X1, X))
        self.assertFalse(only_present_with(X, X1))

        self.assertTrue(always_present_together(P, X))
        self.assertTrue(only_present_with(P1, X))
        self.assertTrue(only_present_with(X1, P))

        self.assertFalse(only_present_with(P1, X1))
        self.assertFalse(only_present_with(X1, P1))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_implications(self):
        
        solver = Solver()

        A = add_new_non_optional_variable((-10,10), True, solver)
        B = add_new_non_optional_variable((-10,10), True, solver)
        C = add_new_non_optional_variable((-10,10), True, solver)

        # Part 1 : checking "obvious" implications, due to the current values of variables)

        self.assertTrue(solver.is_implication_true(Lit.leq(A, 10), Lit.leq(B, 10)))
        self.assertFalse(solver.is_implication_true(Lit.leq(A, 10), Lit.leq(B, 9)))
        self.assertTrue(solver.is_implication_true(Lit.geq(A, 11), Lit.leq(B, 9)))
        self.assertFalse(solver.is_implication_true(Lit.leq(A, 9), Lit.leq(B, 9)))

        # Part 2 : checking "obvious" "implicit" implications (like [A<=0] => [A<=1]).

        self.assertTrue(solver.is_implication_true(Lit.leq(A,0), Lit.leq(A,0)))
        self.assertTrue(solver.is_implication_true(Lit.leq(A,0), Lit.leq(A,1)))
        self.assertFalse(solver.is_implication_true(Lit.leq(A,0), Lit.leq(B,0)))
        self.assertFalse(solver.is_implication_true(Lit.leq(A,0), Lit.leq(A,-1)))

        # Part 3 : checking "unobvious" implications (both "explicit" and "implicit",
        # related to the "explicit" ones)

        _insert_implication_between_literals_on_non_optional_vars(Lit.leq(A,1),
                                                                  Lit.leq(B,1),
                                                                  solver)
        self.assertTrue(solver.is_implication_true(Lit.leq(A,1), Lit.leq(B,1)))
        self.assertTrue(solver.is_implication_true(Lit.leq(A,0), Lit.leq(B,1)))
        self.assertTrue(solver.is_implication_true(Lit.leq(A,1), Lit.leq(B,2)))
        self.assertTrue(solver.is_implication_true(Lit.leq(A,0), Lit.leq(B,2)))
        self.assertFalse(solver.is_implication_true(Lit.leq(A,1), Lit.leq(B,0)))
        self.assertFalse(solver.is_implication_true(Lit.leq(A,1), Lit.leq(B,0)))

        _insert_implication_between_literals_on_non_optional_vars(Lit.leq(B,2),
                                                                  Lit.leq(C,2),
                                                                  solver)
        self.assertTrue(solver.is_implication_true(Lit.leq(A,1), Lit.leq(B,1)))
        self.assertTrue(solver.is_implication_true(Lit.leq(A,1), Lit.leq(C,2)))
        self.assertTrue(solver.is_implication_true(Lit.leq(A,1), Lit.leq(C,3)))
        self.assertFalse(solver.is_implication_true(Lit.leq(A,1), Lit.leq(C,1)))
        self.assertTrue(solver.is_implication_true(Lit.leq(A,0), Lit.leq(C,2)))
        self.assertFalse(solver.is_implication_true(Lit.leq(A,2), Lit.leq(C,2)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class DummyReasoner(Reasoner):
        ...

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_explanation(self):

        solver = Solver()

        a = Lit.geq(add_new_non_optional_variable((0,1), True, solver), 1)
        b = Lit.geq(add_new_non_optional_variable((0,1), True, solver), 1)
        n = add_new_non_optional_variable((0,10), True, solver)

        # constraint 0: "a => (n <= 4)"
        # constraint 1: "b => (n >= 5)"

        dummy_reasoner = TestSolverBasics.DummyReasoner()

        cause_a = Causes.ReasonerInference(dummy_reasoner, 0)
        cause_b = Causes.ReasonerInference(dummy_reasoner, 1)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
        def optional_domain(v):
            lb = -solver.bound_values[SignedVar.minus(v)]
            ub = solver.bound_values[SignedVar.plus(v)]

            if solver.is_literal_entailed(solver.presence_literals[v]):
                return (True, (lb, ub))
            elif solver.is_literal_entailed(solver.presence_literals[v].negation()):
                return None
            else:
                return (False, (lb, ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def dummy_reasoner_explain(expl, lit, cause: Causes.ReasonerInference, _: Solver) -> None:
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
            if solver.is_literal_entailed(a):
                res = solver.set_bound_value(SignedVar.plus(n), BoundVal(4), cause_a)
                if isinstance(res, InvalidBoundUpdateInfo):
                    return res
            if solver.is_literal_entailed(b):
                res = solver.set_bound_value(SignedVar.minus(n), BoundVal(-5), cause_b)
                if isinstance(res, InvalidBoundUpdateInfo):
                    return res
            return None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        propag()

        solver.increment_decision_level(())
        solver.set_bound_value(a.signed_var, a.bound_value, Causes.Decision())

        self.assertEqual((-solver.bound_values[SignedVar.minus(a.signed_var.var)],
                          solver.bound_values[SignedVar.plus(a.signed_var.var)]),
                         (1, 1))

        propag()
        self.assertEqual(optional_domain(n), (True, (0,4)))

        solver.set_bound_value(SignedVar(n, False), BoundVal(-1), Causes.Decision())

        solver.increment_decision_level(())
        solver.set_bound_value(b.signed_var, b.bound_value, Causes.Decision())

        err = propag()
        if err is not None:
            clause_literals = solver.explain_invalid_bound_update(err, dummy_reasoner_explain).asserting_clause_literals
            # we have three rules
            #  -  !(n <= 4) || !(n >= 5)   (conflict)
            #  -  !a || (n <= 4)           (clause a)
            #  -  !b || (n >= 5)           (clause b)
            # Explanation should perform resolution of the first and last rules for the literal (n >= 5):
            #   !(n <= 4) || !b
            #   !b || (n > 4)      (equivalent to previous)
            self.assertEqual(clause_literals, (Lit.geq(n, 5), b.negation()))

        else:
            self.assertFalse(True)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_scoped_disjunction(self):
    # NOTE: should be removed: we should test constraint addition and posting instead

        solver = Solver()

        def scoped_disj(clause_lits, scope):
            if scope == TRUE_LIT:
                return (clause_lits, scope)
            if len(clause_lits) == 0:
                return ((scope.negation(),), TRUE_LIT)
            if all(solver.is_implication_true(solver.presence_literals[l.signed_var.var],
                                              scope)
                                              for l in clause_lits):
                return (clause_lits, scope)
            return (clause_lits+(scope.negation(),), TRUE_LIT)
            
        PX = Lit.geq(add_new_presence_variable(TRUE_LIT, solver), 1)
        X1 = Lit.geq(add_new_optional_variable((0, 1), True, PX, solver), 1)
        X2 = Lit.geq(add_new_optional_variable((0, 1), True, PX, solver), 1)

        PY = Lit.geq(add_new_presence_variable(TRUE_LIT, solver), 1)

        PXY = _get_or_make_new_scope_lit_from_scope_as_lits_conj((PX, PY), solver)
        XY = Lit.geq(add_new_optional_variable((0, 1), True, PXY, solver), 1)

        self.assertEqual(scoped_disj((X1,), PX), ((X1,), PX))

        self.assertEqual(scoped_disj((X1,X2), PX), ((X1,X2), PX))

        self.assertEqual(scoped_disj((XY,), PX), ((XY,), PX))

        self.assertEqual(scoped_disj((XY,), PY), ((XY,), PY))

        self.assertEqual(scoped_disj((XY,), PXY), ((XY,), PXY))

        self.assertEqual(scoped_disj((X1,), PXY), ((X1, PXY.negation()), TRUE_LIT))

#################################################################################
