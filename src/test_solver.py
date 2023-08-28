from __future__ import annotations

#################################################################################

from typing import Tuple, List

from fundamentals import (
    SignedVar, BoundVal, Lit, TRUE_LIT,
    ConstraintExpression,
)

from solver import SolverCauses, SolverConflictInfo, Solver, SolverDecisions
from solver_sat_reasoner import SATReasoner

from solver_api import (
    add_new_non_optional_variable,
    add_new_optional_variable,
    add_new_presence_variable,
    add_constraint,
    _insert_implication_between_literals_on_non_optional_vars,
    _insert_new_conjunctive_scope,
)

import unittest

#################################################################################

class TestSolverImplications(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

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
            [Bleq1])

        _insert_implication_between_literals_on_non_optional_vars(solver, Bleq1, Cleq1)
        self.assertEqual(
            solver.get_literals_directly_implied_by(Bleq1),
            [Cleq1])

        # We have Aleq1 => Bleq1 and Bleq1 => Cleq1,
        # so we also have Aleq1 => Cleq1. However, this is 
        # not a "direct" implication, as Cleq1 isn't explicitly
        # added to the adjacency set "guarded" by 1 of signed
        # variable A-.
        self.assertNotIn(
            Cleq1,
            solver.get_literals_directly_implied_by(Aleq1))

        # However, solver.is_Lit_implying(Aleq1, Cleq1)
        # returns True, as it should.
        self.assertEqual(
            solver._is_implication_true(Aleq1, Cleq1),
            True)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

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

        self.assertTrue(solver._is_implication_true(Aleq0, Aleq0))
        self.assertTrue(solver._is_implication_true(Aleq0, Aleq1))
        self.assertFalse(solver._is_implication_true(Aleq0, Bleq0))
        self.assertFalse(solver._is_implication_true(Aleq0, AleqM1))

        _insert_implication_between_literals_on_non_optional_vars(solver, Aleq1, Bleq1)

        self.assertTrue(solver._is_implication_true(Aleq1, Bleq1))
        self.assertTrue(solver._is_implication_true(Aleq0, Bleq1))
        self.assertTrue(solver._is_implication_true(Aleq1, Bleq2))
        self.assertTrue(solver._is_implication_true(Aleq0, Bleq2))
        self.assertFalse(solver._is_implication_true(Aleq1, Bleq0))
        self.assertFalse(solver._is_implication_true(Aleq1, Bleq0))

        _insert_implication_between_literals_on_non_optional_vars(solver, Bleq2, Cleq2)

        self.assertTrue(solver._is_implication_true(Aleq1, Bleq1))
        self.assertTrue(solver._is_implication_true(Aleq1, Cleq2))
        self.assertTrue(solver._is_implication_true(Aleq1, Cleq3))
        self.assertFalse(solver._is_implication_true(Aleq1, Cleq1))
        self.assertTrue(solver._is_implication_true(Aleq0, Cleq2))
        self.assertFalse(solver._is_implication_true(Aleq2, Cleq2))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

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

        self.assertFalse(solver._is_implication_true(Aleq0, Cleq0))

#################################################################################

class TestSolverSetBounds(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_non_optional_variables(self):
        solver = Solver()

        A = add_new_non_optional_variable(solver, (0, 10), True)
        AP, AM = SignedVar(A, True), SignedVar(A, False)

        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(1), SolverCauses.Decision()),
            False)
        
        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(0), SolverCauses.Decision()),
            False)
        
        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(-1), SolverCauses.Decision()),
            True)

        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(11), SolverCauses.Decision()),
            False)

        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(10), SolverCauses.Decision()),
            False)

        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(9), SolverCauses.Decision()),
            True)

        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(-9), SolverCauses.Decision()),
            True)

        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(-10), SolverCauses.Decision()),
            SolverConflictInfo.InvalidBoundUpdate(Lit(AM, BoundVal(-10)), SolverCauses.Decision()))

        solver._undo_and_return_last_event_at_current_decision_level()

        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(1), SolverCauses.Decision()),
            True)

        self.assertEqual(
            solver.set_bound_value(AP, BoundVal(0), SolverCauses.Decision()),
            SolverConflictInfo.InvalidBoundUpdate(Lit(AP, BoundVal(0)), SolverCauses.Decision()))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

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
            True)

        self.assertEqual(
            solver.set_bound_value(AM, BoundVal(-5), SolverCauses.Decision()),
            True)

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
            SolverConflictInfo.InvalidBoundUpdate)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_presence_relations(self):
        solver = Solver()

        def always_present_together(A, B):
            return solver.vars_presence_literals[A] == solver.vars_presence_literals[B]

        # returns true if presence(A) => presence(B)
        def only_present_with(A, B):
            return solver.is_implication_true(solver.vars_presence_literals[A], solver.vars_presence_literals[B])

        P = add_new_non_optional_variable(solver, (0,1), True)
        P1 = add_new_optional_variable(solver, (0,1), True, Lit.geq(P, 1))
        P2 = add_new_optional_variable(solver, (0,1), True, Lit.geq(P, 1))

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

        X = add_new_non_optional_variable(solver, (0,1), True)
        X1 = add_new_optional_variable(solver, (0,1), True, Lit.geq(X, 1))

        self.assertTrue(only_present_with(X1, X))
        self.assertFalse(only_present_with(X, X1))

        self.assertTrue(always_present_together(P, X))
        self.assertTrue(only_present_with(P1, X))
        self.assertTrue(only_present_with(X1, P))

        self.assertFalse(only_present_with(P1, X1))
        self.assertFalse(only_present_with(X1, P1))

#################################################################################

class TestSolverEntails(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

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

class TestSolverExplanation(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_explanation(self):
        solver = Solver()

        def optional_domain(v):
            (lb, ub) =  (-solver.bound_values[SignedVar(v, False)], solver.bound_values[SignedVar(v, True)])
            prez = solver.vars_presence_literals[v]
            if solver.is_literal_entailed(prez):
                return (True, (lb, ub))
            elif solver.is_literal_entailed(prez.negation()):
                return None
            else:
                return (False, (lb, ub))

        a = Lit.geq(add_new_non_optional_variable(solver, (0,1), True), 1)
        b = Lit.geq(add_new_non_optional_variable(solver, (0,1), True), 1)
        n = add_new_non_optional_variable(solver, (0,10), True)

        # constraint 0: "a => (n <= 4)"
        # constraint 1: "b => (n >= 5)"

        sat_reasoner = SATReasoner()    # dummy
        cause_a = SolverCauses.ReasonerInference(sat_reasoner, 0)
        cause_b = SolverCauses.ReasonerInference(sat_reasoner, 1)
        
        def propag():
            if solver.is_literal_entailed(a):
                res = solver.set_bound_value(SignedVar(n, True), BoundVal(4), cause_a)
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
            if solver.is_literal_entailed(b):
                res = solver.set_bound_value(SignedVar(n, False), BoundVal(-5), cause_b)
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
            return None

        def explain(expl:List[Lit], lit: Lit, cause: SolverCauses.ReasonerInference, _:Solver) -> None:
            if cause.inference_info == 0:
                self.assertEqual(lit, Lit.leq(n, 4))
                expl.append(a)
            elif cause.inference_info == 1:
                self.assertEqual(lit, Lit.geq(n, 5))
                expl.append(b)
            else:
                assert False

        propag()
        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(a),
            (sat_reasoner,))
        self.assertTupleEqual(
            (-solver.bound_values[SignedVar(a.signed_var.var, False)], solver.bound_values[SignedVar(a.signed_var.var, True)]),
            (1, 1))

        propag()
        self.assertEqual(optional_domain(n), (True, (0,4)))

        solver.set_bound_value(SignedVar(n, False), BoundVal(-1), SolverCauses.Decision())

        solver.increment_decision_level_and_perform_set_literal_decision(
            SolverDecisions.SetLiteral(b),
            (sat_reasoner,))

        err = propag()
        if err is None:
            self.assertFalse(True)
        else:
            clause_literals = solver.explain_invalid_bound_update(err, explain).asserting_clause_literals

            # we have three rules
            #  -  !(n <= 4) || !(n >= 5)   (conflict)
            #  -  !a || (n <= 4)           (clause a)
            #  -  !b || (n >= 5)           (clause b)
            # Explanation should perform resolution of the first and last rules for the literal (n >= 5):
            #   !(n <= 4) || !b
            #   !b || (n > 4)      (equivalent to previous)
            self.assertEqual(clause_literals, (b.negation(), Lit.geq(n, 5)))

#################################################################################

class TestSolverScopes(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_scoped_disjunction(self):
        solver = Solver()

        def get_conjunctive_scope_literal_trivial_case(conj_scope_lits):
            lit = Lit.geq(add_new_non_optional_variable(solver, (0,1), True), 1)
            lits = [lit]
            for l in conj_scope_lits:
                _insert_implication_between_literals_on_non_optional_vars(solver, lit, l)
                lits.append(l.negation())
            add_constraint(solver,
                ConstraintExpression.Or(tuple(lits)),
                ())
            _insert_new_conjunctive_scope(solver, conj_scope_lits, lit)
            return lit

        def scoped_disj(clause_lits: Tuple[Lit,...], scope: Lit):
            if scope == TRUE_LIT:
                return (clause_lits, scope)
            if len(clause_lits) == 0:
                return ((scope.negation(),), TRUE_LIT)
            if all(solver.is_implication_true(solver.vars_presence_literals[l.signed_var.var], scope) for l in clause_lits):
                return (clause_lits, scope)
            return (clause_lits+(scope.negation(),), TRUE_LIT)
            
        PX = Lit.geq(add_new_presence_variable(solver, TRUE_LIT), 1)
        X1 = Lit.geq(add_new_optional_variable(solver, (0, 1), True, PX), 1)
        X2 = Lit.geq(add_new_optional_variable(solver, (0, 1), True, PX), 1)

        PY = Lit.geq(add_new_presence_variable(solver, TRUE_LIT), 1)

        PXY = get_conjunctive_scope_literal_trivial_case((PX, PY))
        XY = Lit.geq(add_new_optional_variable(solver, (0, 1), True, PXY), 1)

        self.assertTupleEqual(
            scoped_disj((X1,), PX),
            ((X1,), PX))
        self.assertTupleEqual(
            scoped_disj((X1,X2), PX),
            ((X1,X2), PX))
        self.assertTupleEqual(
            scoped_disj((XY,), PX),
            ((XY,), PX))
        self.assertTupleEqual(
            scoped_disj((XY,), PY),
            ((XY,), PY))
        self.assertTupleEqual(
            scoped_disj((XY,), PXY),
            ((XY,), PXY))
        self.assertTupleEqual(
            scoped_disj((X1,), PXY),
            ((X1, PXY.negation()), TRUE_LIT))

#################################################################################

if __name__ == '__main__':
    unittest.main()
