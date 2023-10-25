from __future__ import annotations

#################################################################################

import unittest
from typing import Optional, Tuple

from src.fundamentals import TRUE_LIT, Bound, Lit, SignedVar, simplify_lits_disjunction

from src.fundamentals import SignedVar, Bound, Lit, TRUE_LIT
from src.solver.common import Causes, ReasonerBaseExplanation
from src.solver.reasoners.sat_reasoner import SATReasoner
from src.solver.solver import Solver

#################################################################################

class TestSATReasonerBasics(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_simple(self):

        solver = Solver(use_sat_reasoner=True,
                        use_diff_reasoner=False)

        assert solver.sat_reasoner is not None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_of(SignedVar.plus(var)) 
                == -solver.state.bound_of(SignedVar.minus(var))
            ):
                return solver.state.bound_of(SignedVar.plus(var))
            return None            

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,1), True)
        B = solver.add_new_non_optional_variable((0,1), True)

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)

        A_or_B = simplify_lits_disjunction((Lit.geq(A, 1), Lit.geq(B, 1)))

        solver.sat_reasoner.add_new_fixed_scoped_clause(A_or_B, TRUE_LIT)

        solver.sat_reasoner.propagate()

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)

        solver.state.set_literal(Lit.leq(A, 0), Causes.Decision())

        self.assertEqual(value_of_bool(A), 0)
        self.assertEqual(value_of_bool(B), None)

        solver.sat_reasoner.propagate()

        self.assertEqual(value_of_bool(A), 0)
        self.assertEqual(value_of_bool(B), 1)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_complex(self):

        solver = Solver(use_sat_reasoner=True,
                        use_diff_reasoner=False)

        assert solver.sat_reasoner is not None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_of(SignedVar.plus(var)) 
                == -solver.state.bound_of(SignedVar.minus(var))
            ):
                return solver.state.bound_of(SignedVar.plus(var))
            return None            
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,1), True)
        B = solver.add_new_non_optional_variable((0,1), True)
        C = solver.add_new_non_optional_variable((0,1), True)
        D = solver.add_new_non_optional_variable((0,1), True)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [None, None, None, None])

        A_or_B_or_C_or_D = simplify_lits_disjunction((Lit.geq(A, 1),
                                                      Lit.geq(B, 1),
                                                      Lit.geq(C, 1),
                                                      Lit.geq(D, 1)))
        solver.sat_reasoner.add_new_fixed_scoped_clause(A_or_B_or_C_or_D, TRUE_LIT)

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [None, None, None, None])

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Lit.leq(A, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, None, None, None])

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, None, None, None])

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Lit.leq(B, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Lit.geq(C, 1), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, 0, 1, None])

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, 0, 1, None])

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Lit.leq(D, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, 0, 1, 0])

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, 0, 1, 0])

        solver.backtrack_to_decision_level(solver.state.decision_level-1,
                                           )

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 1, None])

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 1, None])

        solver.backtrack_to_decision_level(solver.state.decision_level-1,
                                           )

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Lit.leq(C, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 0, None])

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 0, 1])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_failure(self):

        solver = Solver(use_sat_reasoner=True,
                        use_diff_reasoner=False)

        assert solver.sat_reasoner is not None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_of(SignedVar.plus(var)) 
                == -solver.state.bound_of(SignedVar.minus(var))
            ):
                return solver.state.bound_of(SignedVar.plus(var))
            return None            

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,1), True)
        B = solver.add_new_non_optional_variable((0,1), True)

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)

        A_or_B = simplify_lits_disjunction((Lit.geq(A, 1), Lit.geq(B, 1)))

        solver.sat_reasoner.add_new_fixed_scoped_clause(A_or_B, TRUE_LIT)

        solver.sat_reasoner.propagate()

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)

        solver.state.set_literal(Lit.leq(A, 0), Causes.Decision())

        solver.state.set_literal(Lit.leq(B, 0), Causes.Decision())

        self.assertEqual(value_of_bool(A), False)
        self.assertEqual(value_of_bool(B), False)

        self.assertIsInstance(solver.sat_reasoner.propagate(), 
                              ReasonerBaseExplanation)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_int_propagation(self):

        solver = Solver(use_sat_reasoner=True,
                        use_diff_reasoner=False)

        assert solver.sat_reasoner is not None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_int(var) -> Tuple[int, int]:
            return (-solver.state.bound_of(SignedVar.minus(var)),
                    solver.state.bound_of(SignedVar.plus(var)))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,10), True)
        B = solver.add_new_non_optional_variable((0,10), True)
        C = solver.add_new_non_optional_variable((0,10), True)
        D = solver.add_new_non_optional_variable((0,10), True)

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(0,10), (0,10), (0,10), (0,10)])

        clause1_literals = simplify_lits_disjunction((Lit.leq(A, 5), Lit.leq(B, 5)))
        clause2_literals = simplify_lits_disjunction((Lit.geq(C, 5), Lit.geq(D, 5)))

        solver.sat_reasoner.add_new_fixed_scoped_clause(clause1_literals, TRUE_LIT)
        solver.sat_reasoner.add_new_fixed_scoped_clause(clause2_literals, TRUE_LIT)

        solver.sat_reasoner.propagate()

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(0,10), (0,10), (0,10), (0,10)])

        # Lower bound changes

        solver.state.set_literal(Lit.geq(A, 4), Causes.Decision())

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)],
                             [(4,10), (0,10), (0,10), (0,10)])

        solver.sat_reasoner.propagate()

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(4,10), (0,10), (0,10), (0,10)])

        solver.state.set_literal(Lit.geq(A, 5), Causes.Decision())

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(5,10), (0,10), (0,10), (0,10)])
        
        solver.sat_reasoner.propagate()
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(5,10), (0,10), (0,10), (0,10)])

        # Trigger first clause

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Lit.geq(A, 6), Causes.Decision())

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(6,10), (0,10), (0,10), (0,10)])
        
        solver.sat_reasoner.propagate()
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(6,10), (0,5), (0,10), (0,10)])

        # Retrigger first clause with stronger literal

        solver.backtrack_to_decision_level(solver.state.decision_level-1, 
                                           )

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(5,10), (0,10), (0,10), (0,10)])

        solver.state.set_literal(Lit.geq(A, 8), Causes.Decision())
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,10), (0,10), (0,10)])

        solver.sat_reasoner.propagate()
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,10), (0,10)])

        # Upper bound changes

        solver.state.set_literal(Lit.leq(C, 6), Causes.Decision())
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,6), (0,10)])
        
        solver.sat_reasoner.propagate()
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,6), (0,10)])

        solver.state.set_literal(Lit.leq(C, 5), Causes.Decision())
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,5), (0,10)])
        
        solver.sat_reasoner.propagate()
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,5), (0,10)])

        # Should trigger second clause
        
        solver.increment_decision_level_by_one()

        solver.state.set_literal(Lit.leq(C, 4), Causes.Decision())

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,4), (0,10)])

        solver.sat_reasoner.propagate()

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,4), (5,10)])

        # Retrigger second clause with stronger literal

        solver.backtrack_to_decision_level(solver.state.decision_level-1, 
                                           )
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,5), (0,10)])
        
        solver.state.set_literal(Lit.leq(C, 2), Causes.Decision())
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,2), (0,10)])
        
        solver.sat_reasoner.propagate()
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,2), (5,10)])

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

class TestSATReasonerClauses(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_online_clause_insertion(self):

        solver = Solver(use_sat_reasoner=True,
                        use_diff_reasoner=False)

        assert solver.sat_reasoner is not None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_of(SignedVar.plus(var)) 
                == -solver.state.bound_of(SignedVar.minus(var))
            ):
                return solver.state.bound_of(SignedVar.plus(var))
            return None            

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,1), True)
        B = solver.add_new_non_optional_variable((0,1), True)
        C = solver.add_new_non_optional_variable((0,1), True)
        D = solver.add_new_non_optional_variable((0,1), True)

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)
        self.assertEqual(value_of_bool(C), None)
        self.assertEqual(value_of_bool(D), None)

        # not A and not B
        solver.state.set_literal(Lit.leq(A, 0), Causes.Decision())
        solver.state.set_literal(Lit.leq(B, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        A_or_B_or_C_or_D = simplify_lits_disjunction((Lit.geq(A, 1),
                                                      Lit.geq(B, 1),
                                                      Lit.geq(C, 1), 
                                                      Lit.geq(D, 1)))

        solver.sat_reasoner.add_new_fixed_scoped_clause(A_or_B_or_C_or_D, TRUE_LIT)

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        notA_or_notB = simplify_lits_disjunction((Lit.leq(A, 0), Lit.leq(B, 0)))

        solver.sat_reasoner.add_new_fixed_scoped_clause(notA_or_notB, TRUE_LIT)

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        notA_or_B = simplify_lits_disjunction((Lit.leq(A, 0), Lit.geq(B, 1)))

        solver.sat_reasoner.add_new_fixed_scoped_clause(notA_or_B, TRUE_LIT)

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        A_or_B_or_notC = simplify_lits_disjunction((Lit.geq(A, 1), 
                                                    Lit.geq(B, 1), 
                                                    Lit.leq(C, 0)))

        solver.sat_reasoner.add_new_fixed_scoped_clause(A_or_B_or_notC, TRUE_LIT)

        solver.sat_reasoner.propagate()

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 0, 1])

        A_or_B_or_C_or_notD = simplify_lits_disjunction((Lit.geq(A, 1), 
                                                         Lit.geq(B, 1), 
                                                         Lit.geq(C, 1), 
                                                         Lit.leq(D, 0)))

        solver.sat_reasoner.add_new_fixed_scoped_clause(A_or_B_or_C_or_notD, TRUE_LIT)

        self.assertIsInstance(solver.sat_reasoner.propagate(),
                              ReasonerBaseExplanation)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_scoped_clauses(self):

        solver = Solver(use_sat_reasoner=True,
                        use_diff_reasoner=False)

        assert solver.sat_reasoner is not None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_of(SignedVar.plus(var)) 
                == -solver.state.bound_of(SignedVar.minus(var))
            ):
                return solver.state.bound_of(SignedVar.plus(var))
            return None            

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        # For a literal `l` that is true in the current state,
        # returns a list of entailing literals `l_1 ... l_n` that
        # forms an explanation `(l_1 & ... l_n) => l`.
        # Returns None if the literal is a decision.
        # 
        # Limitation: differently from the explanations provided in
        # the main clause construction loop, the explanation will
        # not be built in the exact state where the inference was
        # made (which might be problematic for some reasoners).
        def implying_literals(lit):

            assert solver.sat_reasoner is not None

            first_implying_ev = solver.state.get_first_event_entailing(lit)

            if first_implying_ev is None:
                return []

            expl_lits = []
            match first_implying_ev.cause:

                case Causes.ReasonerInference():
                    # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => literal
                    solver.sat_reasoner.explain(expl_lits, lit, first_implying_ev.cause)

                case Causes.ImplicationPropagation():
                    expl_lits.append(first_implying_ev.cause.literal)

                case Causes.EmptyDomain():
                    expl_lits.append(first_implying_ev.cause.literal.neg)

                    match first_implying_ev.cause.cause:

                        case Causes.ReasonerInference():
                            # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => cause.literal
                            solver.sat_reasoner.explain(expl_lits, first_implying_ev.cause.literal, first_implying_ev.cause.cause)

                        case Causes.ImplicationPropagation():
                            expl_lits.append(first_implying_ev.cause.cause.literal)
                        
                        case _:
                            assert False

                case _:
                    assert False

            return expl_lits

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        PX = Lit.geq(solver.add_new_presence_variable(TRUE_LIT), 1)
        X1 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PX), 1)
        X2 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PX), 1)

        PY = Lit.geq(solver.add_new_presence_variable(TRUE_LIT), 1)
        Y1 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PY), 1)
        Y2 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PY), 1)

        PZ = \
            solver.state.get_scope_representative_literal( \
                solver.state._process_raw_required_presences_and_guards((PX, PY), (), True))

        Z1 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PZ), 1)
        Z2 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PZ), 1)

        solver.sat_reasoner.add_new_fixed_scoped_clause((X1, X2), PX)

        solver.increment_decision_level_by_one()
        solver.state.set_literal(X1.neg, Causes.Decision())

        solver.sat_reasoner.propagate()

        self.assertTrue(solver.state.entails(X2))
        self.assertIsNone(value_of_bool(PX.signed_var.var))

        self.assertListEqual(implying_literals(X2), [X1.neg])

        solver.sat_reasoner.add_new_fixed_scoped_clause((Y2.neg, Y1), PY)
        solver.sat_reasoner.add_new_fixed_scoped_clause((Y2.neg, Y1.neg), PY)

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Y2, Causes.Decision())

        solver.sat_reasoner.propagate()

        self.assertListEqual(implying_literals(PY.neg), [Y2, Y1]) # note: could be be Y1.negated as well depending on propagation order.

        solver.backtrack_to_decision_level(0)
        solver.increment_decision_level_by_one()

        solver.sat_reasoner.add_new_fixed_scoped_clause((Y1, Y2), PY)

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Y1.neg, Causes.Decision())

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Y2.neg, Causes.Decision())

        solver.sat_reasoner.propagate()

        self.assertListEqual(implying_literals(PY.neg), [Y1.neg, Y2.neg])

        solver.backtrack_to_decision_level(0,)
        solver.increment_decision_level_by_one()

        solver.sat_reasoner.add_new_fixed_scoped_clause((Z1, Z2), PZ)

        solver.increment_decision_level_by_one()        
        solver.state.set_literal(PZ, Causes.Decision())
        
        solver.increment_decision_level_by_one()
        solver.state.set_literal(Z1.neg, Causes.Decision())

        solver.increment_decision_level_by_one()
        solver.state.set_literal(Z2.neg, Causes.Decision())

        self.assertIsInstance(solver.sat_reasoner.propagate(),
                              ReasonerBaseExplanation)

#################################################################################
