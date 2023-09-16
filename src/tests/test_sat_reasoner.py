from __future__ import annotations

#################################################################################

import unittest
from typing import Optional, Tuple

from src.fundamentals import TRUE_LIT, BoundVal, Lit, SignedVar, tighten_literals

from src.fundamentals import SignedVar, BoundVal, Lit, TRUE_LIT
from src.solver.common import Causes, ReasonerBaseExplanation
from src.solver.reasoners.sat_reasoner import SATReasoner
from src.solver.solver import Solver

#################################################################################

class TestSATReasonerBasics(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_simple(self):

        solver = Solver()
        sat_reasoner = SATReasoner()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_value_of(SignedVar.plus(var)) 
                == -solver.state.bound_value_of(SignedVar.minus(var))
            ):
                return solver.state.bound_value_of(SignedVar.plus(var))
            return None            

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,1), True)
        B = solver.add_new_non_optional_variable((0,1), True)

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)

        A_or_B = tighten_literals((Lit.geq(A, 1), Lit.geq(B, 1)))

        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B, TRUE_LIT)

        sat_reasoner.propagate(solver.state)

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)

        solver.state.set_literal(Lit.leq(A, 0), Causes.Decision())

        self.assertEqual(value_of_bool(A), 0)
        self.assertEqual(value_of_bool(B), None)

        sat_reasoner.propagate(solver.state)

        self.assertEqual(value_of_bool(A), 0)
        self.assertEqual(value_of_bool(B), 1)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_complex(self):

        solver = Solver()
        sat_reasoner = SATReasoner()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_value_of(SignedVar.plus(var)) 
                == -solver.state.bound_value_of(SignedVar.minus(var))
            ):
                return solver.state.bound_value_of(SignedVar.plus(var))
            return None            
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,1), True)
        B = solver.add_new_non_optional_variable((0,1), True)
        C = solver.add_new_non_optional_variable((0,1), True)
        D = solver.add_new_non_optional_variable((0,1), True)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [None, None, None, None])

        A_or_B_or_C_or_D = tighten_literals((Lit.geq(A, 1),
                                             Lit.geq(B, 1),
                                             Lit.geq(C, 1),
                                             Lit.geq(D, 1)))
        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B_or_C_or_D, TRUE_LIT)

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [None, None, None, None])

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Lit.leq(A, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, None, None, None])

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, None, None, None])

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Lit.leq(B, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Lit.geq(C, 1), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, 0, 1, None])

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, 0, 1, None])

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Lit.leq(D, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, 0, 1, 0])

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)],
                         [0, 0, 1, 0])

        solver.backtrack_to_decision_level(solver.state.decision_level-1,
                                           (sat_reasoner,))

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 1, None])

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 1, None])

        solver.backtrack_to_decision_level(solver.state.decision_level-1,
                                           (sat_reasoner,))

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Lit.leq(C, 0), Causes.Decision())

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 0, None])

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 0, 1])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation_failure(self):

        solver = Solver()
        sat_reasoner = SATReasoner()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_value_of(SignedVar.plus(var)) 
                == -solver.state.bound_value_of(SignedVar.minus(var))
            ):
                return solver.state.bound_value_of(SignedVar.plus(var))
            return None            

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,1), True)
        B = solver.add_new_non_optional_variable((0,1), True)

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)

        A_or_B = tighten_literals((Lit.geq(A, 1), Lit.geq(B, 1)))

        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B, TRUE_LIT)

        sat_reasoner.propagate(solver.state)

        self.assertEqual(value_of_bool(A), None)
        self.assertEqual(value_of_bool(B), None)

        solver.state.set_literal(Lit.leq(A, 0), Causes.Decision())

        solver.state.set_literal(Lit.leq(B, 0), Causes.Decision())

        self.assertEqual(value_of_bool(A), False)
        self.assertEqual(value_of_bool(B), False)

        self.assertIsInstance(sat_reasoner.propagate(solver.state), 
                              ReasonerBaseExplanation)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_int_propagation(self):

        solver = Solver()
        sat_reasoner = SATReasoner()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_int(var) -> Tuple[int, int]:
            return (-solver.state.bound_value_of(SignedVar.minus(var)),
                    solver.state.bound_value_of(SignedVar.plus(var)))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0,10), True)
        B = solver.add_new_non_optional_variable((0,10), True)
        C = solver.add_new_non_optional_variable((0,10), True)
        D = solver.add_new_non_optional_variable((0,10), True)

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(0,10), (0,10), (0,10), (0,10)])

        clause1_literals = tighten_literals((Lit.leq(A, 5), Lit.leq(B, 5)))
        clause2_literals = tighten_literals((Lit.geq(C, 5), Lit.geq(D, 5)))

        sat_reasoner.add_new_fixed_clause_with_scope(clause1_literals, TRUE_LIT)
        sat_reasoner.add_new_fixed_clause_with_scope(clause2_literals, TRUE_LIT)

        sat_reasoner.propagate(solver.state)

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(0,10), (0,10), (0,10), (0,10)])

        # Lower bound changes

        solver.state.set_literal(Lit.geq(A, 4), Causes.Decision())

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)],
                             [(4,10), (0,10), (0,10), (0,10)])

        sat_reasoner.propagate(solver.state)

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(4,10), (0,10), (0,10), (0,10)])

        solver.state.set_literal(Lit.geq(A, 5), Causes.Decision())

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(5,10), (0,10), (0,10), (0,10)])
        
        sat_reasoner.propagate(solver.state)
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(5,10), (0,10), (0,10), (0,10)])

        # Trigger first clause

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Lit.geq(A, 6), Causes.Decision())

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(6,10), (0,10), (0,10), (0,10)])
        
        sat_reasoner.propagate(solver.state)
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(6,10), (0,5), (0,10), (0,10)])

        # Retrigger first clause with stronger literal

        solver.backtrack_to_decision_level(solver.state.decision_level-1, 
                                           (sat_reasoner,))

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(5,10), (0,10), (0,10), (0,10)])

        solver.state.set_literal(Lit.geq(A, 8), Causes.Decision())
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,10), (0,10), (0,10)])

        sat_reasoner.propagate(solver.state)
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,10), (0,10)])

        # Upper bound changes

        solver.state.set_literal(Lit.leq(C, 6), Causes.Decision())
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,6), (0,10)])
        
        sat_reasoner.propagate(solver.state)
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,6), (0,10)])

        solver.state.set_literal(Lit.leq(C, 5), Causes.Decision())
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,5), (0,10)])
        
        sat_reasoner.propagate(solver.state)
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,5), (0,10)])

        # Should trigger second clause
        
        solver.increment_one_decision_level((sat_reasoner,))

        solver.state.set_literal(Lit.leq(C, 4), Causes.Decision())

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,4), (0,10)])

        sat_reasoner.propagate(solver.state)

        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,4), (5,10)])

        # Retrigger second clause with stronger literal

        solver.backtrack_to_decision_level(solver.state.decision_level-1, 
                                           (sat_reasoner,))
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,5), (0,10)])
        
        solver.state.set_literal(Lit.leq(C, 2), Causes.Decision())
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,2), (0,10)])
        
        sat_reasoner.propagate(solver.state)
        
        self.assertListEqual([value_of_int(v) for v in (A,B,C,D)], 
                             [(8,10), (0,5), (0,2), (5,10)])

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

class TestSATReasonerClauses(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_online_clause_insertion(self):

        solver = Solver()
        sat_reasoner = SATReasoner()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_value_of(SignedVar.plus(var)) 
                == -solver.state.bound_value_of(SignedVar.minus(var))
            ):
                return solver.state.bound_value_of(SignedVar.plus(var))
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

        A_or_B_or_C_or_D = tighten_literals((Lit.geq(A, 1),
                                             Lit.geq(B, 1),
                                             Lit.geq(C, 1), 
                                             Lit.geq(D, 1)))

        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B_or_C_or_D, TRUE_LIT)

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        notA_or_notB = tighten_literals((Lit.leq(A, 0), Lit.leq(B, 0)))

        sat_reasoner.add_new_fixed_clause_with_scope(notA_or_notB, TRUE_LIT)

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        notA_or_B = tighten_literals((Lit.leq(A, 0), Lit.geq(B, 1)))

        sat_reasoner.add_new_fixed_clause_with_scope(notA_or_B, TRUE_LIT)

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, None, None])

        A_or_B_or_notC = tighten_literals((Lit.geq(A, 1), 
                                           Lit.geq(B, 1), 
                                           Lit.leq(C, 0)))

        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B_or_notC, TRUE_LIT)

        sat_reasoner.propagate(solver.state)

        self.assertEqual([value_of_bool(v) for v in (A,B,C,D)], 
                         [0, 0, 0, 1])

        A_or_B_or_C_or_notD = tighten_literals((Lit.geq(A, 1), 
                                                Lit.geq(B, 1), 
                                                Lit.geq(C, 1), 
                                                Lit.leq(D, 0)))

        sat_reasoner.add_new_fixed_clause_with_scope(A_or_B_or_C_or_notD, TRUE_LIT)

        self.assertIsInstance(sat_reasoner.propagate(solver.state),
                              ReasonerBaseExplanation)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_scoped_clauses(self):

        solver = Solver()
        sat_reasoner = SATReasoner()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of_bool(var) -> Optional[int]:
            if (solver.state.bound_value_of(SignedVar.plus(var)) 
                == -solver.state.bound_value_of(SignedVar.minus(var))
            ):
                return solver.state.bound_value_of(SignedVar.plus(var))
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

            first_implying_ev = solver.state.first_event_entailing(lit)

            if first_implying_ev is None:
                return []

            expl_lits = []
            match first_implying_ev.cause:

                case Causes.ReasonerInference():
                    # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => literal
                    sat_reasoner.explain(expl_lits, lit, first_implying_ev.cause, solver.state)

                case Causes.ImplicationPropagation():
                    expl_lits.append(first_implying_ev.cause.literal)

                case Causes.EmptyDomain():
                    expl_lits.append(first_implying_ev.cause.literal.negated)

                    match first_implying_ev.cause.cause:

                        case Causes.ReasonerInference():
                            # Ask the reasoner for an explanation clause (l_1 & ... & l_n) => cause.literal
                            sat_reasoner.explain(expl_lits, first_implying_ev.cause.literal, first_implying_ev.cause.cause, solver.state)

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
            solver.state._get_or_make_new_scope_lit_from_conjunction( \
                solver.state._process_raw_required_presences_and_guards((PX, PY), (), True))

        Z1 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PZ), 1)
        Z2 = Lit.geq(solver.add_new_optional_variable((0, 1), True, PZ), 1)

        sat_reasoner.add_new_fixed_clause_with_scope((X1, X2), PX)

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(X1.negated, Causes.Decision())

        sat_reasoner.propagate(solver.state)

        self.assertTrue(solver.state.is_entailed(X2))
        self.assertIsNone(value_of_bool(PX.signed_var.var))

        self.assertListEqual(implying_literals(X2), [X1.negated])

        sat_reasoner.add_new_fixed_clause_with_scope((Y2.negated, Y1), PY)
        sat_reasoner.add_new_fixed_clause_with_scope((Y2.negated, Y1.negated), PY)

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Y2, Causes.Decision())

        sat_reasoner.propagate(solver.state)

        self.assertListEqual(implying_literals(PY.negated), [Y2, Y1]) # note: could be be Y1.negated as well depending on propagation order.

        solver.backtrack_to_decision_level(0, (sat_reasoner,))
        solver.increment_one_decision_level((sat_reasoner,))

        sat_reasoner.add_new_fixed_clause_with_scope((Y1, Y2), PY)

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Y1.negated, Causes.Decision())

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Y2.negated, Causes.Decision())

        sat_reasoner.propagate(solver.state)

        self.assertListEqual(implying_literals(PY.negated), [Y1.negated, Y2.negated])

        solver.backtrack_to_decision_level(0, (sat_reasoner,))
        solver.increment_one_decision_level((sat_reasoner,))

        sat_reasoner.add_new_fixed_clause_with_scope((Z1, Z2), PZ)

        solver.increment_one_decision_level((sat_reasoner,))        
        solver.state.set_literal(PZ, Causes.Decision())
        
        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Z1.negated, Causes.Decision())

        solver.increment_one_decision_level((sat_reasoner,))
        solver.state.set_literal(Z2.negated, Causes.Decision())

        self.assertIsInstance(sat_reasoner.propagate(solver.state),
                              ReasonerBaseExplanation)

#################################################################################
