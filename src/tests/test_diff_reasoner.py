from __future__ import annotations

#################################################################################

import unittest

from src.fundamentals import TRUE_LIT, BoundVal, Lit, SignedVar, Var
from src.solver.common import (Causes, InvalidBoundUpdateInfo,
                               ReasonerBaseExplanation)
from src.solver.reasoners.diff_reasoner import DiffReasoner
from src.solver.solver import Solver

#################################################################################

class TestDiffReasonerBasics(unittest.TestCase):
   
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_active_edge(self, 
        src: Var,
        tgt: Var,
        weight: int,
        solver: Solver,
    ) -> Lit:

        psrc, ptgt = solver.state.presence_literal_of(src), solver.state.presence_literal_of(tgt)

        valid_edge = solver.state._get_or_make_new_scope_lit_from_conjunction(
            solver.state._process_raw_required_presences_and_guards((psrc, ptgt), (), True))

        active_edge = solver.state._get_or_make_tautology_of_scope(valid_edge)

        assert solver.diff_reasoner is not None

        solver.diff_reasoner.add_reified_difference_constraint(active_edge, src, tgt, weight)
        return active_edge

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_inactive_edge(self,
        src: Var,
        tgt: Var,
        weight: int,
        solver: Solver,
    ) -> Lit:
        psrc, ptgt = solver.state.presence_literal_of(src), solver.state.presence_literal_of(tgt)
        
        valid_edge = solver.state._get_or_make_new_scope_lit_from_conjunction(
            solver.state._process_raw_required_presences_and_guards((psrc, ptgt), (), True))
        
        active_edge = Lit.geq(solver.add_new_optional_variable((0, 1), True, valid_edge), 1)
        
        assert solver.diff_reasoner is not None

        solver.diff_reasoner.add_reified_difference_constraint(active_edge, src, tgt, weight)
        return active_edge

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def add_delay(self, var1, var2, delay, solver):
        self.add_active_edge(var2, var1, -delay, solver)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def mark_edge_active(self, edge: Lit, solver: Solver):
        return solver.state.set_bound_value(edge.signed_var, edge.bound_value, Causes.Decision())

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def forward_dist(self, var, solver: Solver):
                
        dists = DiffReasoner.DijkstraState()
        assert solver.diff_reasoner is not None
        solver.diff_reasoner.distances_from(SignedVar.plus(var), dists)
        return { v.var: d for d, v in dists.reached_nodes() }

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def backward_dist(self, var, solver: Solver):

        dists = DiffReasoner.DijkstraState()
        assert solver.diff_reasoner is not None
        solver.diff_reasoner.distances_from(SignedVar.minus(var), dists)
        return { v.var: -d for d, v in dists.reached_nodes() }

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_propagation(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None
    
        A = solver.add_new_non_optional_variable((0,10), True)
        B = solver.add_new_non_optional_variable((0,10), True)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(A)], solver.state._bound_values[SignedVar.plus(A)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(B)], solver.state._bound_values[SignedVar.plus(B)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        check_bounds(0, 10, 0, 10)

        solver.state.set_literal(Lit.leq(A, 3), Causes.Decision())

        self.add_active_edge(A, B, 5, solver)

        solver.diff_reasoner.propagate()

        check_bounds(0, 3, 0, 8)

        solver.state.set_literal(Lit.leq(A, 1), Causes.Decision())

        solver.diff_reasoner.propagate()

        check_bounds(0, 1, 0, 6)

        x = self.add_inactive_edge(A, B, 3, solver)
        self.mark_edge_active(x, solver)

        solver.diff_reasoner.propagate()

        check_bounds(0, 1, 0, 4)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_backtracking(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        A = solver.add_new_non_optional_variable((0,10), True)
        B = solver.add_new_non_optional_variable((0,10), True)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(A)], solver.state._bound_values[SignedVar.plus(A)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(B)], solver.state._bound_values[SignedVar.plus(B)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        check_bounds(0, 10, 0, 10)

        solver.state.set_literal(Lit.leq(A, 1), Causes.Decision())

        solver.diff_reasoner.propagate()

        check_bounds(0, 1, 0, 10)
        
        solver.increment_one_decision_level()

        self.add_active_edge(A, B, 5, solver)

        solver.diff_reasoner.propagate()

        check_bounds(0, 1, 0, 6)

        solver.increment_one_decision_level()

        self.add_active_edge(B, A, -6, solver)

        self.assertIsInstance(solver.diff_reasoner.propagate(), 
                              InvalidBoundUpdateInfo)

        solver.backtrack_to_decision_level(solver.state.decision_level-1)
        check_bounds(0, 1, 0, 6)
 
        solver.backtrack_to_decision_level(solver.state.decision_level-1)
        check_bounds(0, 1, 0, 10)

        x = self.add_inactive_edge(A, B, 5, solver)
        self.mark_edge_active(x, solver)

        solver.diff_reasoner.propagate()

        check_bounds(0, 1, 0, 6)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_explanation(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        A = solver.add_new_non_optional_variable((0,10), True)
        B = solver.add_new_non_optional_variable((0,10), True)
        C = solver.add_new_non_optional_variable((0,10), True)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(A)], solver.state._bound_values[SignedVar.plus(A)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(B)], solver.state._bound_values[SignedVar.plus(B)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        solver.diff_reasoner.propagate()

        solver.increment_one_decision_level()

        x = self.add_inactive_edge(A, A, -1, solver)
        self.mark_edge_active(x, solver)

        self.assertIsInstance(solver.diff_reasoner.propagate(), 
                              ReasonerBaseExplanation)

        solver.backtrack_to_decision_level(solver.state.decision_level-1)

        solver.increment_one_decision_level()

        self.add_active_edge(A, B, 2, solver)
        self.add_active_edge(B, A, -3, solver)

        self.assertIsInstance(solver.diff_reasoner.propagate(), 
                              ReasonerBaseExplanation)
        
        solver.backtrack_to_decision_level(solver.state.decision_level-1)

        solver.increment_one_decision_level()

        self.add_active_edge(A, B, 2, solver)
        self.add_active_edge(B, A, -2, solver)

        solver.diff_reasoner.propagate()

        self.add_active_edge(B, A, -3, solver)

        self.assertIsInstance(solver.diff_reasoner.propagate(), 
                              ReasonerBaseExplanation)
        
        solver.backtrack_to_decision_level(solver.state.decision_level-1)

        solver.increment_one_decision_level()

        self.add_active_edge(A, B, 2, solver)
        self.add_active_edge(B, C, 2, solver)
        self.add_active_edge(C, A, -4, solver)

        solver.diff_reasoner.propagate()

        self.add_active_edge(C, A, -5, solver)

        self.assertIsInstance(solver.diff_reasoner.propagate(),
                              ReasonerBaseExplanation)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_optionals(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        PA = Lit.geq(solver.add_new_non_optional_variable((0, 1), True), BoundVal(1))
        A = solver.add_new_optional_variable((0,10), True, PA)

        PB = Lit.geq(solver.add_new_presence_variable(PA), BoundVal(1))
        B = solver.add_new_optional_variable((0,10), True, PB)
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(A)], solver.state._bound_values[SignedVar.plus(A)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(B)], solver.state._bound_values[SignedVar.plus(B)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.add_delay(A, B, 0, solver)

        solver.diff_reasoner.propagate()

        solver.state.set_literal(Lit.geq(B, 1), Causes.Decision())
        solver.state.set_literal(Lit.leq(B, 9), Causes.Decision())

        solver.diff_reasoner.propagate()

        check_bounds(0, 10, 1, 9)

        solver.state.set_literal(Lit.geq(A, 2), Causes.Decision())

        solver.diff_reasoner.propagate()

        check_bounds(2, 10, 2, 9)

        solver.state.set_literal(PB, Causes.Decision())

        solver.diff_reasoner.propagate()

        check_bounds(2, 9, 2, 9)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_optional_chain(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        vars = []
        context = TRUE_LIT

        for i in range(10):
            prez = Lit.geq(solver.add_new_presence_variable(context), 1)
            var = solver.add_new_optional_variable((0, 20), True, prez)
            if i > 0:
                self.add_delay(vars[i-1][1], var, 1, solver)
            vars.append((prez, var))
            context = prez
        
        solver.diff_reasoner.propagate()

        for i, (_, var) in enumerate(vars):
            self.assertEqual((-solver.state.bound_value_of(SignedVar.minus(var)),
                              solver.state.bound_value_of(SignedVar.plus(var))), 
                             (i, 20))
        
        self.assertTrue(solver.state.set_literal(Lit.leq(vars[5][1], 4), Causes.Decision()))

        solver.diff_reasoner.propagate()

        for i, (_, var) in enumerate(vars):
            if i <= 4:
                self.assertEqual((-solver.state.bound_value_of(SignedVar.minus(var)),
                                  solver.state.bound_value_of(SignedVar.plus(var))), 
                                 (i, 20))
            else:
                self.assertTrue(solver.state.is_entailed(solver.state.presence_literal_of(var).negated))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_distances_simple(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        A = solver.add_new_non_optional_variable((0,1), True)
        B = solver.add_new_non_optional_variable((0,10), True)

        self.add_active_edge(B, A, -1, solver)

        solver.diff_reasoner.propagate()

        dists = self.backward_dist(A, solver)

        self.assertEqual(len(dists), 2)
        self.assertEqual(dists[A], 0)
        self.assertEqual(dists[B], 1)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_distances(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        # create an STN graph with the following edges, all with a weight of 1
        # A -1-> C -1-> D -1-> E -1-> F
        # |                    ^
        # |                    |
        # ----1---> B ----1-----

        A = solver.add_new_non_optional_variable((0,10), True)
        B = solver.add_new_non_optional_variable((0,10), True)
        C = solver.add_new_non_optional_variable((0,10), True)
        D = solver.add_new_non_optional_variable((0,10), True)
        E = solver.add_new_non_optional_variable((0,10), True)
        F = solver.add_new_non_optional_variable((0,10), True)

        self.add_active_edge(A, B, 1, solver)
        self.add_active_edge(A, C, 1, solver)
        self.add_active_edge(C, D, 1, solver)
        self.add_active_edge(B, E, 1, solver)
        self.add_active_edge(D, E, 1, solver)
        self.add_active_edge(E, F, 1, solver)

        solver.diff_reasoner.propagate()

        dists = self.forward_dist(A, solver)

        self.assertEqual(len(dists), 6)
        self.assertEqual(dists[A], 0)
        self.assertEqual(dists[B], 1)
        self.assertEqual(dists[C], 1)
        self.assertEqual(dists[D], 2)
        self.assertEqual(dists[E], 2)
        self.assertEqual(dists[F], 3)

        dists = self.backward_dist(A, solver)

        self.assertEqual(len(dists), 1)
        self.assertEqual(dists[A], 0)

        dists = self.backward_dist(F, solver)

        self.assertEqual(len(dists), 6)
        self.assertEqual(dists[F], 0)
        self.assertEqual(dists[E], -1)
        self.assertEqual(dists[D], -2)
        self.assertEqual(dists[B], -2)
        self.assertEqual(dists[C], -3)
        self.assertEqual(dists[A], -3)

        dists = self.backward_dist(D, solver)

        self.assertEqual(len(dists), 3)
        self.assertEqual(dists[D], 0)
        self.assertEqual(dists[C], -1)
        self.assertEqual(dists[A], -2)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_distances_negative(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        # create an STN graph with the following edges, all with a weight of -1
        # A -(-1)-> C -(-1)-> D -(-1)-> E -(-1)-> F
        # |                            ^
        # |                            |
        # ---(-1)---> B ---(-1-)--------

        A = solver.add_new_non_optional_variable((0,10), True)
        B = solver.add_new_non_optional_variable((0,10), True)
        C = solver.add_new_non_optional_variable((0,10), True)
        D = solver.add_new_non_optional_variable((0,10), True)
        E = solver.add_new_non_optional_variable((0,10), True)
        F = solver.add_new_non_optional_variable((0,10), True)

        self.add_active_edge(A, B, -1, solver)
        self.add_active_edge(A, C, -1, solver)
        self.add_active_edge(C, D, -1, solver)
        self.add_active_edge(B, E, -1, solver)
        self.add_active_edge(D, E, -1, solver)
        self.add_active_edge(E, F, -1, solver)

        solver.diff_reasoner.propagate()

        dists = self.forward_dist(A, solver)

        self.assertEqual(len(dists), 6)
        self.assertEqual(dists[A], 0)
        self.assertEqual(dists[B], -1)
        self.assertEqual(dists[C], -1)
        self.assertEqual(dists[D], -2)
        self.assertEqual(dists[E], -3)
        self.assertEqual(dists[F], -4)

        dists = self.backward_dist(A, solver)

        self.assertEqual(len(dists), 1)
        self.assertEqual(dists[A], 0)

        dists = self.backward_dist(F, solver)

        self.assertEqual(len(dists), 6)
        self.assertEqual(dists[F], 0)
        self.assertEqual(dists[E], 1)
        self.assertEqual(dists[D], 2)
        self.assertEqual(dists[B], 2)
        self.assertEqual(dists[C], 3)
        self.assertEqual(dists[A], 4)

        dists = self.backward_dist(D, solver)

        self.assertEqual(len(dists), 3)
        self.assertEqual(dists[D], 0)
        self.assertEqual(dists[C], 1)
        self.assertEqual(dists[A], 2)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_negative_self_loop(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        A = solver.add_new_non_optional_variable((0,1), True)

        self.add_active_edge(A, A, -1, solver)

        self.assertIsNotNone(solver.diff_reasoner.propagate())
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_theory_propagation_edges_simple(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        A = solver.add_new_non_optional_variable((10, 20), True)
        PA1 = Lit.geq(solver.add_new_non_optional_variable((0, 1), True), BoundVal(1))
        A1 = solver.add_new_optional_variable((0, 30), True, PA1)

        B = solver.add_new_non_optional_variable((10, 20), True)
        PB1 = Lit.geq(solver.add_new_non_optional_variable((0, 1), True), BoundVal(1))
        B1 = solver.add_new_optional_variable((0, 30), True, PA1)

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def check_bounds(a_lb, a_ub, b_lb, b_ub):
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(A1)], solver.state._bound_values[SignedVar.plus(A1)]), 
                             (a_lb, a_ub))
            self.assertEqual((-solver.state._bound_values[SignedVar.minus(B1)], solver.state._bound_values[SignedVar.plus(B1)]), 
                             (b_lb, b_ub))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.add_delay(A, A1, 0, solver)
        self.add_delay(A1, A, 0, solver)

        self.add_delay(B, B1, 0, solver)
        self.add_delay(B1, B, 0, solver)

        # A strictly before B
        top = self.add_inactive_edge(B, A, -1, solver)
        # B1 strictly before A1
        bottom = self.add_inactive_edge(A1, B1, -1, solver)

        solver.diff_reasoner._propagate(("edges",))

        check_bounds(10, 20, 10, 20)

        solver.state.set_literal(top, Causes.Decision())

        solver.diff_reasoner._propagate(("edges",))

        # TODO: optional propagation currently does not takes an edge whose source is not proved present
        # self.assertTrue(solver.state.is_entailed(bottom.negated))
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_theory_propagation_edges(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        A = solver.add_new_non_optional_variable((0, 10), True)
        B = solver.add_new_non_optional_variable((0, 10), True)

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of(lit):
            if solver.state.is_entailed(lit):
                return True
            elif solver.state.is_entailed(lit.negated):
                return False
            return None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def explain_literal(lit):
            assert solver.diff_reasoner is not None

            expl = [lit]
            return solver.refine_explanation(expl, solver.diff_reasoner.explain).asserting_clause_literals
    
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.add_active_edge(A, B, 1, solver)
        ba0 = self.add_inactive_edge(B, A, 0, solver)
        ba1 = self.add_inactive_edge(B, A, -1, solver)
        ba2 = self.add_inactive_edge(B, A, -2, solver)

        self.assertEqual(value_of(ba0), None)

        solver.diff_reasoner._propagate(("edges",))

        self.assertEqual(value_of(ba0), None)
        self.assertEqual(value_of(ba1), None)
        self.assertEqual(value_of(ba2), False)

        self.assertEqual(len(explain_literal(ba2.negated)), 0)

        # TODO: adding a new edge does not trigger theory propagation
        # ba3 = self.add_inactive_edge(B, A, -3, solver)
        # solver.diff_reasoner._propagate(solver.state, ("edges",))
        # self.assertEqual(value_of(ba3), 0)

        C = solver.add_new_non_optional_variable((0, 10), True)
        D = solver.add_new_non_optional_variable((0, 10), True)
        E = solver.add_new_non_optional_variable((0, 10), True)
        F = solver.add_new_non_optional_variable((0, 10), True)
        G = solver.add_new_non_optional_variable((0, 10), True)

        # create a chain "abcdefg" of length 6
        # the edge in the middle is the last one added

        self.add_active_edge(B, C, 1, solver)
        self.add_active_edge(C, D, 1, solver)
        de = self.add_inactive_edge(D, E, 1, solver)
        self.add_active_edge(E, F, 1, solver)
        self.add_active_edge(F, G, 1, solver)

        # do not mark active at the root, otherwise the constraint might be inferred as always active
        # its enabler ignored in explanations
        solver.diff_reasoner._propagate(("edges",))
        solver.increment_one_decision_level()
        self.mark_edge_active(de, solver)
        
        ga0 = self.add_inactive_edge(G, A, -5, solver)
        ga1 = self.add_inactive_edge(G, A, -6, solver)
        ga2 = self.add_inactive_edge(G, A, -7, solver)

        solver.diff_reasoner._propagate(("edges",))
        
        self.assertEqual(value_of(ga0), None)
        self.assertEqual(value_of(ga1), None)
        self.assertEqual(value_of(ga2), False)

        self.assertEqual(len(explain_literal(ga2.negated)), 1)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_theory_propagation_bounds(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=True)
        
        assert solver.diff_reasoner is not None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def value_of(lit):
            if solver.state.is_entailed(lit):
                return True
            elif solver.state.is_entailed(lit.negated):
                return False
            return None

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        A = solver.add_new_non_optional_variable((0, 10), True)
        B = solver.add_new_non_optional_variable((10, 20), True)

        edge_trigger = self.add_inactive_edge(A, B, 0, solver)

        solver.diff_reasoner.propagate()

        self.assertEqual(value_of(edge_trigger), None)

        solver.increment_one_decision_level()
        solver.state.set_literal(Lit.geq(B, 11), Causes.Decision())

        solver.diff_reasoner.propagate()

        self.assertEqual(value_of(edge_trigger), False)

        solver.backtrack_to_decision_level(0, )
        solver.increment_one_decision_level()
        solver.state.set_literal(Lit.leq(A, 9), Causes.Decision())

        solver.diff_reasoner.propagate()

        self.assertEqual(value_of(edge_trigger), False)

#################################################################################
