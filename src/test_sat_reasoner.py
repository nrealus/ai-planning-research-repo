from __future__ import annotations

#################################################################################

from fundamentals import *

from solver import *
from solver_sat_reasoner import *
from solver_api import *
from solver_api import _add_clause_from_raw_clause_literals_and_scope

import unittest

#################################################################################

class TestSATReasonerClauseAddition(unittest.TestCase):
   
    def test_add_clause_from_raw_clause_literals_and_scope(self):
        solver = Solver()
        sat_reasoner = SATReasoner()

        PX = add_new_presence_variable(solver, TRUE_LIT)
        PX_lit = Literal(SignedVar(PX, False), BoundValue(-1))

        X1 = add_new_optional_variable(solver, (0, 1), True, PX_lit)
        X1_lit = Literal(SignedVar(X1, False), BoundValue(-1))

        X2 = add_new_optional_variable(solver, (0, 1), True, PX_lit)
        X2_lit = Literal(SignedVar(X2, False), BoundValue(-1))

        PY = add_new_presence_variable(solver, TRUE_LIT)
        PY_lit = Literal(SignedVar(PY, False), BoundValue(-1))

#        let mut m = Model::new();
#
#        let px = m.new_presence_variable(Lit::TRUE, "px").true_lit();
#        let x1 = m.new_optional_bvar(px, "x1").true_lit();
#        let x2 = m.new_optional_bvar(px, "x2").true_lit();
#
#        let py = m.new_presence_variable(Lit::TRUE, "py").true_lit();
#        // let y1 = m.new_optional_bvar(py, "y1").true_lit();
#        // let y2 = m.new_optional_bvar(py, "y2").true_lit();
#
#        let pxy = m.get_conjunctive_scope(&[px, py]);
#        let xy1 = m.new_optional_bvar(pxy, "xy1").true_lit();
#        // let xy2 = m.new_optional_bvar(pxy, "xy2").true_lit();
#
#        let s = &Solver::new(m);
#
#        fn check(
#            s: &Solver,
#            scope: Lit,
#            clause: impl Into<Disjunction>,
#            expected: impl Into<Disjunction>,
#            expected_scope: Lit,
#        ) {
#            let clause = clause.into();
#            let result = s.scoped_disjunction(clause, scope);
#            let expected = expected.into();
#            assert_eq!(result, (expected, expected_scope));
#        }
#
#        check(s, px, [x1], [x1], px);
#        // check(s, T, [!px, x1], [x1]);
#        check(s, px, [x1, x2], [x1, x2], px);
#        // check(s, T, [!px, x1, x2], [x1, x2]);
#        check(s, px, [xy1], [xy1], px); // ??
#        check(s, py, [xy1], [xy1], py);
#        check(s, pxy, [xy1], [xy1], pxy);
#        check(s, pxy, [x1], [!pxy, x1], Lit::TRUE);
#        // check(s, T, [!pxy, xy1], [xy1]);
#        // check(s, T, [!px, !py, xy1], [xy1]);
#        // check(s, T, [!px, !py], [!px, !py]); // !pxy, would be correct as well

#################################################################################
#################################################################################

if __name__ == '__main__':
    unittest.main()
