from __future__ import annotations

#################################################################################

import unittest

from typing import Dict

from src.fundamentals import BoolAtom, IntAtom, FracAtom, SymbAtom, Atom, ZERO_VAR, TRUE_LIT, SymbType_WIP
from src.solver.solver import Solver
from src.planning_and_acting.common import ChronicleId, Chronicle, Task, Constraint, Condition, Effect, SubTask, StateVar
from src.planning_and_acting.planning import instantiate_chronicle_template

#################################################################################

class TestChronicles(unittest.TestCase):

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def test_instantiation(self):

        solver = Solver(use_sat_reasoner=False,
                        use_diff_reasoner=False)

        templ_prez = BoolAtom(solver.add_new_presence_variable(TRUE_LIT))
        templ_start = FracAtom(IntAtom(solver.add_new_optional_variable((0, 10), True, TRUE_LIT), 0), 1)
        templ_end = FracAtom(IntAtom(solver.add_new_optional_variable((5, 15), True, TRUE_LIT), 0), 1)
        templ_t1 = FracAtom(IntAtom(solver.add_new_optional_variable((2, 6), True, TRUE_LIT), 0), 1)
        templ_t2 = FracAtom(IntAtom(solver.add_new_optional_variable((4, 8), True, TRUE_LIT), 0), 1)

        dummy_sv = (SymbAtom(IntAtom(ZERO_VAR, 777), SymbType_WIP("object")), IntAtom(solver.add_new_optional_variable((0, 3), True, TRUE_LIT), 0))

        chronicle_template = Chronicle(templ_prez,
                                       templ_start,
                                       templ_end,
                                       None,
                                       [Constraint(Constraint.Kind.LEQ, (templ_start, templ_end)),
                                        Constraint(Constraint.Kind.LEQ, (templ_start, templ_t1)),
                                        Constraint(Constraint.Kind.LEQ, (templ_t1, templ_t2)),
                                        Constraint(Constraint.Kind.LEQ, (templ_t2, templ_end))],
                                       [Condition(templ_t2, templ_end, dummy_sv, IntAtom(ZERO_VAR, 1))],
                                       [Effect(templ_start, templ_start, (templ_t1,), dummy_sv, IntAtom(ZERO_VAR, 1))],
                                       [])
        
        t = FracAtom(IntAtom(solver.add_new_optional_variable((2, 8), True, TRUE_LIT), 0), 1)
        substitution: Dict[Atom, Atom] = { templ_start: FracAtom(IntAtom(ZERO_VAR, 2), 1), templ_t1: t, templ_t2: t }

        chronicle_instance = instantiate_chronicle_template(chronicle_template,
                                                            TRUE_LIT,
                                                            substitution,
                                                            solver)
        
        print(chronicle_template)
        print("")
        print(chronicle_instance)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#################################################################################
