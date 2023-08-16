from __future__ import annotations

#################################################################################

from typing import Tuple

from fundamentals import *
from solver import *

#################################################################################
#################################################################################
#                                   CONTENTS:
# - PROBLEM ENCODING FOR THE SOLVER:
#    - VARIABLE ADDITION (NON OPTIONAL AND OPTIONAL)
#    - IMPLICATION ADDITION (BETWEEN LITERALS ON NON-OPTIONAL VARIABLES)
#################################################################################
#################################################################################

def _add_new_variable(
    solver: Solver,
    initial_domain: Tuple[int, int],
    controllable_or_not: bool,
) -> Var:
    """
    TODO
    """

    solver._vars_id_counter += 1
    var = Var(solver._vars_id_counter)

    solver.vars[controllable_or_not].add(var)
    
    solver.bound_values[SignedVar(var, False)] = BoundValue(-initial_domain[0])
    solver.bound_values_event_indices[SignedVar(var, False)] = (0, len(solver.events_trail[0]))
    solver.events_trail[0].append(SolverEvent(
        SignedVar(var, True),
        BoundValue(initial_domain[1]),
        BoundValue(initial_domain[1]),
        (0,len(solver.events_trail[0])),
        SolverCause.Encoding(),
    ))


    solver.bound_values[SignedVar(var, True)] = BoundValue(initial_domain[1])
    solver.bound_values_event_indices[SignedVar(var, True)] = (0, len(solver.events_trail[0]))
    solver.events_trail[0].append(SolverEvent(
        SignedVar(var, True),
        BoundValue(initial_domain[1]),
        BoundValue(initial_domain[1]),
        (0,len(solver.events_trail[0])),
        SolverCause.Encoding(),
    ))

    return var

#################################################################################

def add_new_non_optional_variable(
    solver: Solver,
    initial_domain: Tuple[int, int],
    controllable_or_not: bool,
) -> Var:
    """
    TODO
    """

    var = _add_new_variable(solver, initial_domain, controllable_or_not)
    solver.vars_presence_literals[var] = TrueLiteral

    return var

#################################################################################

def add_new_optional_variable(
    solver: Solver,
    initial_domain: Tuple[int, int],
    controllable_or_not: bool,
    presence_literal: Literal,
) -> Var:
    """
    TODO
    """

    if solver.vars_presence_literals[presence_literal.signed_var.var] != TrueLiteral:
        raise ValueError("""The presence literal of an optional variable must not be based on an optional variable.""")

    var = _add_new_variable(solver, initial_domain, controllable_or_not)
    solver.vars_presence_literals[var] = presence_literal

    return var

#################################################################################

def add_implication(
    solver: Solver,
    from_literal: Literal,
    to_literal: Literal,
):
    """
    TODO
    """

    if (solver.vars_presence_literals[from_literal.signed_var.var] != TrueLiteral
        or solver.vars_presence_literals[to_literal.signed_var.var] != TrueLiteral
    ):
        raise ValueError("Only implications between non-optional variables are supported")

    from_literal_neg = from_literal.negation()
    to_literal_neg = to_literal.negation()

    # Add the implication to the implication graph.

    if (to_literal == TrueLiteral
        or from_literal == FalseLiteral
        or from_literal.entails(to_literal)
#        or to_literal in solver.get_literals_directly_implied_by(from_literal)
#        or from_literal_negation in solver.get_literals_directly_implied_by(to_literal_negation)
    ):
        pass    # Obvious cases of implications: no need to add 
                # them to the implication graph.
    else:
        solver.non_optional_vars_implication_graph.setdefault(
            from_literal.signed_var, {}).setdefault(
            from_literal.bound_value, set()).add(to_literal)
        solver.non_optional_vars_implication_graph.setdefault(
            to_literal_neg.signed_var, {}).setdefault(
            to_literal_neg.bound_value, set()).add(from_literal_neg)

    # Now, check whether the introduction of
    # the implication introduces any inconsistency.

    # If from_literal is entailed
    if solver.bound_values[from_literal.signed_var].is_stronger_than(from_literal.bound_value):
        propag_result = solver.set_bound_value(
            to_literal.signed_var,
            to_literal.bound_value,
            SolverCause.ImplicationPropagation(from_literal)
        )
        if isinstance(propag_result, SolverConflictInfo.InvalidBoundUpdate):
            raise ValueError("""Inconsistency on the addition of the implication {0} => {1}""".format(
                from_literal, to_literal)
            )

    # If to_literal_negation is entailed
    if solver.bound_values[to_literal_neg.signed_var].is_stronger_than(to_literal_neg.bound_value):
        propag_result = solver.set_bound_value(
            from_literal.signed_var,
            from_literal_neg.bound_value,
            SolverCause.ImplicationPropagation(to_literal_neg)
        )
        if isinstance(propag_result, SolverConflictInfo.InvalidBoundUpdate):
            raise ValueError("""Inconsistency on the addition of the implication {0} => {1}""".format(
                from_literal, to_literal)
            )

#################################################################################
