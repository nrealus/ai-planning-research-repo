from __future__ import annotations

#################################################################################

from typing import Tuple

from fundamentals import *
from solver import *
from solver_sat_reasoner import *

#################################################################################
#################################################################################
#                                   CONTENTS:
# - PROBLEM ENCODING FOR THE SOLVER:
#    - VARIABLE ADDITION (NON OPTIONAL AND OPTIONAL)
#    - IMPLICATION ADDITION (BETWEEN LITERALS ON NON-OPTIONAL VARIABLES)
#################################################################################
#################################################################################

def add_new_non_optional_variable(
    solver: Solver,
    initial_domain: Tuple[int, int],
    controllable_or_not: bool,
) -> Var:
    """
    Registers a new non-optional variable to the solver and returns it.
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
    Registers a new optional variable to the solver and returns it.
    """

    if solver.vars_presence_literals[presence_literal.signed_var.var] != TrueLiteral:
        raise ValueError("""The presence literal of an optional variable must not be based on an optional variable.""")

    var = _add_new_variable(solver, initial_domain, controllable_or_not)
    solver.vars_presence_literals[var] = presence_literal

    return var

#################################################################################

def _add_new_variable(
    solver: Solver,
    initial_domain: Tuple[int, int],
    controllable_or_not: bool,
) -> Var:
    """
    Used internally by other functions that register/add a new variable to
    the solver and then return it.
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

def add_new_presence_variable(
    solver: Solver,
    scope_literal: Literal,      
) -> Var:
    """
    Registers a new presence variable, defined in the scope corresponding to
    the given scope literal, and returns it.

    A presence variable is simply a non-optional boolean variable (its initial
    domain is {0,1}), that is defined inside of a particular scope.   
    """
    
    var = add_new_non_optional_variable(solver, (0,1), True)
    lit = Literal(SignedVar(var, False), BoundValue(-1))
    _insert_conjunctive_scope(solver, (lit,), lit)
    _add_implication(solver, lit, scope_literal)
    return var

#################################################################################

def _add_implication(
    solver: Solver,
    from_literal: Literal,
    to_literal: Literal,
) -> None:
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

def _insert_conjunctive_scope(
    solver: Solver,
    presence_literals_conjunction: Tuple[Literal,...],
    scope_literal: Literal
) -> None:

    assert presence_literals_conjunction not in solver.conjunctive_scopes

    solver.conjunctive_scopes[presence_literals_conjunction] = scope_literal
    solver.conjunctive_scopes_reverse[scope_literal] = presence_literals_conjunction

#################################################################################

def enforce_constr_expr(
    solver: Solver,
    constr_expr: ConstrExpr,
    scope_literals_conjunction: Tuple[Literal,...],
) -> Literal:
    
    constr_formula = # TODO_decompose_constr_expr_to_formula()
    return _enforce_constr_formula(solver, constr_formula, scope_literals_conjunction)
        
#################################################################################

def _enforce_constr_formula(
    solver: Solver,
    constr_formula: ConstrFormula.Any,
    scope_literals_conjunction: Tuple[Literal,...],
) -> Literal:
    """
    Enforces the given formula to be true whenever all literals of the scope are true.

    Similar to posintg a constraint in CP solvers.

    Internally, the formula is reified to an optional literal that is true,
    when the formula is valid/defined and absent otherwise.

    Returns that literal.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_tautology_of_scope(
        _scope_literal: Literal,
    ) -> Literal:
        """
        Returns a literal whose presence is scope_literal and that is always true.

        This is functionally equivalent to creating a new optional boolean variable
        with domain {1} and with presence scope_literal, but will ensure that only
        one such variable is created in this scope.
        
        Indeed, the TrueLiteral cannot work for this, because it (just as its
        variable, the special ZeroVar variable) is present always/in all scopes.
        """

        if _scope_literal in solver.conjunctive_scopes_tautologies:
            return solver.conjunctive_scopes_tautologies[_scope_literal]

        else:
            var = add_new_optional_variable(solver, (1, 1), False, _scope_literal)
            literal = Literal(SignedVar(var, False), BoundValue(-1))
            solver.conjunctive_scopes_tautologies[_scope_literal] = literal
            return literal

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_formula_conjunctive_scope(
        _constr_formula: ConstrFormula.Any,
    ) -> Tuple[Dict[SignedVar, BoundValue], Tuple[Literal,...]]:
        """
        Get the (validity) scope of an formula.

        It is represented by a pair (tuple):
        - The 1st element (aka `scope_required_presences`) is the set of presence
        literals that appear in the formula.
        - The 2nd element (aka `scope_guards`) is a set of literals such that if
        one of them is true, the formula is defined/valid.
        """
        
        if isinstance(_constr_formula, ConstrFormula.SingleLit):
            prez_lit = solver.vars_presence_literals[_constr_formula.literal.signed_var.var]
            return (
                { prez_lit.signed_var: prez_lit.bound_value },
                (),
            )

        elif isinstance(_constr_formula, ConstrFormula.Or):
            prez_lits = [solver.vars_presence_literals[lit.signed_var.var]
                for lit in _constr_formula.literals]
            return (
                { prez_lit.signed_var: prez_lit.bound_value for prez_lit in prez_lits },
                tuple(lit for lit in _constr_formula.literals
                    if solver.vars_presence_literals[lit.signed_var.var] == TrueLiteral),
            )

        elif isinstance(_constr_formula, ConstrFormula.And):
            prez_lits = [solver.vars_presence_literals[lit.signed_var.var]
                for lit in _constr_formula.literals]
            return (
                { prez_lit.signed_var: prez_lit.bound_value for prez_lit in prez_lits },
                tuple(lit.negation() for lit in _constr_formula.literals
                    if solver.vars_presence_literals[lit.negation().signed_var.var] == TrueLiteral),
            )

        elif isinstance(_constr_formula, ConstrFormula.MaxDiffCnt):
            prez_lit_from_var = solver.vars_presence_literals[_constr_formula.from_var]
            prez_lit_to_var = solver.vars_presence_literals[_constr_formula.from_var]
            return (
                { prez_lit_from_var.signed_var: prez_lit_from_var.bound_value,
                  prez_lit_to_var.signed_var: prez_lit_to_var.bound_value },
                (),
            )

        else:
            assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_flattened_conjunctive_scope_literals(
        _conjunctive_scope: Tuple[Dict[SignedVar, BoundValue], Tuple[Literal,...]],
        _check_for_top_decision_level: bool,
    ) -> Tuple[Literal,...]:
        """
        Flattens a scope (describing the validity/definition conditions of
        a formula) represented as a pair into a conjunction of literals.
        """

        scope_required_presences, scope_guards = _conjunctive_scope
        scope_guards = tuple(guard for guard in scope_guards if guard != FalseLiteral)

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def is_tautology(lit: Literal):

            return (solver.is_literal_entailed(lit)
                and (not _check_for_top_decision_level
                    or solver.get_index_of_first_event_implying_literal(lit)[0] == 0
            ))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        flattened_scope_literals_conjunction_dict: Dict[SignedVar, BoundValue] = {}

        for s_var, b_val in scope_required_presences.items():
            lit = Literal(s_var, b_val)

            # If a presence literal is defined as a conjunction of other literals, replace it with them.
            flattened = solver.conjunctive_scopes_reverse.get(lit, None)
            if flattened is not None:

                for l in flattened:
                    if (not is_tautology(l)
                        and (l.signed_var not in flattened_scope_literals_conjunction_dict
                            or l.bound_value.is_stronger_than(flattened_scope_literals_conjunction_dict[l.signed_var])
                        )
                    ):
                        flattened_scope_literals_conjunction_dict[l.signed_var] = l.bound_value

            # Otherwise, if the presence literal is not considered to be a tautology,
            # do add it to the conjunction
            elif not is_tautology(lit):
                flattened_scope_literals_conjunction_dict[lit.signed_var] = lit.bound_value

        for guard in scope_guards:
            guard_neg = guard.negation()

            # If a presence literal is guarded, remove it from the conjunction.
            if (guard_neg.signed_var in flattened_scope_literals_conjunction_dict
                and flattened_scope_literals_conjunction_dict[guard_neg.signed_var].is_stronger_than(guard_neg.bound_value)
            ):
                # FIXME: + 1 used here instead of a defined constant
                weaker = Literal(guard_neg.signed_var, BoundValue(guard.bound_value + BoundValue(1)))
                if is_tautology(weaker):
                    flattened_scope_literals_conjunction_dict.pop(guard_neg.signed_var)
                else:
                    flattened_scope_literals_conjunction_dict[guard_neg.signed_var] = weaker.bound_value

        # Convert the set/conjunction of literals to a list, and sort it (lexicographically).
        flattened_scope_literals_conjunction_list = [Literal(signed_var, bound_value)
            for signed_var, bound_value in flattened_scope_literals_conjunction_dict.items()
        ]
        flattened_scope_literals_conjunction_list.sort()
        return tuple(flattened_scope_literals_conjunction_list)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_or_make_scope_literal_from_flattened_conjunctive_scope_literals(
        _scope_literals_conjunction: Tuple[Literal,...],
    ) -> Literal:
        """
        Return a scope literal corresponding to the scope defined by the
        given conjunction of scope literals.

        If there isn't already a scope literal like that, add it to the solver.
        """

        # If the scope already exists, return it immediately.
        if _scope_literals_conjunction in solver.conjunctive_scopes:
            return solver.conjunctive_scopes[_scope_literals_conjunction]

        # We need to create a new literal l such that l <=> l1 & l2 & ... & ln
        # (where li are the (presence) literals composing the conjunctive scope)

        # Simplify the conjunction of literals
        simplified_literal_attempt: Optional[Literal] = None

        if len(_scope_literals_conjunction) == 1:
            simplified_literal_attempt = _scope_literals_conjunction[0]

        elif len(_scope_literals_conjunction) == 2:

            # If l1 => l2, the conjunction can be simplified to l1
            if solver.is_implication_true(_scope_literals_conjunction[0], _scope_literals_conjunction[1]):
                simplified_literal_attempt = _scope_literals_conjunction[0]

            # If l2 => l1, the conjunction can be simplified to l2
            elif solver.is_implication_true(_scope_literals_conjunction[1], _scope_literals_conjunction[0]):
                simplified_literal_attempt = _scope_literals_conjunction[1]
    
            # If l1 and l2 are exclusive (i.e. cannot be true at the same time, i.e. l1 => !l2),
            # the conjunctive scope literal is false. However, we cannot directly use FalseLiteral,
            # because we need to uniquely identify the literal as the conjunction of the other two
            # in some corner cases. So we create a new literal that is always false.
            if solver.is_implication_true(_scope_literals_conjunction[0], _scope_literals_conjunction[1].negation()):
                simplified_literal_attempt = Literal(
                    SignedVar(_add_new_variable(solver, (0,0), False), False),
                    BoundValue(-1),
                )

        # If a simplification was found, we return it as the scope literal of the conjunction.
        if simplified_literal_attempt is not None:
            _insert_conjunctive_scope(solver, _scope_literals_conjunction, simplified_literal_attempt)
            return simplified_literal_attempt

        # If no simplication was found, a new literal l is created such that:
        # - l => l1, l => l2, ...
        # - l v !l1 v !l2 v ... v !ln
        # This literal l will indeed satisfy l <=> l1 & l2 & ... & ln.
        else:
            literal = Literal(
                SignedVar(_add_new_variable(solver, (0,0), False), False),
                BoundValue(-1),
            )
            clause_literals: List[Literal] = []
            for lit in _scope_literals_conjunction:
                _add_implication(solver, literal, lit)
                clause_literals.append(lit.negation())
            bind(
                ConstrFormula.Or(tuple(clause_literals)),
                get_tautology_of_scope(
                    get_or_make_scope_literal_from_flattened_conjunctive_scope_literals(())
                )
            )
            _insert_conjunctive_scope(solver, _scope_literals_conjunction, literal)
            return literal

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def reify_and_add_constraint_formula(
        _constr_formula: ConstrFormula.Any,
    ) -> Literal:
        """
        Reify a constraint and add/register the reification in the solver.

        The returned "reification literal" is *optional* and defined such
        that it is present iff the formula is valid (typically meaning
        that all variables involved in the formula are present)
        """
        if _constr_formula in solver.reifications:
            return solver.reifications[_constr_formula]
    
#        scope_literal = get_or_create_formula_scope_literal(_constr_formula)
        scope_literal = get_or_make_scope_literal_from_flattened_conjunctive_scope_literals(
            get_flattened_conjunctive_scope_literals(
                get_formula_conjunctive_scope(_constr_formula),
                False,
            )
        )
        
        var = add_new_optional_variable(solver, (0,1), True, scope_literal)
        reification_literal = Literal(SignedVar(var, False), BoundValue(-1))

        solver.reifications[_constr_formula] = reification_literal
        solver.reifications[_constr_formula.negation()] = reification_literal.negation()
        solver.reified_constraints.append(ReifiedConstraint(_constr_formula, reification_literal))

        return reification_literal

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def bind(
        _constr_formula: ConstrFormula.Any,
        _literal: Literal,
    ) -> None:
        """
        Record that the given literal <=> the given formula (constrain)
        (i.e. the literal is True iff the constraint is satisfied)
        """

        # Compute the validity scope of the formula
        # (it can be larger than that of the literal)
        formula_scope_literal = get_or_make_scope_literal_from_flattened_conjunctive_scope_literals(
            get_flattened_conjunctive_scope_literals(
                get_formula_conjunctive_scope(_constr_formula),
                False,
            )
        )
        
        # If the formula is already reified to a literal l,
        # unify it (l) with the parameter literal.
        reification_literal = solver.reifications.get(_constr_formula, None)
        if reification_literal is not None:
            if _literal != reification_literal:
                solver.reified_constraints.append(ReifiedConstraint(
                    ConstrFormula.SingleLit(reification_literal),
                    _literal,
                ))
        
        # If the formula is not already reified and
        # scopes are compatible, suggest literal to be the reified literal.
        elif formula_scope_literal == solver.vars_presence_literals[_literal.signed_var.var]:
            solver.reifications[_constr_formula] = _literal
            solver.reifications[_constr_formula.negation()] = _literal.negation()
            solver.reified_constraints.append(ReifiedConstraint(_constr_formula, _literal))
        
        # If the formula is not already reified,
        # but literal cannot be used directly because it has a different scope
        else:
            reification_literal = reify_and_add_constraint_formula(_constr_formula)
            if _literal != reification_literal:
                solver.reified_constraints.append(ReifiedConstraint(
                    ConstrFormula.SingleLit(reification_literal),
                    _literal,
                ))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    scope_literal = get_or_make_scope_literal_from_flattened_conjunctive_scope_literals(
        scope_literals_conjunction,
    )

    # Bind the formula with an optional variable that is always true in the scope.
    # This optional variable can be retrieved if it already exists, or can be created on the fly.
    bind(constr_formula, get_tautology_of_scope(scope_literal))
    return scope_literal

#################################################################################
#################################################################################
#################################################################################
#################################################################################
#################################################################################
