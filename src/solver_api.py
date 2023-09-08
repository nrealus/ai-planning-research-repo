from __future__ import annotations

#################################################################################

from typing import Dict, List, Optional, Tuple

from fundamentals import (
    Var,
    SignedVar, BoundVal, Lit, TRUE_LIT, FALSE_LIT,
)
from constraint_expressions import (
    ConstrExpr,
    ElemConstrExpr,    
)
from solver import Causes, InvalidBoundUpdateInfo, Solver

#################################################################################
#################################################################################
#                                   CONTENTS:
# - SOLVER PROBLEM ENCODING API:
#   - VARIABLES ADDITION
#   - CONSTRAINTS ADDITION
#
# - HELPER FUNCTIONS:
#   - INSERTION OF IMPLICATIONS BETWEEN LITERALS ON NON OPTIONAL VARIABLES
#   - INSERTION OF NEW CONJUNCTIVE SCOPES
#################################################################################
#################################################################################

#################################################################################
# VARIABLE ADDITION
#################################################################################

def add_new_non_optional_variable(
    initial_domain: Tuple[int, int],
    controllable: bool,
    solver: Solver,
) -> Var:
    """
    Adds a new non-optional variable to the solver and returns it.
    """

    return _add_new_variable(initial_domain, controllable, TRUE_LIT, solver)

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def add_new_optional_variable(
    initial_domain: Tuple[int, int],
    controllable: bool,
    presence_literal: Lit,
    solver: Solver,
) -> Var:
    """
    Adds a new optional variable to the solver and returns it.
    """

    return _add_new_variable(initial_domain, controllable, presence_literal, solver)

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def add_new_presence_variable(
    solver: Solver,
    scope_literal: Lit,      
) -> Var:
    """
    Adds a new presence variable, defined in the scope corresponding to
    the given scope literal, and returns it.

    A presence variable is simply a non-optional (boolean) variable
    which is used to define presence literals.

    A presence literal, is simply a literal on (the truth value of) a presence
    variable. They are encoded as [presence_variable >= 1].
    """
    
    var = add_new_non_optional_variable((0,1), True, solver)
    
    lit = Lit.geq(var, 1)
    _insert_new_scope_from_scope_as_lits_conj_and_scope_lit((lit,), lit, solver)
    _insert_implication_between_literals_on_non_optional_vars(lit, scope_literal, solver)
    
    return var

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _add_new_variable(
    initial_domain: Tuple[int, int],
    controllable: bool,
    presence_literal: Lit,
    solver: Solver,
) -> Var:
    """
    Helper function for higher level functions that add a new variable.
    """

    if solver.vars_presence_literals[presence_literal.signed_var.var] != TRUE_LIT:
        raise ValueError("""The presence literal of an optional variable must not be based on an optional variable.""")

    solver._vars_id_counter += 1

    var = Var(solver._vars_id_counter)

    solver.vars[controllable].add(var)
    solver.vars_presence_literals[var] = presence_literal
    
    solver.bound_values[SignedVar.minus(var)] = BoundVal(-initial_domain[0])
    solver.bound_values[SignedVar.plus(var)] = BoundVal(initial_domain[1])

    return var
        
#################################################################################
# CONSTRAINT ADDITION
# (NOTE: Should probably be changed into a class, so that the nested functions could be tested...)
#################################################################################

def add_constraint(
    constr_expr: ConstrExpr,
    conj_scope_lits: Tuple[Lit,...],
    solver: Solver,
) -> Tuple[ElemConstrExpr, Lit]:
    """
    Adds a constraint defined by the given expression, in a scope defined by the given literals.
    (i.e. the constraint must be true when all the literals defining the conjunctive scope are true)

    Internally, the expression is transformed into elementary form, potentially
    reifying some intermediate constraints. The expression in elementary form is
    then reified to an optional literal that is true when the expression is
    valid/well-defined and absent otherwise.

    Returns a reified constraint, formed by the elementary form expression
    as well as that optional literal.
    """

    elem_constr_expr = _preprocess_constr_expr_into_elem_form(constr_expr, solver)
    scope_lit = _get_or_make_new_scope_lit_from_scope_as_lits_conj(conj_scope_lits, solver)

    # Bind the formula with an optional variable that is always true in the scope.
    # This optional variable can be retrieved if it already exists, or can be created on the fly.

    tauto = _get_or_make_tautology_of_scope_from_scope_lit(scope_lit, solver)
    _bind_elem_constr_expr(elem_constr_expr, tauto, solver)

    return (elem_constr_expr, tauto)

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
def _preprocess_constr_expr_into_elem_form(
    constr_expr: ConstrExpr,
    solver: Solver,
) -> ElemConstrExpr:
    """
    Transforms a constraint expression into elementary form
    (or constraint elementary expression).

    Also, may reify intermediate constraints, while preparing for
    the reification of the whole constraint.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _preprocess_eq_int_atoms(
        var_left: Var,
        offset_left: int,
        var_right: Var,
        offset_right: int,
    ) -> ElemConstrExpr:

        if var_left == var_right:
            return ElemConstrExpr.from_lit(TRUE_LIT)

        leq12_elem_form = ElemConstrExpr.from_int_atoms_leq(var_left, offset_left,
                                                            var_right, offset_right)
        leq21_elem_form = ElemConstrExpr.from_int_atoms_leq(var_right, offset_right,
                                                            var_left, offset_left)
        leq12_reif_lit = _reify_elem_constr_expr(leq12_elem_form, solver)
        leq21_reif_lit = _reify_elem_constr_expr(leq21_elem_form, solver)

        return ElemConstrExpr.from_lits_tighten_and_simplify_or((leq12_reif_lit.negation(),
                                                                 leq21_reif_lit.negation())).negation()

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def _preprocess_eq_bool_vars(
        var1: Var,
        var2: Var,
    ) -> ElemConstrExpr:

        if var1 == var2:
            return ElemConstrExpr.from_lit(TRUE_LIT)

        lit1 = Lit.geq(var1, 1)
        lit2 = Lit.geq(var2, 1)

        imply12_elem_form = ElemConstrExpr.from_lits_tighten_and_simplify_or((lit1.negation(), lit2))
        imply21_elem_form = ElemConstrExpr.from_lits_tighten_and_simplify_or((lit2.negation(), lit1))

        imply12_reif_lit = _reify_elem_constr_expr(imply12_elem_form, solver)
        imply21_reif_lit = _reify_elem_constr_expr(imply21_elem_form, solver)

        return ElemConstrExpr.from_lits_tighten_and_simplify_or((imply12_reif_lit.negation(),
                                                                 imply21_reif_lit.negation())).negation()

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    kind, terms = constr_expr.kind, constr_expr.terms

    match terms:
        case ((Var() as var_left, int() as offset_left), 
              (Var() as var_right, int() as offset_right)
        ):

            match kind:
                case ConstrExpr.Kind.LEQ:
                    return ElemConstrExpr.from_int_atoms_leq(var_left, offset_left,
                                                             var_right, offset_right)
                case ConstrExpr.Kind.LT:
                    return ElemConstrExpr.from_int_atoms_leq(var_left, offset_left,
                                                             var_right, offset_right-1)
                case ConstrExpr.Kind.GEQ:
                    return ElemConstrExpr.from_int_atoms_leq(var_right, offset_right,
                                                             var_left, offset_left)
                case ConstrExpr.Kind.GT:
                    return ElemConstrExpr.from_int_atoms_leq(var_right, offset_right,
                                                             var_left, offset_left-1)
                case ConstrExpr.Kind.EQ:
                    return _preprocess_eq_int_atoms(var_left, offset_left,
                                                    var_right, offset_right)
                case ConstrExpr.Kind.NEQ:
                    return _preprocess_eq_int_atoms(var_left, offset_left,
                                                    var_right, offset_right).negation()
                case _:
                    raise ValueError("""Incompatible constraint type and terms: for pairs of integer atoms (variable + offset), only LEQ, LT, GEQ, GT, EQ and NEQ constraints are defined.""")

        case Var() as var1, Var() as var2:

            match kind:
                case ConstrExpr.Kind.EQ:
                    return _preprocess_eq_bool_vars(var1, var2)

                case ConstrExpr.Kind.NEQ:
                    return _preprocess_eq_bool_vars(var1, var2).negation()

                case _:
                    raise ValueError("""Incompatible constraint type and terms: for pairs of boolean variables, only EQ, and NEQ constraints are defined.""")

        case [Lit(), *_] as lits: 

            match kind:
                case ConstrExpr.Kind.OR:
                    return ElemConstrExpr.from_lits_tighten_and_simplify_or(lits)

                case ConstrExpr.Kind.AND:
                    return ElemConstrExpr.from_lits_tighten_and_simplify_or(tuple(lit.negation() for lit in lits)).negation()

                case ConstrExpr.Kind.IMPLY:
                    if len(terms) == 2:
                        lit_from, lit_to = lits[0], lits[1]
                        return ElemConstrExpr.from_lits_tighten_and_simplify_or((lit_from.negation(), lit_to))
                    else:
                        raise ValueError("""Incorrect number of terms: IMPLY constraints require exactly two literals.""")

                case _:
                    raise ValueError("""Incompatible constraint type and terms: OR, AND, and IMPLY constraints require a sequence of literals.""")

    raise ValueError("""Constraint expression could not be interpreted.""")

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _reify_elem_constr_expr(
    elem_constr_expr: ElemConstrExpr,
    solver: Solver,
) -> Lit:
    """
    Adds a reification of a constraint given in a elementary expression form, if
    it wasn't already reified. Otherwise, gets the corresponding reification literal.

    Returns an *optional* reification literal, which is defined such that it is
    present iff the elementary expression is valid/well-defined (typically
    meaning that all variables involved in the formula are present)
    """

    if elem_constr_expr in solver.reifications:
        return solver.reifications[elem_constr_expr]

    scope = _get_scope_of_elem_constr_expr(elem_constr_expr, solver)
    lits_of_scope = _flatten_scope_to_lits_conj(scope, False, solver)
    scope_lit = _get_or_make_new_scope_lit_from_scope_as_lits_conj(lits_of_scope, solver)
    
    reif_lit = Lit.geq(add_new_optional_variable((0,1), True, scope_lit, solver), 1)

    solver.reifications[elem_constr_expr] = reif_lit
    solver.reifications[elem_constr_expr.negation()] = reif_lit.negation()
    solver.constraints.append((elem_constr_expr, reif_lit))

    return reif_lit

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _get_or_make_new_scope_lit_from_scope_as_lits_conj(
    lits_of_scope: Tuple[Lit,...],
    solver: Solver,
) -> Lit:
    """
    Return a literal corresponding to the scope defined by the literals of a conjunctive scope.
    If there isn't already a scope literal like that, add it to the solver.

    In other words, return a literal l such that l <=> l1 & l2 & ... & ln
    """

    # If the (conjunctive) scope already exists, return its literal immediately.
    if lits_of_scope in solver.scopes:
        return solver.scopes[lits_of_scope]

    # The (conjunctive) scope is not already registered.
    # So we need to register with a new literal. There are two possibilities:
    #
    # - (1) if we find a literal that simplifies the conjunction,
    #   it will be used as the scope literal.
    #
    # - (2) if we do not find such a simplifying literal, we will
    # create and use as scope literal a new literal l such that:
    #   l => l1, l => l2, ..., l => ln, and l v (not l1) v (not l2) v ... v (not ln)
    #   (which is equivalent to l <=> l1 & l2 & ... & ln)

    simplified_lit_attempt: Optional[Lit] = None

    if len(lits_of_scope) == 1:
        simplified_lit_attempt = lits_of_scope[0]

    elif len(lits_of_scope) == 2:

        # If l1 => l2, the conjunction can be simplified to l1
        if solver.is_implication_true(lits_of_scope[0], lits_of_scope[1]):
            simplified_lit_attempt = lits_of_scope[0]

        # If l2 => l1, the conjunction can be simplified to l2
        elif solver.is_implication_true(lits_of_scope[1], lits_of_scope[0]):
            simplified_lit_attempt = lits_of_scope[1]

        # If l1 and l2 are exclusive (i.e. cannot be true at the same time,
        # i.e. l1 => (not l2)), the conjunctive scope literal is false.
        # However, we cannot directly use FALSE_LIT, because we need to
        # uniquely identify the literal as the conjunction of the other two
        # in some corner cases. So we create a new literal that is always false.
        if solver.is_implication_true(lits_of_scope[0], lits_of_scope[1].negation()):
            simplified_lit_attempt = Lit.geq(add_new_non_optional_variable((0, 0), False, solver), 1)

    # A simplication was found: case (1) in comment above
    if simplified_lit_attempt is not None:

        _insert_new_scope_from_scope_as_lits_conj_and_scope_lit(lits_of_scope, 
                                                                  simplified_lit_attempt, 
                                                                  solver)
        return simplified_lit_attempt

    # No simplication was found: case (2) in comment above
    else:

        scope_lit = Lit.geq(add_new_non_optional_variable((0, 0), False, solver), 1)

        lits: List[Lit] = [scope_lit]

        for l in lits_of_scope:
            _insert_implication_between_literals_on_non_optional_vars(scope_lit, l, solver)
            lits.append(l.negation())

        or_elem_form = ElemConstrExpr.from_lits_tighten_and_simplify_or(tuple(lits))

        _bind_elem_constr_expr(or_elem_form, TRUE_LIT, solver)  # TRUE_LIT is the tautology of the "empty scope" 
                                                                # (whose scope literal is TRUE_LIT as well)
        _insert_new_scope_from_scope_as_lits_conj_and_scope_lit(lits_of_scope,
                                                                  scope_lit, 
                                                                  solver)
        return scope_lit

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _bind_elem_constr_expr(
    elem_constr_expr: ElemConstrExpr,
    lit: Lit,
    solver: Solver,
) -> None:
    """
    Records that the given literal is true iff the given constraint (in
    elementary form) is true/satisfied. (i.e. lit <=> constraint)
    """

    # Compute the scope of the constraint elementary expression. It can be larger
    # than that of the literal.
    scope = _get_scope_of_elem_constr_expr(elem_constr_expr, solver)
    lits_of_scope = _flatten_scope_to_lits_conj(scope, False, solver)
    scope_lit = _get_or_make_new_scope_lit_from_scope_as_lits_conj(lits_of_scope, solver)
    
    # If the elementary expression is already reified to a literal l,
    # unify it (l) with the parameter literal.
    reif_lit = solver.reifications.get(elem_constr_expr, None)
    if reif_lit is not None:
        if lit != reif_lit:
            solver.constraints.append((ElemConstrExpr.from_lit(reif_lit), lit))
    
    # Otherwise and if the scopes are compatible, suggest literal to be the reified literal.
    elif scope_lit == solver.vars_presence_literals[lit.signed_var.var]:
        solver.reifications[elem_constr_expr] = lit
        solver.reifications[elem_constr_expr.negation()] = lit.negation()
        solver.constraints.append((elem_constr_expr, lit))
    
    # Otherwise (if the formula is not already reified, but literal cannot
    # be used directly because it has a different scope), reify it (with
    # another reification literal)
    else:
        reif_lit = _reify_elem_constr_expr(elem_constr_expr, solver)
        if lit != reif_lit:
            solver.constraints.append((ElemConstrExpr.from_lit(reif_lit), lit))

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _get_scope_of_elem_constr_expr(
    elem_constr_expr: ElemConstrExpr,
    solver: Solver,
) -> Tuple[Dict[SignedVar, BoundVal], Tuple[Lit,...]]:
    """
    
    Get a representation of the scope of the given elementary expression,
    depending on its kind, in the following tuple form:
    - 1st element (aka "required presences"): set of presence literals that
    appear in the expression.
    - 2nd element (aka "guards"): set of literals such that if one of them is
    true, the expression is valid/well-defined.
    """

    kind, terms = elem_constr_expr.kind, elem_constr_expr.terms

    match kind, terms:
        case ElemConstrExpr.Kind.LIT, Lit() as lit:

            prez_lit = solver.vars_presence_literals[lit.signed_var.var]

            return ({ prez_lit.signed_var: prez_lit.bound_value },
                    ())

        case ElemConstrExpr.Kind.OR, [Lit(), *_] as lits:

            prez_lits = [solver.vars_presence_literals[lit.signed_var.var] for lit in lits]

            return ({ prez_lit.signed_var: prez_lit.bound_value for prez_lit in prez_lits },
                    tuple(lit for lit in lits
                          if solver.vars_presence_literals[lit.signed_var.var] == TRUE_LIT))

        case ElemConstrExpr.Kind.AND, [Lit(), *_] as lits:

            prez_lits = [solver.vars_presence_literals[lit.signed_var.var] for lit in lits]

            return ({ prez_lit.signed_var: prez_lit.bound_value for prez_lit in prez_lits }, 
                    tuple(lit.negation() for lit in lits
                          if solver.vars_presence_literals[lit.negation().signed_var.var] == TRUE_LIT))
                
        case (ElemConstrExpr.Kind.MAX_DIFFERENCE,
              (Var() as var_from, Var() as var_to, int())
        ):
            prez_lit_var_from = solver.vars_presence_literals[var_from]
            prez_lit_var_to = solver.vars_presence_literals[var_to]

            return ({ prez_lit_var_from.signed_var: prez_lit_var_from.bound_value,
                     prez_lit_var_to.signed_var: prez_lit_var_to.bound_value },
                     ())

        case _:
            assert False

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _flatten_scope_to_lits_conj(
    conj_scope: Tuple[Dict[SignedVar, BoundVal], Tuple[Lit,...]],
    check_entailed_at_top_dec_level: bool,
    solver: Solver,
) -> Tuple[Lit,...]:
    """
    Flattens a scope, represented as a tuple of required presences and guards
    into a conjunction of literals
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_tautology(lit: Lit):

        if solver.is_literal_entailed(lit):
            if not check_entailed_at_top_dec_level:
                return True
            else:
                first_ev_idx = solver.get_first_event_implying_literal(lit)
                return first_ev_idx is None or first_ev_idx[0] == 0 # CHECKME
        
        return False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    required_presences: Dict[SignedVar, BoundVal] = conj_scope[0]
    guards: Tuple[Lit,...] = tuple(guard for guard in conj_scope[1] if guard != FALSE_LIT)

    flattened_conj_scope: Dict[SignedVar, BoundVal] = {}

    for signed_var, bound_value in required_presences.items():
        lit = Lit(signed_var, bound_value)

        # If the literal corresponds to a scope, instead of adding it to the
        # (conjunction of) literals being built, add the literals of the scope.
        lits = solver.scopes_reverse.get(lit, None)
        if lits is not None:

            for lit in lits:
                if (not is_tautology(lit)
                    and (lit.signed_var not in flattened_conj_scope
                        or lit.bound_value.is_stronger_than(flattened_conj_scope[lit.signed_var])                   )
                ):
                    flattened_conj_scope[lit.signed_var] = lit.bound_value

        # Otherwise, if the literal isn't known to always hold, add it
        elif not is_tautology(lit):
            flattened_conj_scope[lit.signed_var] = lit.bound_value

    for guard in guards:
        guard_neg = guard.negation()

        # If a literal is guarded, remove it from the conjunction.
        if (guard_neg.signed_var in flattened_conj_scope
            and flattened_conj_scope[guard_neg.signed_var].is_stronger_than(guard_neg.bound_value)
        ):
            weaker = Lit(guard_neg.signed_var, guard.bound_value+BoundVal(1))
            if is_tautology(weaker):
                flattened_conj_scope.pop(guard_neg.signed_var)
            else:
                flattened_conj_scope[guard_neg.signed_var] = weaker.bound_value

    # Convert the dict representation of the conjunction of literals
    # to a lexicographically sorted tuple.
    lits_of_scope = [Lit(signed_var, bound_value) 
                     for signed_var, bound_value in flattened_conj_scope.items()]
    lits_of_scope.sort()
    return tuple(lits_of_scope)

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _get_or_make_tautology_of_scope_from_scope_lit(
    scope_lit: Lit,
    solver: Solver,
) -> Lit:
    """
    Returns a literal whose presence is scope_literal and that is always true.

    This is functionally equivalent to creating a new optional boolean variable
    with domain {1} and with presence scope_literal, but ensuring that only
    one such variable is created in the scope corresponding to scope_literal.
    
    Indeed, the TRUE_LIT cannot work for this, because it (just as its
    variable, the special ZERO_VAR variable) is always present (in all scopes,
    not just this one).
    """

    if scope_lit in solver.scopes_tautologies:
        return solver.scopes_tautologies[scope_lit]

    else:
        lit = Lit.geq(add_new_optional_variable((1, 1), False, scope_lit, solver), 1)
        solver.scopes_tautologies[scope_lit] = lit
        return lit

#################################################################################
# HELPER FUNCTIONS
#################################################################################

def _insert_implication_between_literals_on_non_optional_vars(
    lit_from: Lit,
    lit_to: Lit,
    solver: Solver,
) -> None:
    """
    Adds an implication between two literals (defined on non-optional variables) to the solver.
    """

    if (solver.vars_presence_literals[lit_from.signed_var.var] != TRUE_LIT
        or solver.vars_presence_literals[lit_to.signed_var.var] != TRUE_LIT
    ):
        raise ValueError("Only implications between non-optional variables are supported")

    lit_from_neg = lit_from.negation()
    lit_to_neg = lit_to.negation()

    # If the implication is implicit/obvious, no need to add it.
    if (lit_to == TRUE_LIT
        or lit_from == FALSE_LIT
        or lit_from.entails(lit_to)
    ):
        pass

    # Otherwise, add the implication to the implication graph
    # (both from => to and (not to) => (not from))
    else:
        solver.non_optional_vars_implication_graph.setdefault(
            lit_from.signed_var, {}).setdefault(
            lit_from.bound_value, set()).add(lit_to)

        solver.non_optional_vars_implication_graph.setdefault(
            lit_to_neg.signed_var, {}).setdefault(
            lit_to_neg.bound_value, set()).add(lit_from_neg)

    # If from_literal is true, to_literal needs to be enforced as true.
    # (Indeed (from => to) <=> ((not from) or to))
    if solver.is_literal_entailed(lit_from):

        bound_update_result = solver.set_bound_value(lit_to.signed_var,
                                                     lit_to.bound_value,
                                                     Causes.ImplicationPropagation(lit_from))

        if isinstance(bound_update_result, InvalidBoundUpdateInfo):
            raise ValueError("""Inconsistency on the addition of the implication {0} => {1}""".format(lit_from, lit_to))

    # If to_literal is false, from_literal needs to be enforced as false.
    # (Indeed ((not to) => (not from)) <=> (to or (not from)))
    if solver.is_literal_entailed(lit_to_neg):

        bound_update_result = solver.set_bound_value(lit_from_neg.signed_var,
                                                     lit_from_neg.bound_value,
                                                     Causes.ImplicationPropagation(lit_to))

        if isinstance(bound_update_result, InvalidBoundUpdateInfo):
            raise ValueError("""Inconsistency on the addition of the implication {0} => {1}""".format(lit_from, lit_to))

#################################################################################

def _insert_new_scope_from_scope_as_lits_conj_and_scope_lit(
    lits_of_scope: Tuple[Lit,...],
    scope_lit: Lit,
    solver: Solver,
) -> None:
    """
    Adds to the solver a conjunctive scope consisting of the given literals, and
    corresponding to the given scope literal (i.e. it is true iff all the literals are).
    """

    if lits_of_scope in solver.scopes:
        raise ValueError("Could not insert a new scope because it already exists.")

    solver.scopes[lits_of_scope] = scope_lit
    solver.scopes_reverse[scope_lit] = lits_of_scope

#################################################################################
#################################################################################
#################################################################################
#################################################################################