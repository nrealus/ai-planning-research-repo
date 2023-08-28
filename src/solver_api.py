from __future__ import annotations

#################################################################################

from typing import Dict, List, Optional, Tuple

from fundamentals import (
    Var, ZERO_VAR,
    SignedVar, BoundVal, Lit, TRUE_LIT, FALSE_LIT,
    ConstraintExpressionAtoms,
    ConstraintExpression,
    ConstraintElementaryExpression,
#    ReifiedConstraint,
    tighten_literals,
    are_tightened_literals_tautological,
)

from solver import SolverCauses, SolverConflictInfo, Solver

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
    solver: Solver,
    initial_domain: Tuple[int, int],
    controllable: bool,
) -> Var:
    """
    Adds a new non-optional variable to the solver and returns it.
    """

    return _add_new_variable(solver, initial_domain, controllable, TRUE_LIT)

#################################################################################

def add_new_optional_variable(
    solver: Solver,
    initial_domain: Tuple[int, int],
    controllable: bool,
    presence_literal: Lit,
) -> Var:
    """
    Adds a new optional variable to the solver and returns it.
    """

    return _add_new_variable(solver, initial_domain, controllable, presence_literal)

#################################################################################

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
    
    var = add_new_non_optional_variable(solver, (0,1), True)
    
    lit = Lit.geq(var, 1)
    _insert_new_conjunctive_scope(solver, (lit,), lit)
    _insert_implication_between_literals_on_non_optional_vars(solver, lit, scope_literal)
    
    return var

#################################################################################

def _add_new_variable(
    solver: Solver,
    initial_domain: Tuple[int, int],
    controllable: bool,
    presence_literal: Lit,
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
    
    solver.bound_values[SignedVar(var, False)] = BoundVal(-initial_domain[0])
    solver.bound_values[SignedVar(var, True)] = BoundVal(initial_domain[1])

    return var
        
#################################################################################
# CONSTRAINT ADDITION
# (NOTE: Should probably be changed into a class, so that the nested functions could be tested...)
#################################################################################

def add_constraint(
    solver: Solver,
    constraint_expression: ConstraintExpression.AnyExpr,
    conjunctive_scope_literals: Tuple[Lit,...],
#) -> ReifiedConstraint:
) -> Tuple[ConstraintElementaryExpression.AnyExpr, Lit]:
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

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def transform_leq(
        atom_left: ConstraintExpressionAtoms.Int,
        atom_right: ConstraintExpressionAtoms.Int,
    ) -> ConstraintElementaryExpression.AnyExpr:

        offset_difference = atom_right.offset - atom_left.offset

        if atom_right.var == atom_left.var:
            if 0 <= offset_difference:
                return ConstraintElementaryExpression.LitExpr(TRUE_LIT)
            else:
                return ConstraintElementaryExpression.LitExpr(FALSE_LIT)
        
        elif atom_right.var == ZERO_VAR:
            return ConstraintElementaryExpression.LitExpr(Lit.leq(atom_left.var, offset_difference))

        elif atom_left.var == ZERO_VAR:
            return ConstraintElementaryExpression.LitExpr(Lit.geq(atom_right.var, -offset_difference))

        else:
            return ConstraintElementaryExpression.MaxDiffCnt(atom_left.var, atom_right.var, offset_difference)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def transform_or(literals: Tuple[Lit,...]) -> ConstraintElementaryExpression.AnyExpr:

        tightened_literals = tighten_literals(literals)

        if are_tightened_literals_tautological(tightened_literals):
            return ConstraintElementaryExpression.LitExpr(TRUE_LIT)

        elif len(tightened_literals) == 0:
            return ConstraintElementaryExpression.LitExpr(FALSE_LIT)

        elif len(tightened_literals) == 1:
            return ConstraintElementaryExpression.LitExpr(tightened_literals[0])

        else:
            return ConstraintElementaryExpression.Or(tightened_literals)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def transform_and_prepare_eq(
        atom1: ConstraintExpressionAtoms.AnyAtom,
        atom2: ConstraintExpressionAtoms.AnyAtom,
    ) -> ConstraintElementaryExpression.AnyExpr:

        if atom1.var == atom2.var:
            return ConstraintElementaryExpression.LitExpr(TRUE_LIT)

        elif isinstance(atom1, ConstraintExpressionAtoms.Bool) and isinstance(atom2, ConstraintExpressionAtoms.Bool):
            lit1 = Lit.geq(atom1.var, 1)
            lit2 = Lit.geq(atom2.var, 1)
            imply_1_2 = reify_elementary_expression(transform_or((lit1.negation(), lit2)))
            imply_2_1 = reify_elementary_expression(transform_or((lit2.negation(), lit1)))
            return transform_or((imply_1_2.negation(), imply_2_1.negation()))

        elif isinstance(atom1, ConstraintExpressionAtoms.Int) and isinstance(atom2, ConstraintExpressionAtoms.Int):
            leq_1_2 = reify_elementary_expression(transform_leq(atom1, atom2))
            leq_2_1 = reify_elementary_expression(transform_leq(atom2, atom1))
            return transform_or((leq_1_2.negation(), leq_2_1.negation()))

        else:
            raise ValueError("""Incompatible atom types.""")

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_tautology_of_scope(
        scope_lit: Lit,
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

        if scope_lit in solver.conjunctive_scopes_tautologies:
            return solver.conjunctive_scopes_tautologies[scope_lit]

        else:
            lit = Lit.geq(add_new_optional_variable(solver, (1, 1), False, scope_lit), 1)
            solver.conjunctive_scopes_tautologies[scope_lit] = lit
            return lit

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_conjunctive_scope_of_elementary_expr(
        constr_elementary_expr: ConstraintElementaryExpression.AnyExpr,
    ) -> Tuple[Dict[SignedVar, BoundVal], Tuple[Lit,...]]:
        """
        
        Get a representation of the scope of the given elementary expression,
        depending on its kind, in the following tuple form:
        - 1st element (aka "required presences"): set of presence literals that
        appear in the expression.
        - 2nd element (aka "guards"): set of literals such that if one of them is
        true, the expression is valid/well-defined.
        """
        
        if isinstance(constr_elementary_expr, ConstraintElementaryExpression.LitExpr):
            prez_lit = solver.vars_presence_literals[constr_elementary_expr.literal.signed_var.var]
            return (
                { prez_lit.signed_var: prez_lit.bound_value },
                ()
            )

        elif isinstance(constr_elementary_expr, ConstraintElementaryExpression.Or):
            prez_lits = [solver.vars_presence_literals[lit.signed_var.var]
                for lit in constr_elementary_expr.literals]
            return (
                { prez_lit.signed_var: prez_lit.bound_value for prez_lit in prez_lits },
                tuple(lit for lit in constr_elementary_expr.literals
                    if solver.vars_presence_literals[lit.signed_var.var] == TRUE_LIT),
            )

        elif isinstance(constr_elementary_expr, ConstraintElementaryExpression.And):
            prez_lits = [solver.vars_presence_literals[lit.signed_var.var]
                for lit in constr_elementary_expr.literals]
            return (
                { prez_lit.signed_var: prez_lit.bound_value for prez_lit in prez_lits },
                tuple(lit.negation() for lit in constr_elementary_expr.literals
                    if solver.vars_presence_literals[lit.negation().signed_var.var] == TRUE_LIT),
            )

        elif isinstance(constr_elementary_expr, ConstraintElementaryExpression.MaxDiffCnt):
            prez_lit_from_var = solver.vars_presence_literals[constr_elementary_expr.from_var]
            prez_lit_to_var = solver.vars_presence_literals[constr_elementary_expr.from_var]
            return (
                { prez_lit_from_var.signed_var: prez_lit_from_var.bound_value,
                  prez_lit_to_var.signed_var: prez_lit_to_var.bound_value },
                (),
            )

        else:
            assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def flatten_conjunctive_scope_into_conjunctive_scope_literals(
        conj_scope: Tuple[Dict[SignedVar, BoundVal], Tuple[Lit,...]],
        check_top_dec_level: bool,
    ) -> Tuple[Lit,...]:
        """
        Flattens a scope, represented as a tuple of required presences and guards
        into a conjunction of literals
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def is_tautology(lit: Lit):

            return (solver.is_literal_entailed(lit)
                and (not check_top_dec_level
# FIXME: ambiguity: use 0 or None ?                    or solver.get_index_of_first_event_implying_literal(lit)[0] == 0
                    or solver.get_index_of_first_event_implying_literal(lit) is None))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        required_presences: Dict[SignedVar, BoundVal] = conj_scope[0]
        guards: Tuple[Lit,...] = tuple(guard for guard in conj_scope[1] if guard != FALSE_LIT)

        flattened_conj_scope: Dict[SignedVar, BoundVal] = {}

        for signed_var, bound_value in required_presences.items():
            lit = Lit(signed_var, bound_value)

            # If the literal corresponds to a scope, instead of adding it to the
            # (conjunction of) literals being built, add the literals of the scope.
            lits = solver.conjunctive_scopes_reverse.get(lit, None)
            if lits is not None:

                for lit in lits:
                    if (not is_tautology(lit)
                        and (lit.signed_var not in flattened_conj_scope
                            or lit.bound_value.is_stronger_than(flattened_conj_scope[lit.signed_var])
                        )
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
                weaker = Lit(guard_neg.signed_var, BoundVal(guard.bound_value + 1))
                if is_tautology(weaker):
                    flattened_conj_scope.pop(guard_neg.signed_var)
                else:
                    flattened_conj_scope[guard_neg.signed_var] = weaker.bound_value

        # Convert the dict representation of the conjunction of literals
        # to a lexicographically sorted tuple.
        conj_scope_lits = [Lit(signed_var, bound_value) for signed_var, bound_value in flattened_conj_scope.items()]
        conj_scope_lits.sort()
        return tuple(conj_scope_lits)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def get_or_make_new_scope_literal_from_conjunctive_scope_literals(
        conj_scope_lits: Tuple[Lit,...],
    ) -> Lit:
        """
        Return a literal corresponding to the scope defined by the literals of a conjunctive scope.
        If there isn't already a scope literal like that, add it to the solver.

        In other words, return a literal l such that l <=> l1 & l2 & ... & ln
        """

        # If the scope already exists, return it immediately.
        if conj_scope_lits in solver.conjunctive_scopes:
            return solver.conjunctive_scopes[conj_scope_lits]

        # Look for a literal simplifying the conjunction

        simplified_literal_attempt: Optional[Lit] = None

        if len(conj_scope_lits) == 1:
            simplified_literal_attempt = conj_scope_lits[0]

        elif len(conj_scope_lits) == 2:

            # If l1 => l2, the conjunction can be simplified to l1
            if solver._is_implication_true(conj_scope_lits[0], conj_scope_lits[1]):
                simplified_literal_attempt = conj_scope_lits[0]

            # If l2 => l1, the conjunction can be simplified to l2
            elif solver._is_implication_true(conj_scope_lits[1], conj_scope_lits[0]):
                simplified_literal_attempt = conj_scope_lits[1]
    
            # If l1 and l2 are exclusive (i.e. cannot be true at the same time, i.e. l1 => (not l2)),
            # the conjunctive scope literal is false. However, we cannot directly use FALSE_LIT,
            # because we need to uniquely identify the literal as the conjunction of the other two
            # in some corner cases. So we create a new literal that is always false.
            if solver._is_implication_true(conj_scope_lits[0], conj_scope_lits[1].negation()):
                simplified_literal_attempt = Lit.geq(add_new_non_optional_variable(solver, (0, 0), False), 1)

        # If a simplification was found, we return it as the scope literal of the conjunction.
        if simplified_literal_attempt is not None:
            _insert_new_conjunctive_scope(solver, conj_scope_lits, simplified_literal_attempt)
            return simplified_literal_attempt

        # If no simplication was found, a new literal l is created
        # such that l => l1, l => l2, ..., l => ln, and l v (not l1) v (not l2) v ... v (not ln).
        # (which is equivalent to l <=> l1 & l2 & ... & ln)
        else:
            lit = Lit.geq(add_new_non_optional_variable(solver, (0, 0), False), 1)

            lits: List[Lit] = [lit]
            for l in conj_scope_lits:
                _insert_implication_between_literals_on_non_optional_vars(solver, lit, l)
                lits.append(l.negation())

            bind_elementary_expression(
                transform_or(tuple(lits)),
                get_tautology_of_scope(get_or_make_new_scope_literal_from_conjunctive_scope_literals(())))

            _insert_new_conjunctive_scope(solver, conj_scope_lits, lit)
            return lit

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def reify_elementary_expression(
        constr_elementary_expr: ConstraintElementaryExpression.AnyExpr,
    ) -> Lit:
        """
        Adds a reification of a constraint given in a elementary expression form, if
        it wasn't already reified. Otherwise, gets the corresponding reification literal.

        Returns an *optional* reification literal, which is defined such that it is
        present iff the elementary expression is valid/well-defined (typically
        meaning that all variables involved in the formula are present)
        """

        if constr_elementary_expr in solver.reifications:
            return solver.reifications[constr_elementary_expr]
    
        scope_lit = get_or_make_new_scope_literal_from_conjunctive_scope_literals(
            flatten_conjunctive_scope_into_conjunctive_scope_literals(
                get_conjunctive_scope_of_elementary_expr(constr_elementary_expr),
                False))
        
        reif_lit = Lit.geq(add_new_optional_variable(solver, (0,1), True, scope_lit), 1)

        solver.reifications[constr_elementary_expr] = reif_lit
        solver.reifications[constr_elementary_expr.negation()] = reif_lit.negation()
        solver.constraints.append((constr_elementary_expr, reif_lit))

        return reif_lit

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def bind_elementary_expression(
        constr_elementary_expr: ConstraintElementaryExpression.AnyExpr,
        lit: Lit,
    ) -> None:
        """
        Records that the given literal is true iff the given constraint (in
        elementary form) is true/satisfied. (i.e. lit <=> constraint)
        """

        # Compute the scope of the constraint elementary expression. It can be larger
        # than that of the literal.
        expr_scope_literal = get_or_make_new_scope_literal_from_conjunctive_scope_literals(
            flatten_conjunctive_scope_into_conjunctive_scope_literals(
                get_conjunctive_scope_of_elementary_expr(constr_elementary_expr),
                False))
        
        # If the elementary expression is already reified to a literal l,
        # unify it (l) with the parameter literal.
        reification_literal = solver.reifications.get(constr_elementary_expr, None)
        if reification_literal is not None:
            if lit != reification_literal:
                solver.constraints.append(
                    (ConstraintElementaryExpression.LitExpr(reification_literal), lit))
        
        # Otherwise and if the scopes are compatible, suggest literal to be the reified literal.
        elif expr_scope_literal == solver.vars_presence_literals[lit.signed_var.var]:
            solver.reifications[constr_elementary_expr] = lit
            solver.reifications[constr_elementary_expr.negation()] = lit.negation()
            solver.constraints.append((constr_elementary_expr, lit))
        
        # Otherwise (if the formula is not already reified, but literal cannot
        # be used directly because it has a different scope), reify it (with
        # another reification literal)
        else:
            reification_literal = reify_elementary_expression(constr_elementary_expr)
            if lit != reification_literal:
                solver.constraints.append(
                    (ConstraintElementaryExpression.LitExpr(reification_literal), lit))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def transform_and_prepare_constraint_expression_into_elementary_form(
        constr_expr: ConstraintExpression.AnyExpr,
    ) -> ConstraintElementaryExpression.AnyExpr:
        """
        Transforms a constraint expression into elementary form
        (or constraint elementary expression).

        Also, may reify intermediate constraints, while preparing for
        the reification of the whole constraint.
        """
        
        if isinstance(constr_expr, ConstraintExpression.Leq):
            return transform_leq(constr_expr.left_atom, constr_expr.right_atom)

        elif isinstance(constr_expr, ConstraintExpression.Lt):
            return transform_leq(
                constr_expr.left_atom,
                ConstraintExpressionAtoms.Int(constr_expr.right_atom.var, constr_expr.right_atom.offset-1))

        elif isinstance(constr_expr, ConstraintExpression.Geq):
            return transform_leq(constr_expr.right_atom, constr_expr.left_atom)

        elif isinstance(constr_expr, ConstraintExpression.Gt):
            return transform_leq(
                constr_expr.left_atom,
                ConstraintExpressionAtoms.Int(constr_expr.left_atom.var, constr_expr.left_atom.offset-1))

        elif isinstance(constr_expr, ConstraintExpression.Eq):
            return transform_and_prepare_eq(constr_expr.atom1, constr_expr.atom2)

        elif isinstance(constr_expr, ConstraintExpression.Neq):
            return transform_and_prepare_eq(constr_expr.atom1, constr_expr.atom2).negation()

        elif isinstance(constr_expr, ConstraintExpression.Or):
            return transform_or(constr_expr.literals)

        elif isinstance(constr_expr, ConstraintExpression.And):
            return transform_or(tuple(lit.negation() for lit in constr_expr.literals)).negation()

        elif isinstance(constr_expr, ConstraintExpression.Imply):
            return transform_or((constr_expr.from_literal.negation(), constr_expr.to_literal))
        
        else:
            assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    constr_elementary_expr = transform_and_prepare_constraint_expression_into_elementary_form(constraint_expression)
    scope_lit = get_or_make_new_scope_literal_from_conjunctive_scope_literals(conjunctive_scope_literals)

    # Bind the formula with an optional variable that is always true in the scope.
    # This optional variable can be retrieved if it already exists, or can be created on the fly.
    tauto = get_tautology_of_scope(scope_lit)
    bind_elementary_expression(constr_elementary_expr, tauto)

    return (constr_elementary_expr, tauto)

#################################################################################
# HELPER FUNCTIONS
#################################################################################

def _insert_implication_between_literals_on_non_optional_vars(
    solver: Solver,
    from_literal: Lit,
    to_literal: Lit,
) -> None:
    """
    Adds an implication between two literals (defined on non-optional variables) to the solver.
    """

    if (solver.vars_presence_literals[from_literal.signed_var.var] != TRUE_LIT
        or solver.vars_presence_literals[to_literal.signed_var.var] != TRUE_LIT
    ):
        raise ValueError("Only implications between non-optional variables are supported")

    from_literal_neg = from_literal.negation()
    to_literal_neg = to_literal.negation()

    # If the implication is implicit/obvious, no need to add it.
    if (to_literal == TRUE_LIT
        or from_literal == FALSE_LIT
        or from_literal.entails(to_literal)
    ):
        pass

    # Otherwise, add the implication to the implication graph
    # (both from => to and (not to) => (not from))
    else:
        solver.non_optional_vars_implication_graph.setdefault(
            from_literal.signed_var, {}).setdefault(
            from_literal.bound_value, set()).add(to_literal)

        solver.non_optional_vars_implication_graph.setdefault(
            to_literal_neg.signed_var, {}).setdefault(
            to_literal_neg.bound_value, set()).add(from_literal_neg)

    # If from_literal is true, to_literal needs to be enforced as true.
    # (Indeed (from => to) <=> ((not from) or to))
    if solver.is_literal_entailed(from_literal):

        bound_update_result = solver.set_bound_value(
            to_literal.signed_var,
            to_literal.bound_value,
            SolverCauses.ImplicationPropagation(from_literal))

        if isinstance(bound_update_result, SolverConflictInfo.InvalidBoundUpdate):
            raise ValueError("""Inconsistency on the addition of the implication {0} => {1}""".format(from_literal, to_literal))

    # If to_literal is false, from_literal needs to be enforced as false.
    # (Indeed ((not to) => (not from)) <=> (to or (not from)))
    if solver.is_literal_entailed(to_literal_neg):

        bound_update_result = solver.set_bound_value(
            from_literal_neg.signed_var,
            from_literal_neg.bound_value,
            SolverCauses.ImplicationPropagation(to_literal_neg))

        if isinstance(bound_update_result, SolverConflictInfo.InvalidBoundUpdate):
            raise ValueError("""Inconsistency on the addition of the implication {0} => {1}""".format(from_literal, to_literal))

#################################################################################

def _insert_new_conjunctive_scope(
    solver: Solver,
    conjunctive_scope_literals: Tuple[Lit,...],
    scope_literal: Lit
) -> None:
    """
    Adds to the solver a conjunctive scope consisting of the given literals, and
    corresponding to the given scope literal (i.e. it is true iff all the literals are).
    """

    if conjunctive_scope_literals in solver.conjunctive_scopes:
        raise ValueError("Conjunctive scope already exists.")

    solver.conjunctive_scopes[conjunctive_scope_literals] = scope_literal
    solver.conjunctive_scopes_reverse[scope_literal] = conjunctive_scope_literals

#################################################################################
#################################################################################
#################################################################################
#################################################################################