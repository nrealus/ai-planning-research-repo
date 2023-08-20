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

def _insert_conjunctive_scope(
    solver: Solver,
    presence_literals_conjunction: Tuple[Literal,...],
    scope_literal: Literal
) -> None:

    assert presence_literals_conjunction not in solver.conjunctive_scopes

    solver.conjunctive_scopes[presence_literals_conjunction] = scope_literal
    solver.conjunctive_scopes_reverse[scope_literal] = presence_literals_conjunction

#################################################################################

def _add_reified_constraint(
    solver: Solver,
    constr_expr: ConstrExprAny,
    literal: Literal
) -> None:

    solver.reified_constraints.append((constr_expr, literal))

#################################################################################
# 
# def get_conjunctive_scope_literal(
#     solver: Solver,
#     presence_literals_conjunction: Tuple[Literal,...],
# ) -> Literal:
#     """
#     Returns a presence literal that is true if and only if all
#     given presence literal are true.
#     """
#     
#     return _get_or_make_new_conjunctive_presence_literal_from_full_conjunction(
#         solver,
#         _get_flattened_conjunctive_scope(
#             solver,
#             ({lit.signed_var: lit.bound_value for lit in presence_literals_conjunction}, tuple()),
#             False,
#     ))
# 
# #################################################################################
# 
# def _get_flattened_conjunctive_scope(
#     solver: Solver,
#     conjunctive_scope: Tuple[Dict[SignedVar, BoundValue], Tuple[Literal,...]],
#     check_for_top_decision_level: bool,
# ) -> List[Literal]:
#     """
#     Flattens a scope (describing the validity/definition conditions of an expression)
#     into a "full" conjunction of literals.
#     """
# 
#     def is_tautology(lit: Literal):
# 
#         return (solver.is_literal_entailed(lit)
#             and (not check_for_top_decision_level
#                 or solver.get_index_of_first_event_implying_literal(lit)[0] == 0
#         ))
#         
#     
#     scope_required_presences, scope_guards = conjunctive_scope
#     scope_guards = tuple(guard for guard in scope_guards if guard != FalseLiteral)
# 
#     literals_conjunction: Dict[SignedVar, BoundValue] = {}
# 
#     for s_var, b_val in scope_required_presences.items():
#         lit = Literal(s_var, b_val)
# 
#         # If a presence literal is defined as a conjunction of other literals,
#         # replace it with them.
#         flattened = solver.conjunctive_scopes_reverse.get(lit, None)
#         if flattened is not None:
# 
#             for l in flattened:
#                 if (not is_tautology(l)
#                     and (l.signed_var not in literals_conjunction
#                         or l.bound_value.is_stronger_than(literals_conjunction[l.signed_var])
#                 )):
#                     literals_conjunction[l.signed_var] = l.bound_value
#         
#         # Otherwise, if the presence literal is not considered to be a tautology,
#         # do add it to the conjunction
#         elif not is_tautology(lit):
#             literals_conjunction[lit.signed_var] = lit.bound_value
# 
#     for guard in scope_guards:
#         guard_neg = guard.negation()
#     
#         # If a presence literal is guarded, remove it from the conjunction.
#         if (guard_neg.signed_var in literals_conjunction
#             and literals_conjunction[guard_neg.signed_var].is_stronger_than(guard_neg.bound_value)
#         ):
#             # FIXME: + 1 used here instead of a defined constant
#             weaker = Literal(guard_neg.signed_var, BoundValue(guard.bound_value + BoundValue(1)))
#             if is_tautology(weaker):
#                 literals_conjunction.pop(guard_neg.signed_var)
#             else:
#                 literals_conjunction[guard_neg.signed_var] = weaker.bound_value
# 
#     # Convert the set of literals to a list, and sort it (lexicographically).
#     literals_conjunction_as_list = [Literal(signed_var, bound_value)
#         for signed_var, bound_value in literals_conjunction.items()]
#     literals_conjunction_as_list.sort()
#     return literals_conjunction_as_list
# 
# #################################################################################
# 
# def _get_or_make_new_conjunctive_presence_literal_from_full_conjunction(
#     solver: Solver,
#     literals_conjunction: List[Literal],
# ) -> Literal:
# 
#     # If the scope already exists, return it immediately.
#     if tuple(literals_conjunction) in solver.conjunctive_scopes:
#         return solver.conjunctive_scopes[tuple(literals_conjunction)]
# 
#     # We need to create a new literal l such that l <=> l1 & l2 & ... & ln
#     # (where li are the (presence) literals composing the conjunctive scope)
# 
#     # Simplify the conjunction of literals
#     simplified_literal_attempt: Optional[Literal] = None
# 
#     if len(literals_conjunction) == 1:
#         simplified_literal_attempt = literals_conjunction[0]
#     
#     elif len(literals_conjunction) == 2:
# 
#         # If l1 => l2, the conjunction can be simplified to l1
#         if solver.is_implication_true(literals_conjunction[0], literals_conjunction[1]):
#             simplified_literal_attempt = literals_conjunction[0]
#     
#         # If l2 => l1, the conjunction can be simplified to l2
#         elif solver.is_implication_true(literals_conjunction[1], literals_conjunction[0]):
#             simplified_literal_attempt = literals_conjunction[1]
#    
#         # If l1 and l2 are exclusive (i.e. cannot be true at the same time, i.e. l1 => !l2),
#         # the conjunctive scope literal is false. However, we cannot directly use FalseLiteral,
#         # because we need to uniquely identify the literal as the conjunction of the other two
#         # in some corner cases. So we create a new literal that is always false.
#         if solver.is_implication_true(literals_conjunction[0], literals_conjunction[1].negation()):
#             simplified_literal_attempt = Literal(
#                 SignedVar(_add_new_variable(solver, (0,0), False), False),
#                 BoundValue(-1),
#             )
# 
#     # If a simplification was found, we return it as the scope literal of the conjunction.
#     if simplified_literal_attempt is not None:
#         _insert_conjunctive_scope(solver, tuple(literals_conjunction), simplified_literal_attempt)
#         return simplified_literal_attempt
#     
#     # If no simplication was found, a new literal l is created such that:
#     # - l => l1, l => l2, ...
#     # - l v !l1 v !l2 v ... v !ln
#     # This literal l will indeed satisfy l <=> l1 & l2 & ... & ln.
#     else:
#         literal = Literal(
#             SignedVar(_add_new_variable(solver, (0,0), False), False),
#             BoundValue(-1),
#         )
#         clause_literals: List[Literal] = []
#         for lit in literals_conjunction:
#             _add_implication(solver, literal, lit)
#             clause_literals.append(lit.negation())
#             _enforce_expr(solver, ConstrExprOr(tuple(clause_literals)), [])
#         return literal
# 
# #################################################################################
# 
# def _enforce_expr(
#     solver: Solver,
#     constr_expr: ConstrExprAny2,
#     conjunctive_scope: List[Literal],
# ):
#     """
#     Enforce the given expression to be true whenever all literals of the scope are true.
# 
#     Similar to posintg a constraint in CP solvers.
# 
#     Internally; the expression is reified to an optional literal that is true,
#     when the expression is valid/defined and absent otherwise.
#     """
# 
#     scope_literal = _get_or_make_new_conjunctive_presence_literal_from_full_conjunction(
#         solver,
#         conjunctive_scope,
#     )
# 
#     # Bind the expression with an optional variable that is always true in the scope.
#     # This optional variable can be retrieved if it already exists, or can be created on the fly.
#     _bind(solver, constr_expr, _get_tautology_of_scope(solver, scope_literal))
# 
# #################################################################################
# 
# def _get_tautology_of_scope(
#     solver: Solver,
#     scope_literal: Literal,
# ) -> Literal:
#     """
#     Returns a literal whose presence is scope_literal and that is always true.
# 
#     This is functionally equivalent to creating a new optional boolean variable
#     with domain {1} and with presence scope_literal, but will ensure that only
#     one such variable is created in this scope
#     """
# 
#     if scope_literal in solver.conjunctive_scopes_tautologies:
#         return solver.conjunctive_scopes_tautologies[scope_literal]
# 
#     else:
#         var = add_new_optional_variable(solver, (1, 1), False, scope_literal)
#         literal = Literal(SignedVar(var, False), BoundValue(-1))
#         solver.conjunctive_scopes_tautologies[scope_literal] = literal
#         return literal
# 
# #################################################################################
# 
# def _get_expr_conjunctive_scope(
#     solver: Solver,
#     constr_expr: ConstrExprAny2,
# ) -> Tuple[Dict[SignedVar, BoundValue], Tuple[Literal,...]]:
#     """
#     Get the validity scope of an expression
#     """
#     
#     if isinstance(constr_expr, ConstrExprLiteral):
#         prez_lit = solver.vars_presence_literals[constr_expr.literal.signed_var.var]
#         return (
#             {prez_lit.signed_var: prez_lit.bound_value},
#             tuple(),
#         )
# 
#     elif isinstance(constr_expr, ConstrExprOr):
#         prez_lits = [solver.vars_presence_literals[lit.signed_var.var]
#             for lit in constr_expr.literals]
#         return (
#             {prez_lit.signed_var: prez_lit.bound_value for prez_lit in prez_lits},
#             tuple(lit for lit in constr_expr.literals
#                 if solver.vars_presence_literals[lit.signed_var.var] == TrueLiteral),
#         )
# 
#     elif isinstance(constr_expr, ConstrExprAnd):
#         prez_lits = [solver.vars_presence_literals[lit.signed_var.var]
#             for lit in constr_expr.literals]
#         return (
#             {prez_lit.signed_var: prez_lit.bound_value for prez_lit in prez_lits},
#             tuple(lit.negation() for lit in constr_expr.literals
#                 if solver.vars_presence_literals[lit.negation().signed_var.var] == TrueLiteral),
#         )
# 
#     elif isinstance(constr_expr, ConstrExprMaxDiffCnt):
#         prez_lit_from_var = solver.vars_presence_literals[constr_expr.from_var]
#         prez_lit_to_var = solver.vars_presence_literals[constr_expr.from_var]
#         return (
#             { prez_lit_from_var.signed_var: prez_lit_from_var.bound_value,
#                 prez_lit_to_var.signed_var: prez_lit_to_var.bound_value },
#             tuple(),
#         )
# 
#     else:
#         assert False
# 
# #################################################################################
# 
# def _bind(
#     solver: Solver,
#     constr_expr: ConstrExprAny2,
#     literal: Literal,
# ) -> None:
#     """
#     Record that literal <=> constr_expr
#     (i.e. literal is True iff constraint is satisfied)
#     """
# 
#     # FIXME expr = expr.decompose(model) ????
# 
#     # Compute the validity scope of the expression, which can be
#     # larger than that of the literal
#     expr_scope_literal = _get_or_make_new_conjunctive_presence_literal_from_full_conjunction(
#         solver,
#         _get_flattened_conjunctive_scope(
#             solver,
#             _get_expr_conjunctive_scope(solver, constr_expr),
#             False,
#         )
#     )
#     
#     # If the expression is already reified to a literal l,
#     # unify it (l) with the parameter literal.
#     reified_lit = solver.reified_constraints_literals.get(constr_expr, None)
#     if reified_lit is not None:
#         if literal != reified_lit:
#             _add_reified_constraint(solver, constr_expr, literal)
#     
#     # If the expression is not already reified and
#     # scopes are compatible, suggest literal to be the reified literal.
#     elif expr_scope_literal == solver.vars_presence_literals[literal.signed_var.var]:
#         _add_reified_constraint(solver, constr_expr, literal)
#     
#     # If the expression is not already reified,
#     # but literal cannot be used directly because it has a different scope
#     else:
#         reified_lit = None#FIXME_reify_core(constr_expr)
#         if literal != reified_lit:
#             _add_reified_constraint(solver, ConstrExprLiteral(reified_lit), literal)
# 
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

def post_constraints(
    solver: Solver,
    reasoners: List[SolverReasoner],
    reified_constraints: List[Tuple[ConstrExprAny, Literal]],
#) -> Optional[Tuple[
) -> Optional[
    Union[SolverConflictInfo.InvalidBoundUpdate, SolverConflictInfo.ReasonerExplanation],
]:
#     SolverReasoner,
# ]]:
    """
    """
    
    for reified_constraint in reified_constraints:
        res = _post_constraint(solver, reasoners, reified_constraint)

        if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
            return res

    return None

#################################################################################
# NOTE: THE SIMPLEST / CLEAREST OPTION WOULD PROBABLY BE TO
# "ISOLATE" OR "ENCAPSULATE" SCOPES AND REIFICATIONS DATA
# IN 2 NESTED CLASSES IN THE SOLVER CLASS.
# ADDITIONALLY IT COULD BE POSSIBLE (but seems weird if these
# would be nested classes of Solver) TO PASS THEM AS PARAMETERS
# IN THESE API FUNCTIONS

def _post_constraint(
    solver: Solver,
    reasoners: List[SolverReasoner],
    reified_constraint: Tuple[ConstrExprAny, Literal],
) -> Optional[SolverConflictInfo.InvalidBoundUpdate]:
#) -> Optional[Tuple[
#    Union[SolverConflictInfo.InvalidBoundUpdate, SolverConflictInfo.ReasonerExplanation],
#    SolverReasoner,
#]]:
    """
    """
    
    assert solver.dec_level == 0

    sat_reasoner = [reasoner for reasoner in reasoners if isinstance(reasoner, SATReasoner)][0]
#    diff_reasoner = ...

    (constr_expr, reified_constr_literal) = reified_constraint

    scope_literal = solver.vars_presence_literals[reified_constr_literal.signed_var.var]

    # If the scope of the constraint is false, then the constraint
    # is ignored because it's absent/undefined/not valid.
    if solver.is_literal_entailed(scope_literal.negation()):
        return None

    if isinstance(constr_expr, ConstrExprLiteral):

        assert solver.is_implication_true(
            scope_literal,
            solver.vars_presence_literals[constr_expr.literal.signed_var.var])

        _add_clause_from_raw_clause_literals_and_scope(
            solver,
            sat_reasoner, 
            (reified_constr_literal.negation(), constr_expr.literal),
            scope_literal,
            False,
        )
        _add_clause_from_raw_clause_literals_and_scope(
            solver,
            sat_reasoner, 
            (constr_expr.literal.negation(), reified_constr_literal),
            scope_literal,
            False,
        )

    elif isinstance(constr_expr, ConstrExprMaxDiffCnt):
        # _add_reified_edge(
        #     solver,
        #     diff_reasoner,
        #     reified_constr_literal,
        #     constr_expr.to_var,
        #     constr_expr.from_var,
        #     constr_expr.max_diff,
        # )
        pass

    elif isinstance(constr_expr, ConstrExprOr):

        if solver.is_literal_entailed(reified_constr_literal):
            _add_clause_from_raw_clause_literals_and_scope(
                solver,
                sat_reasoner,
                constr_expr.literals,
                scope_literal,
                False,
            )
            return None
        
        elif solver.is_literal_entailed(reified_constr_literal.negation()):
            for lit in constr_expr.literals:
                res = _add_clause_from_raw_clause_literals_and_scope(
                    solver,
                    sat_reasoner,
                    (lit.negation(),),
                    scope_literal,
                    False,
                )
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
            return None
        
        else:

            res = _add_clause_from_raw_clause_literals_and_scope(
                solver,
                sat_reasoner,
                (reified_constr_literal.negation(),)+constr_expr.literals,
                scope_literal,
                True,
            )
            if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                return res
            
            for literal in constr_expr.literals:
                res = _add_clause_from_raw_clause_literals_and_scope(
                    solver,
                    sat_reasoner,
                    (literal.negation(), reified_constr_literal),
                    scope_literal,
                    False,
                )
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res

            return None

    elif isinstance(constr_expr, ConstrExprAnd):

        return _post_constraint(
            solver,
            reasoners,
            (constr_expr.negation(), reified_constr_literal.negation())
        )

    else:
        assert False

#################################################################################

def _add_clause_from_raw_clause_literals_and_scope(
    solver: Solver,
    sat_reasoner: SATReasoner,
    raw_clause_literals: Tuple[Literal,...],
    raw_scope_literal: Literal,
# FIXME: shouldn't we actually ALWAYS want to do this ?
    return_false_if_tautological_clause_literals: bool,
) -> Union[bool, SolverConflictInfo.InvalidBoundUpdate]:

    assert solver.dec_level == 0

    clause_literals: List[Literal] = list(raw_clause_literals)
    processed_scope_literal: Literal = raw_scope_literal

    # Sort clause literals (lexicographically) and remove duplicate
    # literals (weaker literals on the same signed variable).

    clause_literals.sort()

    n = len(raw_clause_literals)
    i = 0
    while i < n-1:
        # Because the clause literals are now lexicographically sorted,
        # we know that if two literals are on the same signed variable,
        # the weaker one is necessarily the next one.
        if clause_literals[i].entails(clause_literals[i+1]):
            clause_literals.pop(i)
        else:
            i += 1

    # Remove clause literals that are guaranteed to not become true
    # (i.e. whose value is False / whose negation literal is entailed)

    n = len(clause_literals)
    i = 0
    while i < n:
        if solver.is_literal_entailed(clause_literals[i].negation()):
            clause_literals.pop(i)
        else:
            i += 1

    if return_false_if_tautological_clause_literals:
        n = len(raw_clause_literals)
        i = 0
        while i < n-1:
            if clause_literals[i].signed_var == clause_literals[i+1].signed_var.opposite_signed_var():
                if clause_literals[i].bound_value + clause_literals[i+1].bound_value >= 0:
                    return False

    # Analyze processed clause literals and scope.
    #
    # If the processing of the clause literals removed all of them,
    # then the scope must be enforced to be false.
    #
    # If the processed clause literals are not empty, the we must make
    # sure the clause added to the solver (or rather its sat reasoner)
    # can be unit propagated safely, as its literals' variables can be optional.
    #
    # NOTE: this could be generalized to look at literals in the clause as potential scopes

    if len(clause_literals) == 0:

        processed_scope_literal_neg = processed_scope_literal.negation()

        scope_negation_enforcement_result = solver.set_bound_value(
            processed_scope_literal_neg.signed_var,
            processed_scope_literal_neg.bound_value,
            SolverCause.Encoding()
        ) 
        if isinstance(scope_negation_enforcement_result, SolverConflictInfo.InvalidBoundUpdate):
            return scope_negation_enforcement_result
        else:
            return True

    elif all(solver.is_implication_true(
        solver.vars_presence_literals[lit.signed_var.var],processed_scope_literal)
        for lit in clause_literals
    ):
        pass
    
    else:
        clause_literals.append(processed_scope_literal.negation())
        processed_scope_literal = TrueLiteral

    sat_reasoner.add_new_fixed_clause_with_scope(
        tuple(clause_literals),
        processed_scope_literal)
    return True

#################################################################################
#################################################################################
#################################################################################
#################################################################################
