"""
"""

from __future__ import annotations

#################################################################################

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, NamedTuple, Optional, Sequence, Set, Tuple, Union
from enum import Enum, auto

from src.fundamentals import Bound, Var, Lit, SignedVar, TRUE_LIT, IntAtom, BoolAtom, FracAtom, SymbAtom, Atom, ZERO_VAR
from src.constraint_expressions import ConstrExpr
from src.planning_and_acting.common import ChronicleId, Chronicle, Constraint, Condition, Effect, Value_WIP, StateVar, Task, SubTask
from src.solver.solver import Solver, SolverState

#################################################################################
#
#################################################################################

MAX_INT = 2**64

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def atoms_unifiable(
    atom1: Atom,
    atom2: Atom,
    solver: Solver
) -> bool:

    match atom1, atom2:
        case BoolAtom(), BoolAtom():
            pass
        case IntAtom(), IntAtom():
            pass
        case FracAtom(), FracAtom():
            pass
        case SymbAtom(_, symb_type1), SymbAtom(_, symb_type2):
            # if (not symb_type1.is_subtype_of(symb_type2)             # TODO: add type hierarchy to solver ?
            #     and not symb_type2.is_subtype_of(symb_type1)         # TODO: add type hierarchy to solver ?
            # ):
            #     return False
            pass
        case _:
            return False

    match atom1:
        case BoolAtom(var):
            l1, u1 = (-solver.state.bound_of(SignedVar.minus(var)),
                      solver.state.bound_of(SignedVar.plus(var)))
        case IntAtom(var, offset_cst):
            l1, u1 = (-solver.state.bound_of(SignedVar.minus(var)) + offset_cst,
                      solver.state.bound_of(SignedVar.plus(var)) + offset_cst)
        case FracAtom(numer_int_atom, denom):
            l1, u1 = ((-solver.state.bound_of(SignedVar.minus(numer_int_atom.var)) + numer_int_atom.offset_cst) / denom,
                      (solver.state.bound_of(SignedVar.plus(numer_int_atom.var)) + numer_int_atom.offset_cst) / denom)
        case SymbAtom(int_view_atom):
            l1, u1 = (-solver.state.bound_of(SignedVar.minus(int_view_atom.var)) + int_view_atom.offset_cst,
                      solver.state.bound_of(SignedVar.plus(int_view_atom.var)) + int_view_atom.offset_cst)
    
    match atom2:
        case BoolAtom(var):
            l2, u2 = (-solver.state.bound_of(SignedVar.minus(var)),
                      solver.state.bound_of(SignedVar.plus(var)))
        case IntAtom(var, offset_cst):
            l2, u2 = (-solver.state.bound_of(SignedVar.minus(var)) + offset_cst,
                      solver.state.bound_of(SignedVar.plus(var)) + offset_cst)
        case FracAtom(numer_int_atom, denom):
            l2, u2 = ((-solver.state.bound_of(SignedVar.minus(numer_int_atom.var)) + numer_int_atom.offset_cst) / denom,
                      (solver.state.bound_of(SignedVar.plus(numer_int_atom.var)) + numer_int_atom.offset_cst) / denom)
        case SymbAtom(int_view_atom):
            l2, u2 = (-solver.state.bound_of(SignedVar.minus(int_view_atom.var)) + int_view_atom.offset_cst,
                      solver.state.bound_of(SignedVar.plus(int_view_atom.var)) + int_view_atom.offset_cst)

    return not (u1 < l2 or u2 < l1)

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def atom_sequences_unifiable(
    atoms1: Sequence[Atom],
    atoms2: Sequence[Atom],
    solver: Solver
) -> bool:
    
    if len(atoms1) != len(atoms2):
        return False
    for (a, b) in zip(atoms1, atoms2):
        if not atoms_unifiable(a, b, solver):
            return False
    return True

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# #class UnpopulatedProblem(NamedTuple):
# class TemplateProblem(NamedTuple):
# #    root_chronicle_id: ChronicleId
#     chronicles: Dict[ChronicleId, Chronicle]    # chronicle_templates?
#     free_chronicle_templates_ids_with_num_to_instantiate: Dict[ChronicleId, int]
#     task_dependent_chronicle_templates_ids: Set[ChronicleId]
#     max_depth: int

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

class InstancesProblem(NamedTuple):

#    root_chronicle_id: ChronicleId

    chronicle_instances: Dict[ChronicleId, Chronicle]

    chronicle_instances_origin_template: Dict[ChronicleId, Optional[ChronicleId]]
    # NOTE: The id of the chronicle is obviously not in chronicle_instances

    chronicle_instances_subtasks_possible_refinements: Dict[Tuple[ChronicleId, int], List[ChronicleId]]

    chronicle_instances_subtasks_possible_refinements_reverse: Dict[ChronicleId, Tuple[ChronicleId, int]]

    chronicle_instances_presence_assumptions: Dict[ChronicleId, Optional[bool]]
    """
    Represents a value to enforce / assume for the presence of the chronicle.
    No assumption = not in this dict.
    """

#    solver: Solver

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def populate_instances_problem(
    instances_problem: InstancesProblem,
    solver: Solver,
    chronicle_templates: Dict[ChronicleId, Chronicle],
    free_chronicle_template_ids_with_num_to_instantiate: Dict[ChronicleId, int],
    task_dependent_chronicle_template_ids: Set[ChronicleId],
    max_depth: int,
):

    max_chr_inst_id = max(instances_problem.chronicle_instances.keys())
    chr_inst_id_counter = max_chr_inst_id

    # Populate the problem with free / non task-dependent chronicles instances

    for chr_templ_id, num_to_inst in free_chronicle_template_ids_with_num_to_instantiate.items():
        chr_templ = chronicle_templates[chr_templ_id]

        if chr_templ.task is not None:
            raise ValueError("Chronicle is supposed to be free (i.e. not task-dependent) but its \"task\" attribute is not None.")

        for _ in range(num_to_inst):
            chr_inst = instantiate_chronicle_template(chronicle_templates[chr_templ_id],
                                                      TRUE_LIT,
                                                      {}, 
                                                      solver)
            chr_inst_id_counter += 1
            instances_problem.chronicle_instances[chr_inst_id_counter] = chr_inst
            instances_problem.chronicle_instances_origin_template[chr_inst_id_counter] = chr_templ_id

    # Populate the problem with task-dependent chronicles instances.
    #
    # Such a chronicle instance is recorded with a reference to the subtask
    # it could refine (in the (owner chronicle, subtask index) format).
    # This way we can prevent instantiating the same chronicle template
    # as a refinement candidate of the same subtask more than once.

    stack: List[Tuple[ChronicleId, int]] = [(chr_inst_id, 0) for chr_inst_id in instances_problem.chronicle_instances]

    while stack:
        (chr_inst_id, d) = stack.pop()
        chr_inst = instances_problem.chronicle_instances[chr_inst_id]

        if d >= max_depth:
            continue

        for idx, subtask in enumerate(chr_inst.subtasks):
            potential_refinement_chronicle_instances_ids: List[ChronicleId] = []

            for chr_templ_id in task_dependent_chronicle_template_ids:
                chr_templ = chronicle_templates[chr_templ_id]
                
                if chr_templ.task is None:
                    raise ValueError("Chronicle is supposed to be task-dependent but its \"task\" attribute is None.")

                if ((chr_inst_id, idx) in instances_problem.chronicle_instances_subtasks_possible_refinements
                    and chr_templ_id in instances_problem.chronicle_instances_subtasks_possible_refinements[(chr_inst_id, idx)]
                ):
                    continue

                # NOTE: If the parameters of the subtask aren't unifiable with the parameters
                # of any of the considered refinement chronicles, we end up with a subtask for
                # which we don't have any refinement chronicle. As such, the solution to the
                # planning problem encoded as a CSP cannot contain the chronicle containing the
                # subtask, as it would be required to refine it to be a correct solution.
                # However, there could also be solutions without the chronicle containing the subtask,

                if atom_sequences_unifiable(subtask.task, chr_templ.task, solver):

                    new_chr_inst = instantiate_chronicle_template(chronicle_templates[chr_templ_id],
                                                                  chr_inst.presence_literal,
                                                                  { atom:subtask.task[i] for i, atom in enumerate(chr_templ.task) },
                                                                  solver)
                    chr_inst_id_counter += 1
                    instances_problem.chronicle_instances[chr_inst_id_counter] = new_chr_inst
                    instances_problem.chronicle_instances_origin_template[chr_inst_id_counter] = chr_templ_id
                    instances_problem.chronicle_instances_presence_assumptions[chr_inst_id] = None
                    instances_problem.chronicle_instances_subtasks_possible_refinements.setdefault((chr_inst_id, idx), []).append(chr_inst_id_counter)
                    instances_problem.chronicle_instances_subtasks_possible_refinements_reverse[chr_inst_id_counter] = (chr_inst_id, idx)

                    potential_refinement_chronicle_instances_ids.append(chr_inst_id_counter)

                    stack.append((chr_inst_id_counter, d+1))

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def instantiate_chronicle_template(
    chronicle_template: Chronicle,
    scope_representative_literal: Lit,
    substitution: Dict[Atom, Atom],
    solver: Solver,
) -> Chronicle:
    """
    Returns:
        A chronicle instance instantiated from `chronicle_template`, substituting \
            its atoms with new ones or those indicated in `substitution`, if any.
    
    TODO
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def new_bool_atom_from(
        bool_atom: BoolAtom,
        presence_literal: Lit, 
    ) -> BoolAtom:
        if bool_atom.var == ZERO_VAR:
            var = ZERO_VAR
        else:
            var = solver.add_new_optional_variable((-solver.state.bound_of(SignedVar.minus(bool_atom.var)),
                                                    solver.state.bound_of(SignedVar.plus(bool_atom.var))),
                                                   True,
                                                   presence_literal)
        return BoolAtom(var)
        
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def new_int_atom_from(
        int_atom: IntAtom,
        presence_literal: Lit, 
    ) -> IntAtom:
        if int_atom.var == ZERO_VAR:
            var = ZERO_VAR
        else:
            var = solver.add_new_optional_variable((-solver.state.bound_of(SignedVar.minus(int_atom.var)),
                                                    solver.state.bound_of(SignedVar.plus(int_atom.var))),
                                                   True,
                                                   presence_literal)
        return IntAtom(var, int_atom.offset_cst)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def new_frac_atom_from(
        frac_atom: FracAtom,
        presence_literal: Lit, 
    ) -> FracAtom:
        return FracAtom(new_int_atom_from(frac_atom.numer_int_atom, presence_literal), frac_atom.denom)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def new_symb_atom_from(
        symb_atom: SymbAtom,
        presence_literal: Lit, 
    ) -> SymbAtom:
        return SymbAtom(new_int_atom_from(symb_atom.int_view_atom, presence_literal), symb_atom.symb_type)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def new_atom_from(
        atom: Atom,
        presence_literal: Lit, 
    ) -> Atom:
        match atom:
            case BoolAtom():
                return new_bool_atom_from(atom, presence_literal)
            case IntAtom():
                return new_int_atom_from(atom, presence_literal)
            case FracAtom():
                return new_frac_atom_from(atom, presence_literal)
            case SymbAtom():
                return new_symb_atom_from(atom, presence_literal)
            case _:
                assert False

    # !!WARNING!!: The "copy" variables initial domain will be the current domain of the "original" variables
    # !!WARNING!!: Need to think about whether this is problematic or if it's actually supposed to be that way
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    sub = substitution.copy()

    if chronicle_template.presence not in substitution:
        sub[chronicle_template.presence] = BoolAtom(solver.add_new_presence_variable(scope_representative_literal))

    presence_atom = sub[chronicle_template.presence]
    assert isinstance(presence_atom, BoolAtom)
    presence_literal = Lit.geq(presence_atom.var, 1)

    if chronicle_template.start not in sub:
        sub[chronicle_template.start] = new_frac_atom_from(chronicle_template.start, presence_literal)

    if chronicle_template.end not in sub:
        sub[chronicle_template.end] = new_frac_atom_from(chronicle_template.end, presence_literal)

    if chronicle_template.task is not None:
        for p in chronicle_template.task[1:]:
            if p not in sub:
                sub[p] = new_atom_from(p, presence_literal)

    for cstr in chronicle_template.constraints:
        for term in cstr.terms:
            if term not in sub:
                sub[term] = new_atom_from(term, presence_literal)

    for cond in chronicle_template.conditions:
        if cond.start not in sub:
            sub[cond.start] = new_frac_atom_from(cond.start, presence_literal)
        if cond.end not in sub:
            sub[cond.end] = new_frac_atom_from(cond.end, presence_literal)
        for p in cond.state_var[1:]:
            if p not in sub:
                sub[p] = new_atom_from(p, presence_literal)
        if cond.value not in sub:
            sub[cond.value] = new_atom_from(cond.value, presence_literal)

    for eff in chronicle_template.effects:
        if eff.transition_start not in sub:
            sub[eff.transition_start] = new_frac_atom_from(eff.transition_start, presence_literal)
        if eff.persistence_start not in sub:
            sub[eff.persistence_start] = new_frac_atom_from(eff.persistence_start, presence_literal)
        for t in eff.min_persistence_end:
            if t not in sub:
                sub[t] = new_frac_atom_from(t, presence_literal)
        for p in eff.state_var[1:]:
            if p not in sub:
                sub[p] = new_atom_from(p, presence_literal)
        if eff.value not in sub:
            sub[eff.value] = new_atom_from(eff.value, presence_literal)

    for st in chronicle_template.subtasks:
        if st.start not in sub:
            sub[st.start] = new_frac_atom_from(st.start, presence_literal)
        if st.end not in sub:
            sub[st.end] = new_frac_atom_from(st.end, presence_literal)
        for p in st.task[1:]:
            if p not in sub:
                sub[p] = new_atom_from(p, presence_literal)

    return Chronicle(presence_atom,
                     sub[chronicle_template.start],
                     sub[chronicle_template.end],
                     (chronicle_template.task[0],)+tuple(sub[p] for p in chronicle_template.task[1:]) \
                        if chronicle_template.task is not None else None,
                     [Constraint(cstr.kind,
                                 tuple(sub[term] for term in cstr.terms))
                        for cstr in chronicle_template.constraints],
                     [Condition(sub[cond.start],                                # type: ignore
                                sub[cond.end],                                  # type: ignore
                                (cond.state_var[0],)+tuple(sub[p] for p in cond.state_var[1:]),
                                sub[cond.value])
                        for cond in chronicle_template.conditions],
                     [Effect(sub[eff.transition_start],                         # type: ignore
                             sub[eff.persistence_start],                        # type: ignore
                             tuple(sub[p] for p in eff.min_persistence_end),    # type: ignore
                             (eff.state_var[0],)+tuple(sub[p] for p in eff.state_var[1:]),
                             sub[eff.value])
                        for eff in chronicle_template.effects],
                     [SubTask(sub[st.start],                                    # type: ignore
                              sub[st.end],                                      # type: ignore                
                              (st.task[0],)+tuple(sub[p] for p in st.task[1:]))
                        for st in chronicle_template.subtasks])

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# TODO: For now, we simply reencode the problem from scratch into the the solver every time.
# However, in the future, we should take advantadge of the fact that many problems that we
# may solve are probably going to be similar. Indeed, when we integrate an observation,
# or slightly change / integrate an update to (the internals of) an (existing) chronicle,
# or assume / mark an (existing) chronicle to be present or absent in the solution, or
# populate the problem with a new chronicle, we may only have to change a rather small part
# of the encoding. As such, it may be interesting to include some kind of caching mechanism
# to avoid re-encoding the same things too often.

# def encode_instances_problem_into_csp(
#     instances_problem: InstancesProblem,
#     solver_with_previous_partial_encoding: Optional[Solver],
# ) -> Tuple[Solver, Solver]:
#     """
#     """
# 
#     if solver_with_previous_partial_encoding is not None:
#         solver_with_new_partial_encoding: Solver = deepcopy(solver_with_previous_partial_encoding)
#     else:
#         solver_with_new_partial_encoding: Solver = Solver(True, True)
# 
#     _encode_conditions_end_after_start(compiled_problem, solver_with_new_partial_encoding)
#     _encode_internal_chronicle_consistency(compiled_problem, solver_with_new_partial_encoding)
# 
#     solver_with_new_full_encoding: Solver = deepcopy(solver_with_new_partial_encoding)
# 
#     _encode_refinement_and_motivation(compiled_problem, solver_with_new_full_encoding)
#     effects_persistence_ends = _encode_effects_end_after_start(compiled_problem, solver_with_new_full_encoding)
#     _encode_coherence(compiled_problem, effects_persistence_ends, solver_with_new_full_encoding)
#     _encode_support(compiled_problem, effects_persistence_ends, solver_with_new_full_encoding)
#     _encode_mutex(compiled_problem, solver_with_new_full_encoding)
#     _encode_resources(compiled_problem, solver_with_new_full_encoding)
# 
#     return solver_with_new_partial_encoding, solver_with_new_full_encoding

def encode_instances_problem(
    instances_problem: InstancesProblem,
    solver: Solver,
) -> None:
    
    # WARNING: If in the future we want to incorporate a caching mechanism
    # for problem encoding, we'll have to deal with effect_persistence_ends 
    # as well, because the addition or removal of an effect from a chronicle
    # will change the indices of the effects in the effects list. As such,
    # effects_persistence_ends will become wrong / need to be updated (because
    # effects won't be correctly identified by their index in the list). 
    effects_persistence_ends: Dict[Tuple[ChronicleId, int], FracAtom] = {}

    for chr_id, chr_ in instances_problem.chronicle_instances.items():
        for i, eff in enumerate(chr_.effects):

            effects_persistence_ends[(chr_id, i)] = FracAtom(IntAtom(solver.add_new_optional_variable((0, MAX_INT),
                                                                                                      True, # TODO
                                                                                                      chr_.presence_literal),
                                                                     0),
                                                             eff.transition_start.denom)

    _encode_conditions_end_after_start(instances_problem, solver)
    _encode_effects_end_after_start(instances_problem, effects_persistence_ends, solver)
    _encode_internal_chronicle_consistency(instances_problem, solver)
    _encode_refinement_and_motivation(instances_problem, solver)
    _encode_coherence(instances_problem, effects_persistence_ends, solver)
    _encode_support(instances_problem, effects_persistence_ends, solver)
    _encode_mutex(instances_problem, solver)
    _encode_resources(instances_problem, solver)
    # solver.add_optimization_objective("function to optimize computing a metric / cost")

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _encode_conditions_end_after_start(
    instances_problem: InstancesProblem,
    solver: Solver,
) -> None:

    for _, chr_ in instances_problem.chronicle_instances.items():
        for cond in chr_.conditions:
            solver.add_scoped_constraint(ConstrExpr.leq((cond.start, cond.end)),
                                         (chr_.presence_literal,))

    solver.propagate()

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _encode_internal_chronicle_consistency(
    instances_problem: InstancesProblem,
    solver: Solver,
) -> None:
    ...

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _encode_effects_end_after_start(
    instances_problem: InstancesProblem,
    effects_persistence_ends: Dict[Tuple[ChronicleId, int], FracAtom],
    solver: Solver,
) -> Dict[Tuple[ChronicleId, int], FracAtom]:

    for chr_id, chr_ in instances_problem.chronicle_instances.items():
        for i, eff in enumerate(chr_.effects):

            persistence_end = effects_persistence_ends[(chr_id, i)]

            solver.add_scoped_constraint(ConstrExpr.leq((eff.transition_start, eff.persistence_start)),
                                         (chr_.presence_literal, ))
            solver.add_scoped_constraint(ConstrExpr.leq((eff.persistence_start, persistence_end)),
                                         (chr_.presence_literal, ))
            for min_pers_end in eff.min_persistence_end:
                solver.add_scoped_constraint(ConstrExpr.leq((min_pers_end, persistence_end)),
                                             (chr_.presence_literal, ))

    solver.propagate()

    return effects_persistence_ends

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _encode_refinement_and_motivation(
    instances_problem: InstancesProblem,
    solver: Solver,
) -> None:
    ...

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _encode_coherence(
    instances_problem: InstancesProblem,
    effects_persistence_ends: Dict[Tuple[ChronicleId, int], FracAtom],
    solver: Solver,
) -> None:
    ...

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _encode_support(
    instances_problem: InstancesProblem,
    effects_persistence_ends: Dict[Tuple[ChronicleId, int], FracAtom],
    solver: Solver,
) -> None:
    ...

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _encode_mutex(
    instances_problem: InstancesProblem,
    solver: Solver,
) -> None:
    ...

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def _encode_resources(
    instances_problem: InstancesProblem,
    solver: Solver,
) -> None:
    ...

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
