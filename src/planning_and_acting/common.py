"""
"""

from __future__ import annotations

#################################################################################

from dataclasses import dataclass, field
from typing import Callable, Dict, FrozenSet, List, NamedTuple, Optional, Set, Tuple, Union
from enum import Enum, auto

from src.fundamentals import Var, Lit, IntAtom, BoolAtom, FracAtom, SymbAtom, Atom

#################################################################################
#
#################################################################################

Value_WIP = int

Table_WIP = List[Tuple[Var, List[Value_WIP]]]

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
 
StateVar = Tuple[Atom, ...]

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

Task = Tuple[Atom, ...]

class Constraint(NamedTuple):

    class Kind(Enum):
        TABLE = auto()
        LEQ = auto()
        LT = auto()
        EQ = auto()
        NEQ = auto()
    #    LINSUM = auto()
        OR = auto()
        AND = auto()
        DUR_REQ = auto()
        DUR_CTG = auto()

    kind: Constraint.Kind
    terms: Tuple[Atom, ...]
    # value: Optional[Lit]  # Comment from Aries: If set, this constraint should be reified so that it is always equal to value.
    # TODO: like for FracAtom, make it so incorrent number of terms raises an error on instantiation

class Condition(NamedTuple):
    start: FracAtom
    end: FracAtom
    state_var: StateVar
    value: Atom

class Effect(NamedTuple):
    transition_start: FracAtom
    persistence_start: FracAtom
    min_persistence_end: Tuple[FracAtom,...]
    state_var: StateVar
    value: Atom

class SubTask(NamedTuple):
    start: FracAtom
    end: FracAtom
    task: Task

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

ChronicleId = int

@dataclass
class Chronicle():
    presence: BoolAtom   # previously: Lit
    start: FracAtom
    end: FracAtom
    task: Optional[Task]
    constraints: List[Constraint]
    conditions: List[Condition]
    effects: List[Effect]
    subtasks: List[SubTask]
    # cost: Optional[LinrAtom]   # TODO TODO TODO !

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
# ActingModelId = int
# 
# class ActingModel(NamedTuple):
# #    id_: ActingModelId
#     chronicle_id: ChronicleId               # a (partially) lifted chronicle - not everything is necessarily grounded -> can be a template or an instance
#     instantiation: Dict[Var, Value_WIP]      # instantiation is on non-contingent (controllable) variables. a priori not on temporal ones / timepoints either. Includes arbitraries and acquires !
#     subtasks_possible_acting_models: List[List[ActingModelId]]  # outer list indices: subtasks indices. inner list indices: possible refining acting models
# #    parent_acting_model: Optional[ActingModelId]  # None for the root
# 
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
# # The tree of acting models / acting tree actually **as a whole** defines a possible instantiation !
# 
# ActingContextId = int
# 
# class ActingContext(NamedTuple):
# 
#     acting_models_collection: Dict[ActingModelId, ActingModel]
#     chronicles_collection: Dict[ChronicleId, Chronicle]
# 
#     chronicle_acting_model_mapping: Dict[ChronicleId, List[ActingModelId]]
#     acting_model_status: Dict[ActingModelId, int]
# 
#     possible_instantiations: Table_WIP
# #    choices_trace: List[Tuple[ActingModelId, TemporalNetwork]]
#     choices_trace: List[ActingModelId]
#     # The temporal network is built by walking through the acting models tree
#     # and taking the union of the "local" PSTNs defined by each method.
#     # This results in some sort of pTPN / cc-pCCTPU, i.e. a PSTN with "choices" / "branches".
#     # A "normal" PSTN remains when we only keep 1 refinement per subtask.
#     # Maybe there is only need to explicitly represent this "normal" PSTN,
#     # when all refinement choices have been made ?
#     
#     root_acting_model_id: ActingModelId # set of different possible roots ?
#                                         # if only one root, should be the first element of choices_trace ?
# 
#     execution_algorithm: object
# 
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
# #class ActingManager():
# #    
# #    acting_context_collection: Dict[ActingContextId, ActingContext]
# #    
# #    acting_contexts_adjacency: Dict[ActingContextId, Set[ActingContextId]]
# #
# #    # template_transition_generation_functions: Set[TransitionGenerationFunction]
# #    transition_generation_funcs: Set[TransitionGenerationFunction]
# #    transition_activation_condition_funcs: Dict[Tuple[ActingContextId, ActingContextId],
# #                                                    TransitionActivationConditionFunction]
# #
# #    current_acting_context_id: ActingContextId
# #    current_acting_context_cache: ActingContext
# #
# #    def merge_observations(self,
# #        acting_context_id: ActingContextId,
# #    )

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# TransitionActivationConditionFunction = Callable[[ActingContext], bool]
# 
# TransitionGenerationFunction = Callable[[ActingContext], List[Tuple[TransitionActivationConditionFunction,
#                                                                     ActingContext]]]

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
