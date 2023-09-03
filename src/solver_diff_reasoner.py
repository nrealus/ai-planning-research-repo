from __future__ import annotations

#################################################################################

import typing
from typing import Callable, Dict, Iterable, List, NamedTuple, Optional, Set, Tuple, Union
from dataclasses import dataclass, field
from abc import ABC

import heapq

from fundamentals import (
    Var, SignedVar, BoundVal, Lit, TRUE_LIT
)

from solver import SolverCauses, SolverConflictInfo, SolverReasoner, Solver

#################################################################################
#################################################################################
#                                   CONTENTS:
# - DIFFERENCE LOGIC REASONER
#################################################################################
#################################################################################

class DiffReasoner(SolverReasoner):
    """
    """

    #############################################################################
    # CONSTRAINT / PROPAGATOR GROUP (& ITS ID), ENABLER, CONSTRAINTS DATABASE
    #############################################################################

    @dataclass
    class PropagatorGroup():
        """
        Represents a group of (elementary) propagators, that only differ by their
        enabling conditions (i.e. `potential_enablers`).
        
        A (elementary) propagator represents the fact that an update on its
        `source` bound should be reflected on its `target` bound when some
        conditions (the enabling conditions) hold.
        
        FIXME: As such, by abuse of language/notation, a propagator can be seen as
        an encoding for a (directed) edge of an STN / difference constraint between two variables.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        source: SignedVar
        """
        Source signed variable of the propagator.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        target: SignedVar
        """
        Target signed variable of the propagator.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        weight: BoundVal
        """
        Weight of the propagator.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        enabler: Optional[DiffReasoner.Enabler] #FIXME rename to current_enabler ?
        """
        The enabler of the propagators of the group.

        It is non-None when the group / its propagators are active (i.e. participate in propagation).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        potential_enablers: List[DiffReasoner.Enabler]
        """
        A set of potential enablers for (all) the propagators of the group.

        The group / all the propagators it represents become enabled once
        one of these enablers' active and valid literals become True.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class PropagatorGroupId(NamedTuple):
        id: int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Enabler(NamedTuple):
        """
        Represents the conditions for a propagator to be enabled, which is for
        literals `active` and `valid` to both be true.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        active: Lit
        """
        When this literal is present (i.e. its variable is present), then it is
        true iff the propagators (enabled by this enabler) are active.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        valid: Lit
        """
        This literal is true iff the propagators (enabled by this enabler) are
        within its validity scope (i.e. when it is known to be sound to propagate
        a change from the propagator's source to the propagator's target)

        In the simplest cast, `valid = presence(active)` (since by construction `presence(active)`
        is true iff both the source and the target of the propagator are present).

        `valid` may be a more specific literal, but it always satisfy that `presence(active) => valid`.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @dataclass
#    class ConstraintsDatabase():
    class PropagatorsDatabase():
        """
        Holds all active and inactive difference constraints / edges.

        This includes propagators corresponding to the negation of inserted difference constraints / edges
        """

        _propagator_group_id_counter: int = 0
        #########################################################################
        propagators: Dict[DiffReasoner.PropagatorGroupId, DiffReasoner.PropagatorGroup] = {}
        """
        Stores all propagators (both active and inactive) as groups or "bundles" of
        propagators sharing their source, target, and weight.

        Each difference constraint / edge (i.e. v2-v1 <= d, i.e. v1 --d-> v2)
        in the STN) added is converted into 4 propagators, which correspond to:
        - the forward (source -> target) view of the "canonical" (i.e. "normal") edge
        - the backward (target -> source) view of the "canonical" (i.e. "normal") edge
        - the forward (source -> target) view of the "negated" (i.e. negation of canonical) edge
        - the backward (target -> source) view of the "negated" (i.e. negation of canonical) edge

        Make no mistake, at no point will those 4 propagators be part of the same group !
        None of them have the same source, target, and weight !
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        propagators_list: List[DiffReasoner.PropagatorGroupId] = []
        """
        Ordered view of `propagators` (their IDs).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        propagators_source_and_target: Dict[Tuple[SignedVar, SignedVar], List[DiffReasoner.PropagatorGroupId]] = {}
        """
        Associates (source, target) signed variable pairs to (IDs of) propagators defined between them.
        """
        #########################################################################
        intermittent_propagators: Dict[SignedVar, List[Tuple[SignedVar, BoundVal, Lit]]] = {}
        """
        Stores propagators whose activity depends on the current state
        (i.e. which may or may not be active, depending on the current state).
        
        Encoding as a dictionary:
        - The key corresponds to the source of a propagator
        - The value for that key / propagator source is a list of (target, weight, presence), for each encoded propagator.

        Here, "presence" corresponds to a literal that is true iff the edge / propagator must be present.
        CHECKME: same thing as "valid" or not ?
        Note that handling of optional variables might allow an edge to propagate even if it is not known to be present yet.
        """
        #########################################################################
        watches: Dict[SignedVar, Dict[BoundVal, List[Tuple[DiffReasoner.PropagatorGroupId, DiffReasoner.Enabler]]]] = {}
        """
        Associates literals to propagators (with an enabler) that should be activated when they become true.
        """
        #########################################################################
        # propagator_groups_events_trail: List[List[DiffReasoner.ConstraintsDatabase.PropagatorGroupEvents.AnyEvent]] = [[]]
        propagator_groups_events_trail: List[List[Optional[Tuple[DiffReasoner.PropagatorGroupId, DiffReasoner.Enabler]]]] = [[]]
        """
        Holds the trail of "propagator groups events", i.e. updates on propagator groups:
        - A None element designates the addition of a new propagator group.
        - A (PropagatorGroupId, Enabler) tuple designates the addition of the specified
        enabler to the set of potential enablers of the propagator group with the specified id.
        """
        #########################################################################
        next_new_constraint_index: int = 0

    #############################################################################
    #  THEORY PROPAGATION CAUSES, INFERENCE CAUSES
    #############################################################################

    class TheoryPropagationCauses(ABC):
        """
        A container / "namespace" for structures describing the kinds of causes
        for an active shortest path to trigger theory propagation.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        class Path(NamedTuple):
            """
            Represents a theory propagation cause corresponding to the activation
            of the propagators represented by `triggering_propagator_group_id`.
            
            (In other words, the activation/"appearance" of a new shortest path between
            `source` and `target`, going through the edge represented by the
            propagators corresponding to `triggering_propagator_group_id`)
            """
            source: SignedVar
            target: SignedVar
            triggering_propagator_group_id: DiffReasoner.PropagatorGroupId
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        class Bounds(NamedTuple):
            """
            Represents a theory propagation cause corresponding to the incompability
            of the `source_lit` and `target_lit` literals with an "edge" (propagator group).
            """
            source_lit: Lit
            target_lit: Lit

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        AnyCause = Union[Path, Bounds]
        """
        Any theory propagation cause.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class InferenceCauses(ABC):
        """
        A container / "namespace" for structures describing the causes that can
        trigger an inference (i.e. bound value update, calling `set_bound_value`
        in the main solver) made during propagation in this reasoner.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        class EdgePropagation(NamedTuple):
            """
            Represents a inference cause corresponding to an edge propagation
            (of the given edge / propagator group)
            """
            propagator_group_id: DiffReasoner.PropagatorGroupId
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        class TheoryPropagation(NamedTuple):
            """
            Represents a inference cause corresponding to a theory propagation.
            That theory propagation's own cause was registered at the
            given index in `theory_propagation_causes`.
            """
            theory_propagation_cause_index: int

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        AnyCause = Union[EdgePropagation, TheoryPropagation]
        """
        Any cause for an inference (made by this reasoner).
        """

    #############################################################################
    #  DIJKSTRA STATE
    #############################################################################

    @dataclass
    class DijkstraState:
        """
        A data structure that contains the mutable data that is updated during a Dijkstra algorithm.
        It is intended to be reusable across multiple runs.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        latest: BoundVal = BoundVal(0)
        """
        The latest distance that was extract from the queue. As a property of the Dijkstra algorithm,
        if a distance in the `distances` table is less than or equal to this value, then it will not
        change for the rest of the process.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        distances: Dict[SignedVar, Tuple[BoundVal, Optional[DiffReasoner.PropagatorGroupId]]] = {}
        """
        Associates each vertex to its distance. If the node is not an origin, it also indicates
        the latest edge on the shortest path to this node.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        queue: List[Tuple[BoundVal, SignedVar]] = []
        """
        Elements of the queue that have not been extracted yet.
        Note that a single node might appear several times in the queue,
        in which case only the one with the smallest distance is relevant.

        Represented with Python's heapq, which is a min-heap.

        The SignedVar corresponds to a node and the BoundVal corresponds
        to the reduced distance from the origin to this node. 
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def clear(self) -> None:
            self.latest = BoundVal(0)
            self.distances.clear()
            self.queue.clear()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def enqueue(self,
            node: SignedVar,
            dist: BoundVal,
            incoming_edge: Optional[DiffReasoner.PropagatorGroupId],
        ) -> None:
            """
            Add a node to the queue, indicating the distance from the origin and
            the latest edge on the path from the origin to this node.
            """
            prev = self.distances.get(node, None)
            if prev is None:
                previous_dist = 2**64  # FIXME: should be max int
            else:
                previous_dist = prev[0]

            if dist < previous_dist:
                self.distances[node] = (dist, incoming_edge)
                heapq.heappush(self.queue, (dist, node))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def dequeue(self) -> Optional[Tuple[BoundVal, SignedVar]]:
            """
            Remove the next element in the queue.
            Nodes are removed by increasing distance to the origin.
            Each node can only be extracted once.
            """
            if len(self.queue) == 0:
                return None

            (dist, node) = heapq.heappop(self.queue)
            
            assert self.latest <= dist
            assert self.distances[node][0] <= dist

            self.latest = dist

            if self.distances[node][0] == dist:
                # Node with the best distance from origin
                return (dist, node)
            else:
                # A node with a better distance was previousl extracted,
                # ignore this one as it cannot contribute to a shortest path
                return None
            
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def distance(self,
            node: SignedVar,
        ) -> Optional[BoundVal]:
            """
            Returns the distance from the origin to this node,
            or None if the node was not reached by Dijkstra's algorithm
            """
            if node not in self.distances:
                return None
            else:
                return self.distances[node][0]

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def reached_nodes_iterator(self) -> Iterable[Tuple[BoundVal, SignedVar]]:
            """
            Returns an iterator over all nodes (and their distances from the origin) that were reached by the algorithm.
            """
            return tuple((d,n) for (n,(d,_)) in self.distances.items())

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def predecessor(self,
            node: SignedVar,
        ) -> Optional[DiffReasoner.PropagatorGroupId]:
            """
            Returns the predecessor edge from the origin to this node or None if it is an origin.

            Will raise an error if the ndoe has no associated distance (i.e. was not reached by the algorithm)
            """
            return self.distances[node][1]

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def is_final(self,
            node: SignedVar,
        ) -> bool:
            """
            Returns true if the node has a distance that is guaranteed not to change in subsequent iterations.
            """
            if node not in self.distances:
                return False
            return self.distances[node][0] <= self.latest

    #############################################################################
 
    def __init__(self):

        #########################################################################
        self.propagators_database: DiffReasoner.PropagatorsDatabase = DiffReasoner.PropagatorsDatabase()
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.propagators_active: Dict[SignedVar, List[Tuple[SignedVar, BoundVal, DiffReasoner.PropagatorGroupId]]] = {}
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.propagators_pending_for_activation: List[Tuple[DiffReasoner.PropagatorGroupId, DiffReasoner.Enabler]] = []
        #########################################################################
        self.pending_bounds_to_update: Set[SignedVar] = set()
        #########################################################################
        self.propagation_metadata_trail: List[List[Optional[DiffReasoner.PropagatorGroupId]]] = [[]]
        """
        Trail of propagation events metadata. Outer list index: decision level.
        Inner list content corresponds to either:
            - Activation of a propagator group (DiffReasoner.PropagatorGroupId - ID of that propagator group).
            - Triggering of theory propagation and registration of its cause (None).
              The corresponding TheoryPropagationCauses.AnyCause is appended to a list (`theory_propagation_causes`).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.theory_propagation_causes: List[DiffReasoner.TheoryPropagationCauses.AnyCause] = []
        """
        List / history of theory propagation causes. A theory propagation cause is added to this list
        when a None object is added to the trail of propagation events metadata (`propagation_metadata_trail`).
        """
        #########################################################################
        self.next_unprocessed_solver_event_index: int = 0
        #########################################################################
        self.internal_propagate_queue: List[SignedVar] = []
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        self.internal_dijkstra_states: Tuple[DiffReasoner.DijkstraState, DiffReasoner.DijkstraState] = (DiffReasoner.DijkstraState(), DiffReasoner.DijkstraState())

    #############################################################################
    #  ADD REIFIED CONSTRAINT
    #############################################################################

    # def add_reified_stn_edge(self,
    def add_reified_difference_constraint(self,
        reification_literal: Lit,
        source: Var,
        target: Var,
        weight: BoundVal,
        solver: Solver,
    ) -> None:
        """
        Adds a new difference constraint (`target - source <= weight`), i.e. STN
        edge (source --weight--> target), which was already reified into `reification_literal`.

        This is done by following these steps:

        1. Decompose the difference constraint into 4 propagators, which will be
        "active" iff `reification_literal` is true, and "valid" iff the variable
        of their target signed variable is present. (see `Enabler`).

        And then for each of these 4 propagators:

        2. Integrate the new propagator to the propagator database (recall that 
        a propagator group "bundles" propagators which only differ by enabling conditions)).
        For each new propagator, this is done by either:

            - Merging / adding the new propagator into an existing group of propagators,
            by adding its enabler to their `potential_enablers`.
            
            - Tightening an already active existing group of propagators (superseded by the new propagator),
            by setting their weight to the new propagator's weight.
            
            - Ignoring the new propagator, if it is redundant with an existing one (i.e. if
            its weight is weaker than an existing propagator's with the same enabling conditions).
            
            - Creating a new propagator group with the new propagator's enabler,
            if there are no existing propagators with the same source and target.

        NOTE that merging, tightening, or ignoring is only done when the solver is at the top decision level.
        Beyond the top decision level, we always choose to create a new propagator group, because it
        would be too complicated to undo/backtrack the reorganization of a propagator group.

        3. Postprocess the integration of the new propagator. The two possibilities are the following:
            
            - Either set the propagators of the group to which the new propagator was staged
            as pending for propagation, if the enabling conditions of the new propagator
            are satisfied (`active` and `valid` literals of its enabler are true).
            
            - Or set watch on the enabling conditions of the new propagator (the `active`
            and `valid` literals of its enabler), if they arent' known to be true yet, so
            that we're notified when one of them becomes true. (When both of them will be true,
            the propagator group will be staged as pending for propagation).
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def integrate_propagator_to_database(
            src: SignedVar,
            tgt: SignedVar,
            wgt: BoundVal, 
            eblr: DiffReasoner.Enabler,
        ) -> Tuple[DiffReasoner.PropagatorGroupId, str]:
            """
            Integrates a new propagator (defined by the arguments) to the propagator database.
            See step 2 (function documentation).
            """
 
            # Only optimize organisation of propagator groups at the top decision level,
            # because if done at a decision level beyond, it would to complex to undo/backtrack
            # the changes made to the groups.
            if solver.dec_level == 0:
                
                self.propagators_database.propagators_source_and_target.setdefault((src, tgt), [])

                # Search for a propagator group compatible with this propagator (same source and target)
                for existing_group_id in self.propagators_database.propagators_source_and_target[(src, tgt)]:
                    existing_group = self.propagators_database.propagators[existing_group_id]

                    if not (existing_group.source == src and existing_group.target == tgt):
                        continue

                    # If there is a compatible propagator group:
                    
                    # If the group has the same weight as the propagator, either merge the
                    # propagator into the group by adding its enabler to it, if it isn't redundant,
                    # or ignore it and do nothing if it is.
                    if existing_group.weight == wgt:
                        
                        if not eblr in existing_group.potential_enablers:
                            existing_group.potential_enablers.append(eblr)
                            return (existing_group_id, "merging")
                        else:
                            return (existing_group_id, "ignoring")


                    # If the propagator's weight is strictly stronger than that of the group and they have the
                    # same one enabler, then just tighten the group by changing its weight to that of the propagator.
                    elif wgt.is_stronger_than(BoundVal(existing_group.weight-1)):

                        if not (len(existing_group.potential_enablers) == 1 and existing_group.potential_enablers[0] == eblr):
                            continue

                        if src in self.propagators_database.intermittent_propagators:
                            # note that since we consider the case where there's only one potential enabler,
                            # there can only be 1 intermittent propagator.
                            for i in range(len(self.propagators_database.intermittent_propagators[src])):
                                if self.propagators_database.intermittent_propagators[src][i] == (tgt, existing_group.weight, eblr.active):
                                    self.propagators_database.intermittent_propagators[src][i] = (tgt, wgt, eblr.active)
                                    break

                        existing_group.weight = wgt
                        return (existing_group_id, "tightening")

                    # If the propagator's weight is weaker than that of the group and they have the same one enabler,
                    # ignore the propagator and do nothing, because it is redundant.
                    elif existing_group.weight.is_stronger_than(BoundVal(wgt-1)):

                        if not (len(existing_group.potential_enablers) == 1 and existing_group.potential_enablers[0] == eblr):
                            continue
                        return (existing_group_id, "ignoring")

            # If the propagator couldn't be unified / integrated with an existing
            # propagator group, then just create a new propagator group for it.

            existing_group_id = DiffReasoner.PropagatorGroupId(self.propagators_database._propagator_group_id_counter)
            self.propagators_database._propagator_group_id_counter += 1

            self.propagators_database.propagators[existing_group_id] = DiffReasoner.PropagatorGroup(src, tgt, wgt, None, [eblr])
            self.propagators_database.propagators_list.append(existing_group_id)
            self.propagators_database.propagators_source_and_target.setdefault((src, tgt), []).append(existing_group_id)

            self.propagators_database.propagator_groups_events_trail[solver.dec_level].append(None)

            return (existing_group_id, "creating")
            
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def postprocess_propagator_integration_into_database(
            propagator_group_id: DiffReasoner.PropagatorGroupId,
            propagator_integrated_by: str,
            eblr: DiffReasoner.Enabler,
        ) -> None:
            """
            Postprocesses the integration to the propagators database of a new propagator.
            See step 3 (function documentation).
            """

            # NOTE: The case of propagator_integrated_by == "ignoring" is dealt in the main function.

            # If propagator was created into a new group or was merged into an existing one,
            # there are different possibilities, depending on whether it is currently enabled or not.
            # FIXME: Note that we should make sure that when backtracking beyond the current decision level, we should deactivate the edge
            if propagator_integrated_by == "creating" or propagator_integrated_by == "merging":

                # If the propagator can never be active/present, do nothing.
                edge_valid = solver.vars_presence_literals[eblr.active.signed_var.var]
                if solver.is_literal_entailed(eblr.active.negation()) or solver.is_literal_entailed(edge_valid.negation()):
                    return
                
                # If the propagator is always active in the current (and following) decision levels, enqueue it for activation.
                elif solver.is_literal_entailed(eblr.active) and solver.is_literal_entailed(eblr.valid):
                    self.propagators_pending_for_activation.insert(0, (propagator_group_id, eblr))
                
                # If the propagator isn't known to be active or inactive yet, 
                # record the fact that:
                # - If the enabling conditions hold (`enabler.valid` and `enabler.active` are true), then the propagator should be enabled
                # - If the propagator is inconsistent, then the `enabler.active` should be made false
                else:

                    if solver.dec_level > 0:
                        # FIXME: when backtracking, we should remove this edge (or at least ensure that it is definitely deactivated)
                        print("WARNING: adding a dynamically enabled edge beyond the root decision level is unsupported.")

                    # Set a watch on both `enabler.active` and `enabler.valid` literals
                    # (when one of them becomes true, we will still have to check that the other one becomes true as well)
                    self.propagators_database.watches.setdefault(
                        eblr.active.signed_var, {}).setdefault(
                            eblr.active.bound_value, []).append((propagator_group_id, eblr))
                    self.propagators_database.watches.setdefault(
                        eblr.valid.signed_var, {}).setdefault(
                            eblr.valid.bound_value, []).append((propagator_group_id, eblr))

                    self.propagators_database.intermittent_propagators.setdefault(
                        self.propagators_database.propagators[propagator_group_id].source, []).append((
                            self.propagators_database.propagators[propagator_group_id].target,
                            self.propagators_database.propagators[propagator_group_id].weight,
                            eblr.active))

                    self.propagators_database.propagator_groups_events_trail[solver.dec_level].append((propagator_group_id, eblr))

            # If an existing group was tightened (as a result of
            # a new propagator's integration into the database), then:
            # - If the group wasn't already active, we don't need to do anything.
            # - If the group was already active, we need to force its propagation
            #   (which we do by "pretending" it was previously inactive and then
            #   enqueuing it for activation)
            elif propagator_integrated_by == "tightening":

                if solver.is_literal_entailed(eblr.active) and solver.is_literal_entailed(eblr.valid):
                    self.propagators_database.propagators[propagator_group_id].enabler = None
                    self.propagators_pending_for_activation.insert(0, (propagator_group_id, eblr))
                else:
                    return

            else:
                assert False

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        # Step 1: (see function documentation)

        # The validity scope of the reification literal is known to be the
        # conjunctive scope of the source and target variables of the edge / constraint.
        # 
        # As such, the edge is valid / well-defined iff its reification literal is
        # present (iff the source and target variables of the edge are both present)
        edge_valid = solver.vars_presence_literals[reification_literal.signed_var.var]
        assert solver.is_implication_true(edge_valid, solver.vars_presence_literals[source])
        assert solver.is_implication_true(edge_valid, solver.vars_presence_literals[target])

        # The edge will be decomposed into 4 propagators:
        # 2 "canonical", and 2 "negated" (or "inverted": swapped source and target for them).
        # 
        # A "canonical" (source-to-target) propagator is valid when `presence(target) => edge_valid`.
        # This is because modifying the target's domain is only meaningful if the edge is present.
        # Analogously, a "negated" (target-to-source) propagator is valid when `presence(source) => edge_valid`.
        #
        # As such, we need to determine a literal that is true iff a "canonical" (source-to-target) propagator
        # is valid, as well as a literal that is true iff a "negated" (target-to-source) propagator is valid.

        # "Canonical" propagator case.
        if solver.is_implication_true(solver.vars_presence_literals[target], edge_valid):
            # If it is statically known that `presence(target) => edge_valid`, the propagator is always valid
            source_to_target_propagator_valid = TRUE_LIT
        else:
            # Given that `presence(source) & presence(target) <=> edge_valid`, we can infer that the propagator becomes valid
            # (i.e. `presence(target) => edge_valid` holds) when `presence(source)` becomes true
            source_to_target_propagator_valid = solver.vars_presence_literals[source]

        # "Negated" propagator case (analogous).
        if solver.is_implication_true(solver.vars_presence_literals[source], edge_valid):
            target_to_source_propagator_valid = TRUE_LIT
        else:
            target_to_source_propagator_valid = solver.vars_presence_literals[target]

        propagators = [

            # "canonical" (i.e. "normal") edge: active <=> source ---(weight)---> target
            (SignedVar(source, True),
            SignedVar(target, True),
            BoundVal(weight),
            DiffReasoner.Enabler(reification_literal, source_to_target_propagator_valid)),

            (SignedVar(target, False),
            SignedVar(source, False),
            BoundVal(weight),
            DiffReasoner.Enabler(reification_literal, target_to_source_propagator_valid)),

            # "negated" (i.e. "inverted") edge: !active <=> source <----(-weight-1)--- target
            (SignedVar(target, True),
            SignedVar(source, True),
            BoundVal(-weight-1),
            DiffReasoner.Enabler(reification_literal, target_to_source_propagator_valid)),

            (SignedVar(source, False),
            SignedVar(target, False),
            BoundVal(-weight-1),
            DiffReasoner.Enabler(reification_literal, source_to_target_propagator_valid)),

        ]

        for p in propagators:
            (group_id, integration_kind) = integrate_propagator_to_database(p[0], p[1], p[2], p[3])
            if integration_kind == "ignoring":
                self.propagators_database.propagators[group_id].enabler = None
                continue
            postprocess_propagator_integration_into_database(group_id, integration_kind, p[3])

    #############################################################################
    # MAIN SOLVER DECISION LEVEL INCREASE OR DECREASE CALLBACKS
    #############################################################################

    def on_solver_new_set_literal_decision(self,
        solver: Solver,
    ) -> None:

        self.next_unprocessed_solver_event_index = 0

        if len(self.propagation_metadata_trail) == solver.dec_level:
            self.propagation_metadata_trail.append([])

        if len(self.propagators_database.propagator_groups_events_trail) == solver.dec_level:
            self.propagators_database.propagator_groups_events_trail.append([])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_solver_backtrack_one_level(self,
        solver: Solver,
    ) -> None:

        self.propagators_pending_for_activation.clear()

        for ev in self.propagation_metadata_trail[solver.dec_level]:
            if ev is None:
                self.theory_propagation_causes.pop()
            else:
                propagator_group = self.propagators_database.propagators[ev]
                self.propagators_active[propagator_group.source].pop()
                propagator_group.enabler = None
        self.propagation_metadata_trail[solver.dec_level].clear()

        self.next_unprocessed_solver_event_index = len(solver.events_trail[solver.dec_level-1])

        for ev in self.propagators_database.propagator_groups_events_trail[solver.dec_level]:
            if ev is None:
                propagator_group_id = self.propagators_database.propagators_list.pop()
                propagator_group = self.propagators_database.propagators.pop(propagator_group_id)
                self.propagators_database.propagators_source_and_target.pop((propagator_group.source, propagator_group.target))
                # NOTE: no need to reset/update self.constraints_database.next_new_constraint_index !
            else:
                (propagator_group_id, enabler) = ev
                self.propagators_database.watches[enabler.active.signed_var][enabler.active.bound_value].remove((propagator_group_id, enabler))
                self.propagators_database.watches[enabler.active.signed_var][enabler.active.bound_value].remove((propagator_group_id, enabler))
                propagator_group = self.propagators_database.propagators[propagator_group_id]
                self.propagators_database.intermittent_propagators[propagator_group.source].pop()
        self.propagators_database.propagator_groups_events_trail[solver.dec_level].clear()

    #############################################################################
    #  PROPAGATION
    #############################################################################

    def propagate(self,
        solver: Solver,
    ) -> Optional[SolverConflictInfo.InvalidBoundUpdate | SolverConflictInfo.ReasonerExplanation]:
        """
        TODO
        """
        return self._propagate(solver, ("bounds",))
        # return self._propagate(solver, ("bounds", "edges"))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate(self,
        solver: Solver,
        theory_propagation_levels: Tuple[str, ...]=("bounds",),
    ) -> Optional[SolverConflictInfo.InvalidBoundUpdate | SolverConflictInfo.ReasonerExplanation]:
        """
        Propagates all edges / propagator groups that have been marked as active since the last propagation.

        (1) First, processes each newly added inactive(*) edge / propagator group once, to check if it
        can be added to the solver based on the literals of its extremities (i.e. minimal and maximal
        possible values for the edge). If not make its enablers false. This step is equivalent to "bound
        theory propagation", but needs to be done independenty because we do not have events for the initial
        domain bound values of variables.
            (*) A newly added edge / propagator group can be active (see `add_reified_difference_constraint`),
            in which case it is added to pending propagator activations.

        (2):
            (2.1) Then, propagate all literals changes.
            
            (2.2) And then process / loop through the edges / propagator groups pending for activation
            (including those that were enqueued at step 2.1). This is done by:
                
                - Checking if the edge / propagator group is a self loop:
                    - A positive self loop is ignored (move on to next edge / propagator)
                    - A negative self loop is a contradiction, for a which a ReasonerExplanation is returned (to build an explanation later)
                
                - If not a self-loop, mark the edge / propagator group as active and propagate it with
                the Cesta96 algorithm (which runs an incremental Bellman-Ford algorithm over active
                edges / propagator groups).
                The assumptions needed to do this (i.e. the edge / propagator group must be newly 
                inserted and the constraint network / STN must be consistent) are indeed satisfied.
        
        Finally, doing step (2.1) before (2.2) is necessary because cycle detection on the insertion of a new
        edge / propagator group requires a consistent constraint network (STN) and no interference of external bound updates.
        """

        # Step (1) (see function documentation).
        if "bounds" in theory_propagation_levels:

            while self.propagators_database.next_new_constraint_index < len(self.propagators_database.propagators_list):
                propagator_group = self.propagators_database.propagators[
                    self.propagators_database.propagators_list[self.propagators_database.next_new_constraint_index]]
                self.propagators_database.next_new_constraint_index += 1
                
                assert propagator_group.enabler is None # CHECKME
                if propagator_group.enabler is not None:
                    continue

                target_new_lb = BoundVal(solver.bound_values[propagator_group.source] + propagator_group.weight)
                target_current_ub = solver.bound_values[propagator_group.target.opposite_signed_var()]

                # If the lower bound implied by the propagator for the target is greater
                # than its current upper bound, then the edge is impossible / is a contradiction.
                # Add a theory propagation cause to allow explanation, and make all potential
                # enablers of the edge / propagator group false.
                if target_new_lb + target_current_ub < 0:

                    self.theory_propagation_causes.append(
                        DiffReasoner.TheoryPropagationCauses.Bounds(
                            Lit(propagator_group.source, solver.bound_values[propagator_group.source]), 
                            Lit(propagator_group.target.opposite_signed_var(), target_current_ub)))
                    cause = SolverCauses.ReasonerInference(
                        self,
                        DiffReasoner.InferenceCauses.TheoryPropagation(len(self.theory_propagation_causes)-1))

                    for enabler in propagator_group.potential_enablers:
                        enabler_active_neg = enabler.active.negation()
                        res = solver.set_bound_value(enabler_active_neg.signed_var, enabler_active_neg.bound_value, cause)
                        if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                            return res

        # Step (2) (see function documentation).
        while (self.next_unprocessed_solver_event_index < len(solver.events_trail[solver.dec_level]) 
            or self.propagators_pending_for_activation
        ):
            
            # Step (2.1) (see function documentation).
            while self.next_unprocessed_solver_event_index < len(solver.events_trail[solver.dec_level]):
                ev = solver.events_trail[solver.dec_level][self.next_unprocessed_solver_event_index]
                self.next_unprocessed_solver_event_index += 1
                
                # If a watched literal was newly entailed, check if makes enabling conditions of an edge / propagator
                # group true. If so, enqueue such edges / propagator groups to pending active propagators.
                for guard_bound_val in self.propagators_database.watches[ev.signed_var]:
                    if ev.new_bound_value.is_stronger_than(guard_bound_val):
                        for (propagator_group_id, enabler) in self.propagators_database.watches[ev.signed_var][guard_bound_val]:
                            if solver.is_literal_entailed(enabler.active) and solver.is_literal_entailed(enabler.valid):
                                self.propagators_pending_for_activation.insert(0, (propagator_group_id, enabler))
                
                if "bounds" in theory_propagation_levels:
                    res = self.theory_propagate_bound(Lit(ev.signed_var, ev.new_bound_value), solver)
                    if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                        return res
                
                if (isinstance(ev.cause, SolverCauses.ReasonerInference)
                    and ev.cause.reasoner == self
                    and isinstance(ev.cause.inference_info, DiffReasoner.InferenceCauses.EdgePropagation)
                ):
                    # We generated this event ourselves by edge propagation, we can safely
                    # ignore it as it would been handled immediately    
                    continue

                # Propagate bound change
                if ev.signed_var in self.propagators_active or len(self.propagators_active[ev.signed_var]) > 0:
                    res = self.run_propagation_loop(ev.signed_var, False, solver)
                    if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                        return res

            # Step (2.2) (see function documentation).
            while self.propagators_pending_for_activation:
                (propagator_group_id, enabler) = self.propagators_pending_for_activation.pop()
                propagator_group = self.propagators_database.propagators[propagator_group_id]

                assert propagator_group.enabler is None # CHECKME
                if propagator_group.enabler is not None:
                    continue
                propagator_group.enabler = enabler

                # If we are in a self loop, we handle it separately here,
                # since it is trivial and not supported by the propagation loop.
                if propagator_group.source == propagator_group.target:
                    if propagator_group.weight >= 0:
                        continue    # positive self-loop: useless / can be ignored
                    else:
                        return SolverConflictInfo.ReasonerExplanation((
                            propagator_group.enabler.active,
                            solver.vars_presence_literals[propagator_group.enabler.active.signed_var.var]))
                
                # The edge / propagator group is not a self loop:

                self.propagators_active.setdefault(propagator_group.source, []).append((
                    propagator_group.target,
                    propagator_group.weight,
                    propagator_group_id))

                self.propagation_metadata_trail[solver.dec_level].append(propagator_group_id)

                # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
                # Propagate new edge: implementation of the Cesta96 algorithm.
                # Propagates a **newly inserted** edge / propagator group
                # into a **consistent** constraint network / STN.
                # Does not support self loops (handled above).

                res = solver.set_bound_value(
                    propagator_group.target,
                    solver.bound_values[propagator_group.source],
                    SolverCauses.ReasonerInference(
                        self,
                        DiffReasoner.InferenceCauses.EdgePropagation(propagator_group_id)))
                
                if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                    return res
                elif res is True:
                    res = self.run_propagation_loop(propagator_group.target, True, solver)
                    if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                        return res

                # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

                if "edges" in theory_propagation_levels:
                    res = self.theory_propagate_edge(propagator_group_id, solver)
                    if isinstance(res, SolverConflictInfo.InvalidBoundUpdate):
                        return res

        return None
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def run_propagation_loop(self,
        original: SignedVar,
        cycle_on_update: bool,
        solver: Solver,
    ) -> Optional[SolverConflictInfo.InvalidBoundUpdate | SolverConflictInfo.ReasonerExplanation]:
        """
        TODO
        Incremental Bellman-Ford
        """
        ... # TODO

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def theory_propagate_bound(self,
        literal: Lit,
        solver: Solver,
    ) -> Optional[SolverConflictInfo.InvalidBoundUpdate | SolverConflictInfo.ReasonerExplanation]:
        ... # TODO

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def theory_propagate_edge(self,
        propagator_group_id: PropagatorGroupId,
        solver: Solver,
    ) -> Optional[SolverConflictInfo.InvalidBoundUpdate | SolverConflictInfo.ReasonerExplanation]:
        ... # TODO

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    #############################################################################
    #  EXPLANATION
    #############################################################################

    def explain(self,
        explanation_literals: List[Lit],
        literal: Lit,
        inference_cause: SolverCauses.ReasonerInference,
        solver: Solver,
    ) -> None:
        
        if isinstance(inference_cause, DiffReasoner.InferenceCauses.EdgePropagation):
            self.explain_bound_propagation(
                explanation_literals,
                literal,
                inference_cause.propagator_group_id,
                solver)

        elif isinstance(inference_cause, DiffReasoner.InferenceCauses.TheoryPropagation):
            theory_propagation_cause = self.theory_propagation_causes[inference_cause.theory_propagation_cause_index]

            if isinstance(theory_propagation_cause, DiffReasoner.TheoryPropagationCauses.Path):
                # We need to replace ourselves in exactly the context in which this theory propagation occurred.
                # Undo all events until we are back in the state where this theory propagation cause
                # had not occurred yet.
                # FIXME: KNOWN PROBLEM: this prevents the explanation of arbitrary literals which is required by some heuristics (e.g. LRB)
                while inference_cause.theory_propagation_cause_index < len(self.theory_propagation_causes):
                    # get an event to undo
                    propagator_group_id = self.propagation_metadata_trail[solver.dec_level].pop()

                    # NOTE: this is copied from `on_solver_backtrack_one_level`
                    if propagator_group_id is None:
                        self.theory_propagation_causes.pop()
                    else:
                        propagator_group = self.propagators_database.propagators[propagator_group_id]
                        self.propagators_active[propagator_group.source].pop()
                        propagator_group.enabler = None
            
            self.explain_theory_propagation(
                explanation_literals,
                theory_propagation_cause,
                solver)

        else:
            assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def explain_bound_propagation(self,
        explanation_literals: List[Lit],
        literal: Lit,
        propagator_group_id: DiffReasoner.PropagatorGroupId,
        solver: Solver,
        deep_explanation: bool=False,
    ) -> None:

        propagator_group = self.propagators_database.propagators[propagator_group_id]
        val = literal.bound_value

        enabler = propagator_group.enabler

        assert enabler is not None

        explanation_literals.append(enabler.active)
        explanation_literals.append(solver.vars_presence_literals[enabler.active.signed_var.var])

        cause_lit = Lit(propagator_group.source, BoundVal(val-propagator_group.weight))

        if deep_explanation:
            pass    # TODO

        explanation_literals.append(cause_lit)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def explain_theory_propagation(self,
        explanation_literals: List[Lit],
        cause: DiffReasoner.TheoryPropagationCauses.AnyCause,
        solver: Solver,
    ) -> None:
        
        if isinstance(cause, DiffReasoner.TheoryPropagationCauses.Path):

            path = self.get_theory_propagation_path(cause.source, cause.target, cause.triggering_propagator_group_id, solver)

            for edge in path:
                enabler = self.propagators_database.propagators[edge].enabler

                assert enabler is not None

                explanation_literals.append(enabler.active)
                explanation_literals.append(solver.vars_presence_literals[enabler.active.signed_var.var])

        elif isinstance(cause, DiffReasoner.TheoryPropagationCauses.Bounds):

            assert solver.is_literal_entailed(cause.source_lit) and solver.is_literal_entailed(cause.target_lit)

            explanation_literals.append(cause.source_lit)
            explanation_literals.append(cause.target_lit)
        
        else:
            assert False

    #############################################################################
    # UTILITIES
    #############################################################################

    def get_theory_propagation_path(self,
        source: SignedVar,
        target: SignedVar,
        through_propagator_group_id: DiffReasoner.PropagatorGroupId,
        solver: Solver,
    ) -> List[DiffReasoner.PropagatorGroupId]:
        """
        Returns a (shortest) path that triggered a theory propagation from `source`
        to `target`, through the edge corresponding to `through_propagator_group_id`.

        Getting this path is needed for explanations, to explain the contradiction
        encountered as a result of theory propagation triggered by the activation of 
        the edge corresponding to `through_propagator_group_id`. The path resulting
        from propagation would be conflicting with an edge from `target` to `source`,
        as it would have formed a negative cycle if activated.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def shortest_path_from_to(
            from_: SignedVar,
            to: SignedVar,
            dijkstra_state: DiffReasoner.DijkstraState,
            out: List[DiffReasoner.PropagatorGroupId],
        ):
            dijkstra_state.clear()
            dijkstra_state.enqueue(from_, BoundVal(0), None)
        
            # Run Dijkstra until exhaustion to find all reachable nodes
            self.run_dijkstra(dijkstra_state, lambda curr: curr == to, solver)

            # Go up the predecessors chain to extract the shortest path and append the edge to `out`.
            curr = to
            while curr != from_:
                edge = dijkstra_state.predecessor(curr)
                
                assert edge is not None

                out.append(edge)
                assert self.propagators_database.propagators[edge].target == curr
                curr = self.propagators_database.propagators[edge].source

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        res = []

        e = self.propagators_database.propagators[through_propagator_group_id]
        dijkstra_state = DiffReasoner.DijkstraState()

        # Add `e.source -> e.target` edge to path
        res.append(through_propagator_group_id)

        # Add `e.target -> target` subpath to path
        shortest_path_from_to(e.target, target, dijkstra_state, res)

        # Add `source -> e.source` subpath to path, computed in th reverse direction.
        shortest_path_from_to(e.source.opposite_signed_var(), source.opposite_signed_var(), dijkstra_state, res)

        return res

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def will_get_theory_propagation_path_succeed(self,
        source: SignedVar,
        target: SignedVar,
        through_propagator_group_id: DiffReasoner.PropagatorGroupId,
        successors: DijkstraState,
        predecessors: DijkstraState,
        solver: Solver,
    ) -> bool:
        """
        This method checks whether the `get_theory_propagation_path` method would be able to find a path
        for explaining a theory propagation.
        
        For efficiency reasons, we do not run the dijkstra algorithm.
        Instead we accept two prefilled Dijkstra state:
        - `successors`: one-to-all distances from `through_edge.target`
        - `predecessors`: one-to-all distances from `through_edge.source.opposite_signed_var`
        Complexity is linear in the length of the path to check.
        """
    
        # A path is active (i.e. findable by Dijkstra) if all nodes in it are not shown absent
        # We assume that the edges themselves are active (since it cannot be made inactive once activated).
        def path_active(src: SignedVar, tgt: SignedVar, dij: DiffReasoner.DijkstraState):
            curr = tgt
            if solver.is_literal_entailed(solver.vars_presence_literals[curr.var].negation()):
                return False
            while curr != src:
                pred_edge = dij.predecessor(curr)
                assert pred_edge is not None
                ee = self.propagators_database.propagators[pred_edge]
                curr = ee.source
                if solver.is_literal_entailed(solver.vars_presence_literals[curr.var].negation()):
                    return False
            return True
        
        e = self.propagators_database.propagators[through_propagator_group_id]

        # The path is active if both its prefix and its postfix are active
        active = (path_active(e.target, target, successors)
            and path_active(e.source.opposite_signed_var(), source.opposite_signed_var(), predecessors))

        # CHECKME assert not active or self.get_theory_propagation_path(source, target, through_propagator_group_id, solver)

        return active

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def run_dijkstra(self,
        dijkstra_state: DiffReasoner.DijkstraState,
        stop_condition: Callable[[SignedVar], bool],
        solver: Solver,
    ) -> None:
        """
        Run the Dijkstra algorithm from a pre-initialized queue.
        The queue should initially contain the origin of the shortest path problem.
        The algorithm will once the queue is exhausted or the predicate `stop_condition`
        returns true when given the next node to expand.
        
        At the end of the method, the `dijkstra_state` will contain the distances
        and predecessors of all nodes reached by the algorithm.
        """

        while dijkstra_state.queue:

            curr = dijkstra_state.dequeue()

            if curr is None:
                return
            
            curr_rdist, curr_node = curr

            if stop_condition(curr_node):
                return
            
            if solver.is_literal_entailed(solver.vars_presence_literals[curr_node.var].negation()):
                continue
                
            curr_bound = solver.bound_values[curr_node]

            # Process all outgoing edges
            for prop_target, prop_weight, prop_id in self.propagators_active[curr_node]:
                
                # TODO: here we check that the target is present and thus that all nodes in the path are present.
                # This is correct but overly pessimistic/
                # In theory, it would be sufficient to check that presence(...) is not entailed.
                # However this dijkstra is used in both forward and backward mode, starting from the negated node
                # for backward traversal.
                # The condition checking for the presence of prop_target.var to be entailed ensure
                # that if there is an edge `a -> b` then there is an (-b) -> (-a)` that can be used for backward traversal.
                # To properly fix this, we should index the active propagators backward and make this dijkstra pass
                # aware of whether it is traversing backward or forward.
                if (dijkstra_state.is_final(prop_target)
                    and solver.is_literal_entailed(solver.vars_presence_literals[prop_target.var])
                ):
                    
                    # We do not have a shortest path to this node yet, so compute a the reduced cost of the edge.

                    target_bound = solver.bound_values[prop_target]
                    cost = prop_weight

                    reduced_cost = cost + (curr_bound - target_bound)   # rcost(curr, tgt) = cost(curr, tgt) + val(curr) - val(tgt)
                    assert reduced_cost >= 0

                    reduced_dist = curr_rdist + reduced_cost    # rdist(orig, tgt) = dist(orig, tgt) + val(tgt) - val(orig)
                                                                #                  = dist(orig, curr) + cost(curr, tgt) + val(tgt) - val(orig)
                                                                #                  = [rdist(orig, curr) + val(orig) - val(curr)] + [rcost(curr, tgt) - val(tgt) + val(curr)] + val(tgt) - val(orig)
                                                                #                  = rdist(orig, curr) + rcost(curr, tgt)
                    dijkstra_state.enqueue(prop_target, BoundVal(reduced_dist), prop_id)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #