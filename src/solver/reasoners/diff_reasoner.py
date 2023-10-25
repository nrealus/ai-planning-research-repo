"""
This module defines the "Difference logic reasoner"
(aka "diff reasoner", aka "stn reasoner") of the solver.

This reasoner is dedicated to handling reified difference constraints of
the form `X + Y < c` (where `X` and `Y` are variables, and `c` is a constant).
"""

from __future__ import annotations

#################################################################################
# FILE CONTENTS:
# - DIFFERENCE LOGIC (STN) REASONER CLASS
#################################################################################

import heapq
from abc import ABC
from dataclasses import dataclass, field
from typing import (Callable, Dict, Iterable, List, NamedTuple, Optional, Set,
                    Tuple, Union)

from src.fundamentals import TRUE_LIT, Bound, Lit, SignedVar, Var
from src.solver.common import Causes, InvalidBoundUpdate, ReasonerBaseExplanation, SetGuardedByLits
from src.solver.reasoners.reasoner import Reasoner
from src.solver.solver_state import SolverState

MAX_INT = 2**64

#################################################################################

class DiffReasoner(Reasoner):
    """
    """

    #############################################################################
    # PROPAGATOR GROUPS, ENABLERS, PROPAGATORS DATABASE | DOC: OK 25.10.23
    #############################################################################

    @dataclass
    class PropaGroup():
        """
        Represents a group of (elementary) propagators for (maximum)
        difference constraints. The propagators of the group only differ
        by their enabling conditions (corresponding to `potential_enablers`).
        
        Note:
            In general, a propagator can be seen as an implicit encoding of
            a constraint, since its purpose is to propagate an update on one
            of its variables to the other ones.

            Our elementary propagators for difference constraints (see [1])
            allow us to reflect (i.e. propagate) the consequences of an update
            on the bound of the `source` signed variable on the bound of the
            `target` signed variable, when some conditions hold (the "enabling conditions").
            
            As such, by abuse of language and notation, a propagator in our case
            can also be seen as an encoding for a (directed) edge of a STN.

            [1]: Bit-Monnot, Arthur. "Enhancing Hybrid CP-SAT Search for Disjunctive Scheduling." 26th European Conference on Artificial Intelligence (ECAI 2023)). 2023
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        source: SignedVar
        """Source signed variable of the propagators of the group."""

        target: SignedVar
        """Target signed variable of the propagators of the group."""

        weight: Bound
        """Weight of the propagators of the group."""

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        enabler: Optional[DiffReasoner.Enabler] #FIXME rename to current_enabler ?
        """
        The enabler of the propagators of the group.

        It is non None when the group is active (i.e. when its propagators
        are active, i.e. participate in propagation).
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        potential_enablers: List[DiffReasoner.Enabler]
        """
        A set of potential enablers for the propagators of the group.

        The group (or rather its propagators) becomes active once one of
        these enablers' `active` and `valid` literals become True.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class PropaGroupId(NamedTuple):
        id: int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Enabler(NamedTuple):
        """
        Represents the conditions for a propagator to be enabled
        (which is for literals `active` and `valid` to both be true).
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        active: Lit
        """
        When this literal is present (i.e. its variable is present), then it is
        true iff the propagators (enabled by this enabler) are active.
        """

        valid: Lit
        """
        This literal is true iff the propagators (enabled by this enabler) are
        within its scope (i.e. when it is known to be sound to propagate
        a change from the propagator's source to the propagator's target)

        In the simplest cast, `valid = presence(active)` (since by construction
        `presence(active)` is true iff both the source and the target of the
        propagator are present).

        `valid` may be a more specific literal, but it always satisfies that
        `presence(active) => valid`.
        """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @dataclass
    class ConstraintsDatabase():
        """
        The constraints database, in which constraints are implemented through propagators.
        """

        _propagator_group_id_counter: int = 0
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        propagators: Dict[DiffReasoner.PropaGroupId,
                          DiffReasoner.PropaGroup] = field(default_factory=dict)
        """
        Stores all propagators (both active and inactive) as groups or "bundles" of
        propagators sharing their source, target, and weight.

        Note:
            Each difference constraint / STN edge (i.e. `v2-v1 <= d`, i.e. `v1 -d-> v2`)
            added is converted into 4 propagators, which correspond to:
            - the forward (source -> target) view of the "canonical" (i.e. "normal") edge
            - the backward (target -> source) view of the "canonical" (i.e. "normal") edge
            - the forward (source -> target) view of the "negated" (i.e. negation of canonical) edge
            - the backward (target -> source) view of the "negated" (i.e. negation of canonical) edge

            Make no mistake, at no point will those 4 propagators be part of the same group !
            None of them have the same source, target, and weight !
        """

        propagators_list: List[DiffReasoner.PropaGroupId] = field(default_factory=list)
        """Ordered view of `propagators`."""

        propagators_source_and_target: Dict[Tuple[SignedVar, SignedVar],
                                            List[DiffReasoner.PropaGroupId]] = field(default_factory=dict)
        """
        Associates (source, target) pairs of signed variables to propagators defined on them.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        intermittent_propagators: Dict[SignedVar,
                                       List[Tuple[SignedVar, Bound, Lit]]] = field(default_factory=dict)
        """
        Stores propagators whose active or not status may depend on the current state.
        
        Note:
            A key in the dictionary corresponds to a propagator's `source`.
            A value in the dictionary corresponds to a list of
            tuples `(target, weight, presence)` for that propagator.
            
            Here `presence` is a literal that is true iff the propagator is present.
            But note that handling of optional variables might allow an edge to
            propagate even if it is not known to be present yet.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        watches: SetGuardedByLits[Tuple[DiffReasoner.PropaGroupId,
                                        DiffReasoner.Enabler]] = field(default_factory=SetGuardedByLits)
        """
        Associates (watched) literals to (propagator, enabler) pairs.
        When a watched literal becomes true, and the associated enabler's
        `valid` and `active` literals are true as well, the associated propagator
        is triggered (i.e. added to a propagation queue).
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        propagators_events_trail: List[List[Optional[Tuple[DiffReasoner.PropaGroupId,
                                                           DiffReasoner.Enabler]]]] = field(default_factory=lambda:[[]])
        """
        Holds the trail of "propagator groups events", which are:
        - The addition of a new propagator group (encoded as None).
        - The addition of a new enabler to an existing propagator group's potential enablers (encoded as a tuple).

        The maintenance of the history of these events
        is necessary to allow resetting to a previous state.
        """

        next_newly_added_inactive_propagators_to_process_index: int = 0

    #############################################################################
    # THEORY PROPAGATION CAUSES, INFERENCE CAUSES | DOC: OK 25/10/23
    #############################################################################

    class ShortestPathTheoryPropCause(NamedTuple):
        """
        Represents a theory propagation cause corresponding to the activation
        of the propagators represented by `triggering_propagator_group_id`, as
        a result of the appearance of a new shortest path through it,
        between `source` and `target`.
        """
        source: SignedVar
        target: SignedVar
        triggering_propagator_group_id: DiffReasoner.PropaGroupId
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class InvalidBoundsTheoryPropCause(NamedTuple):
        """
        Represents a theory propagation cause corresponding to the incompability
        of the `source_lit` and `target_lit` literals with an "edge" (represented
        by a propagator group).
        """
        source_lit: Lit
        target_lit: Lit

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    TheoryPropCause = ShortestPathTheoryPropCause | InvalidBoundsTheoryPropCause

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class EdgePropInferenceCause(NamedTuple):
        """
        Represents the cause of an inference (i.e. bound update of a signed variable)
        corresponding to an edge propagation (i.e. application of a propagator representing that edge).
        """
        propagator_group_id: DiffReasoner.PropaGroupId
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class TheoryPropInferenceCause(NamedTuple):
        """
        Represents the cause of an inference (i.e. bound update of a signed variable)
        corresponding to a theory propagation, whose own cause was registered at
        `theory_propagation_cause_index` in `DiffReasoner.theory_propagation_causes`.
        """
        theory_propagation_cause_index: int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    InferenceCause = EdgePropInferenceCause | TheoryPropInferenceCause

    #############################################################################
    # DIJKSTRA STATE | DOC: OK 25/10/23
    #############################################################################

    @dataclass
    class DijkstraState:
        """
        A structure that contains the mutable data that is updated during a run of
        Dijkstra's algorithm. It is intended to be reusable across multiple runs.
        """
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        latest: Bound = Bound(0)
        """
        The latest distance that was extract from the queue. As a property of the
        Dijkstra algorithm, if a distance in the `distances` table is less than or
        equal to this value, then it will not change for the rest of the process.
        """

        distances: Dict[SignedVar, Tuple[Bound, Optional[DiffReasoner.PropaGroupId]]] = field(default_factory=dict)
        """
        Associates each node of the network to its distance. If the node is
        not an origin, it also indicates the latest edge on the shortest path to this node.
        """

        queue: List[Tuple[Bound, SignedVar]] = field(default_factory=list)
        """
        Elements of the queue that have not been extracted yet.
        Note that a single node might appear several times in the queue,
        in which case only the one with the smallest distance is relevant.
        The `Bound` corresponds to the reduced distance from the
        origin to the `SignedVar` node.

        Represented with Python's heapq, which is a min-heap.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def clear(self) -> None:
            self.latest = Bound(0)
            self.distances.clear()
            self.queue.clear()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def enqueue(self,
            node: SignedVar,
            dist: Bound,
            incoming_edge: Optional[DiffReasoner.PropaGroupId],
        ) -> None:
            """
            Add a node to the queue, indicating the distance from the origin and
            the latest edge on the path from the origin to this node.
            """
            prev = self.distances.get(node, None)
            if prev is None:
                previous_dist = MAX_INT
            else:
                previous_dist = prev[0]

            if dist < previous_dist:
                self.distances[node] = (dist, incoming_edge)
                heapq.heappush(self.queue, (dist, node))

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def dequeue(self) -> Optional[Tuple[Bound, SignedVar]]:
            """
            Remove the next element in the queue.
            Nodes are removed by increasing distance to the origin.
            Each node can only be extracted once.

            Returns:
                The removed element (if any).
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
                # A node with a better distance was previously extracted,
                # ignore this one as it cannot contribute to a shortest path
                return None
            
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def distance(self,
            node: SignedVar,
        ) -> Optional[Bound]:
            """
            Returns:
                The distance from the origin to this node, \
                    or None if the node was not reached by Dijkstra's algorithm
            """
            if node not in self.distances:
                return None
            else:
                return self.distances[node][0]

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def reached_nodes(self) -> Iterable[Tuple[Bound, SignedVar]]:
            """
            Returns:
                An iterator over all nodes (and their distances from \
                    the origin) that were reached by Dijkstra's algorithm.
            """
            return tuple((d,n) for (n,(d,_)) in self.distances.items())

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def predecessor(self,
            node: SignedVar,
        ) -> Optional[DiffReasoner.PropaGroupId]:
            """
            Returns:
                The predecessor edge from the origin to this node or None if it is an origin.

            Raises:
                KeyError: if the node has no associated distance (i.e. was not reached by the algorithm)
            """
            return self.distances[node][1]

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def is_final(self,
            node: SignedVar,
        ) -> bool:
            """
            Returns:
                True if the node has a distance that is guaranteed not to \
                    change in subsequent iterations. False otherwise.
            """
            if node not in self.distances:
                return False
            return self.distances[node][0] <= self.latest

    #############################################################################
    # INIT | DOC: OK 25/10/23
    #############################################################################
 
    def __init__(self,
        state: SolverState,
    ):

        self._state: SolverState = state

        self.cstrs_db: DiffReasoner.ConstraintsDatabase = DiffReasoner.ConstraintsDatabase()

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.propagators_active: Dict[SignedVar, List[Tuple[SignedVar, Bound, DiffReasoner.PropaGroupId]]] = {}
        """
        "Reverse" adjacency list of currenctly active edges / propagators.

        The key of the dictionary corresponds to the target of the edge / propagator.
        """

        self.propagators_pending_for_activation: List[Tuple[DiffReasoner.PropaGroupId, DiffReasoner.Enabler]] = []
        """
        A queue containing the propagators that are pending for (i.e. "have been marked for") activation. 
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.pending_bounds_to_update: Set[SignedVar] = set()

        self.internal_pending_bounds_to_update_queue: List[SignedVar] = []

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.propagation_metadata_trail: List[List[Optional[DiffReasoner.PropaGroupId]]] = [[]]
        """
        History of propagation events metadata. Outer list index: decision level.
        Inner list content corresponds to either:
        - The activation of a propagator group.
        - The triggering of theory propagation and appendance of its
        cause in `theory_propagation_causes`. Encoded as None.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.theory_propagation_causes: List[DiffReasoner.TheoryPropCause] = []
        """
        History of all performed theory propagations' causes.
        
        A theory propagation cause is added to this list when a None is added to `propagation_metadata_trail`. 
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        self.next_solver_event_to_process_index: int = 0
        """
        The index of the next unprocessed (i.e. not yet propagated)
        event in `SolverState._events_trail`.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#        self.num_propagations: int = 0
#
#        self.num_distance_updates: int = 0

    @property
    def state(self) -> SolverState:
        return self._state

    #############################################################################
    # (REIFIED) DIFFERENCE CONSTRAINT REGISTRATION | DOC: OK 25/10/23
    #############################################################################

    def add_reified_difference_constraint(self,
        reification_literal: Lit,
        source: Var,
        target: Var,
        weight: int,
    ) -> None:
        """
        Adds a new difference constraint `target - source <= weight`, i.e. STN
        edge `source --weight--> target`, which was already reified into `reification_literal`.

        Note:
        
            This is done by following these steps:

            1. Decompose the difference constraint into 4 propagators, which will be
            "active" iff `reification_literal` is true, and "valid" iff the variable
            of their target signed variable is present. (see `Enabler`).

            And then for each of these 4 propagators:

            2. Integrate the new propagator to the propagator database (recall that 
            a propagator group "bundles" propagators which only differ by enabling conditions).
            For each new propagator, this is done by either:

                - Merging / adding the new propagator into an existing group
                of propagators, by adding its enabler to their `potential_enablers`.
                
                - Tightening an already active existing group of propagators
                (superseded by the new propagator), by setting their weight to
                the new propagator's weight.
                
                - Ignoring the new propagator, if it is redundant with an
                existing one (i.e. if its weight is weaker than an existing
                propagator's with the same enabling conditions).
                
                - Creating a new propagator group with the new propagator's enabler,
                if there are no existing propagators with the same source and target.

            NOTE that merging, tightening, or ignoring is only done when the solver
            is at the top decision level. Beyond the top decision level, we always choose 
            to create a new propagator group, because it would be too complicated to
            undo/backtrack the reorganization of a propagator group.

            3. Postprocess the integration of the new propagator. The two possibilities are the following:
                
                - Either set the propagators of the group (to which the new propagator was added)
                as pending for activation, if the enabling conditions of the new propagator
                are satisfied (`active` and `valid` literals of its enabler are true).
                
                - Or set watch on the enabling conditions of the new propagator (the `active`
                and `valid` literals of its enabler), if they aren't known to be true yet, so
                that we're notified when one of them becomes true. (If both of them are true,
                the propagator group will be staged as pending for activation).
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def integrate_propagator_to_database(
            src: SignedVar,
            tgt: SignedVar,
            wgt: Bound, 
            eblr: DiffReasoner.Enabler,
        ) -> Tuple[DiffReasoner.PropaGroupId, str]:
            """
            Integrates a new propagator (defined by the `src`, `tgt`, `wgt` and `eblr`)
            to the propagator database. See step 2 of the function's documentation.
            """
 
            # Only optimize organisation of propagator groups at the top decision level,
            # because if done at a decision level beyond, it would to complex to undo/backtrack
            # the changes made to the groups.
            if self.state.decision_level == 0:
                
                self.cstrs_db.propagators_source_and_target.setdefault((src, tgt), [])

                # Search for a propagator group compatible with this propagator (same source and target)
                for existing_group_id in self.cstrs_db.propagators_source_and_target[(src, tgt)]:
                    existing_group = self.cstrs_db.propagators[existing_group_id]

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


                    # If the propagator's weight is strictly stronger than that of
                    # the group and they have the same one enabler, then just tighten
                    # the group by changing its weight to that of the propagator.
                    elif wgt.is_stronger_than(existing_group.weight-Bound(1)):

                        if not (len(existing_group.potential_enablers) == 1
                            and existing_group.potential_enablers[0] == eblr
                        ):
                            continue

                        if src in self.cstrs_db.intermittent_propagators:
                            # note that since we consider the case where there's only one potential enabler,
                            # there can only be 1 intermittent propagator.
                            for i in range(len(self.cstrs_db.intermittent_propagators[src])):

                                if (self.cstrs_db.intermittent_propagators[src][i]
                                    == (tgt, existing_group.weight, eblr.active)
                                ):
                                    self.cstrs_db.intermittent_propagators[src][i] = (tgt, wgt, eblr.active)
                                    break

                        existing_group.weight = wgt
                        return (existing_group_id, "tightening")

                    # If the propagator's weight is weaker than that of the group and they have the same one enabler,
                    # ignore the propagator and do nothing, because it is redundant.
                    elif existing_group.weight.is_stronger_than(Bound(wgt-1)):

                        if not (len(existing_group.potential_enablers) == 1
                            and existing_group.potential_enablers[0] == eblr
                        ):
                            continue
                        return (existing_group_id, "ignoring")

            # If the propagator couldn't be unified / integrated with an existing
            # propagator group, then just create a new propagator group for it.

            created_group_id = DiffReasoner.PropaGroupId(self.cstrs_db._propagator_group_id_counter)
            self.cstrs_db._propagator_group_id_counter += 1

            self.cstrs_db.propagators[created_group_id] = DiffReasoner.PropaGroup(src, tgt, wgt, None, [eblr])
            self.cstrs_db.propagators_list.append(created_group_id)
            self.cstrs_db.propagators_source_and_target.setdefault((src, tgt), []).append(created_group_id)

            self.cstrs_db.propagators_events_trail[self.state.decision_level].append(None)

            return (created_group_id, "creating")
            
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def postprocess_propagator_integration_into_database(
            propagator_group_id: DiffReasoner.PropaGroupId,
            propagator_integrated_by: str,
            eblr: DiffReasoner.Enabler,
        ) -> None:
            """
            Postprocesses the integration to the propagators database of a new propagator.
            See step 3 (function documentation).
            """

            # NOTE: The case of `propagator_integrated_by == "ignoring"` is dealt with in the main function.

            # If propagator was created into a new group or was merged into an existing one,
            # there are different possibilities, depending on whether it is currently enabled
            # or not.FIXME: Note that we should make sure that when backtracking beyond the
            # current decision level, we should deactivate the edge
            if (propagator_integrated_by == "creating" 
                or propagator_integrated_by == "merging"
            ):
                # If the propagator can never be active/present, do nothing.
                edge_valid = self.state.presence_literal_of(eblr.active.signed_var.var)
                if (self.state.entails(eblr.active.neg)
                    or self.state.entails(edge_valid.neg)
                ):
                    return
                
                # If the propagator is always active in the current (and following) decision
                # levels, enqueue it for activation.
                elif self.state.entails(eblr.active) and self.state.entails(eblr.valid):
                    self.propagators_pending_for_activation.insert(0, (propagator_group_id, eblr))

                # If the propagator isn't known to be active or inactive yet, 
                # record the fact that:
                # - If the enabling conditions hold (`enabler.valid` and `enabler.active` are true),
                #   then the propagator should be enabled
                # - If the propagator is inconsistent, then the `enabler.active` should be made false
                else:

                    # Set a watch on both `enabler.active` and `enabler.valid` literals
                    # (when one of them becomes true, we will still have to check that the
                    # other one becomes true as well)
                    self.cstrs_db.watches.add((propagator_group_id, eblr), eblr.active)
                    self.cstrs_db.watches.add((propagator_group_id, eblr), eblr.valid)

                    self.cstrs_db.intermittent_propagators.setdefault(
                        self.cstrs_db.propagators[propagator_group_id].source, []).append((
                            self.cstrs_db.propagators[propagator_group_id].target,
                            self.cstrs_db.propagators[propagator_group_id].weight,
                            eblr.active))

                    self.cstrs_db.propagators_events_trail[self.state.decision_level].append((propagator_group_id, eblr))

            # If an existing group was tightened (as a result of
            # a new propagator's integration into the database), then:
            # - If the group wasn't already active, we don't need to do anything.
            # - If the group was already active, we need to force its propagation
            #   (which we do by "pretending" it was previously inactive and then
            #   enqueuing it for activation)
            elif propagator_integrated_by == "tightening":

                if self.state.entails(eblr.active) and self.state.entails(eblr.valid):
                    self.cstrs_db.propagators[propagator_group_id].enabler = None
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
        edge_valid = self.state.presence_literal_of(reification_literal.signed_var.var)
        assert self.state.entails_implication(edge_valid, self.state.presence_literal_of(source))
        assert self.state.entails_implication(edge_valid, self.state.presence_literal_of(target))

        # The edge will be decomposed into 4 propagators:
        # 2 "canonical", and 2 "negated" (or "inverted": swapped source and target for them).
        # 
        # A "canonical" (source-to-target) propagator is valid
        # when `presence(target) => edge_valid`. This is because modifying
        # the target's domain is only meaningful if the edge is present.
        # Analogously, a "negated" (target-to-source) propagator is valid
        # when `presence(source) => edge_valid`.
        #
        # As such, we need to determine a literal that is true iff a
        # "canonical" (source-to-target) propagator is valid, as well as
        # a literal that is true iff a "negated" (target-to-source) propagator is valid.

        # "Canonical" propagator case.
        if self.state.entails_implication(self.state.presence_literal_of(target), edge_valid):
            # If it is statically known that `presence(target) => edge_valid`,
            # the propagator is always valid
            source_to_target_propagator_valid = TRUE_LIT
        else:
            # Given that `presence(source) & presence(target) <=> edge_valid`, we can infer
            # that the propagator becomes valid (i.e. `presence(target) => edge_valid` holds)
            # when `presence(source)` becomes true
            source_to_target_propagator_valid = self.state.presence_literal_of(source)

        # "Negated" propagator case (analogous).
        if self.state.entails_implication(self.state.presence_literal_of(source), edge_valid):
            target_to_source_propagator_valid = TRUE_LIT
        else:
            target_to_source_propagator_valid = self.state.presence_literal_of(target)

        propagators = [

            # "canonical" (i.e. "normal") edge: active <=> source ---(weight)---> target
            (SignedVar(source, True),
            SignedVar(target, True),
            Bound(weight),
            DiffReasoner.Enabler(reification_literal, source_to_target_propagator_valid)),

            (SignedVar(target, False),
            SignedVar(source, False),
            Bound(weight),
            DiffReasoner.Enabler(reification_literal, target_to_source_propagator_valid)),

            # "negated" (i.e. "inverted") edge: !active <=> source <----(-weight-1)--- target
            (SignedVar(target, True),
            SignedVar(source, True),
            Bound(-weight-1),
            DiffReasoner.Enabler(reification_literal.neg, target_to_source_propagator_valid)),

            (SignedVar(source, False),
            SignedVar(target, False),
            Bound(-weight-1),
            DiffReasoner.Enabler(reification_literal.neg, source_to_target_propagator_valid)),

        ]

        for p in propagators:

            (group_id, integration_kind) = integrate_propagator_to_database(p[0], p[1], p[2], p[3])

            if integration_kind == "ignoring":
                self.cstrs_db.propagators[group_id].enabler = None
                continue

            postprocess_propagator_integration_into_database(group_id, integration_kind, p[3])

    #############################################################################
    # SOLVER DECISION LEVEL CHANGE CALLBACKS | DOC: OK 25/10/23
    #############################################################################

    def on_solver_increment_decision_level_by_one(self) -> None:
        """
        See `Reasoner.on_solver_increment_decision_level_by_one`.
        """

        self.next_solver_event_to_process_index = 0

        if len(self.propagation_metadata_trail) == self.state.decision_level:
            self.propagation_metadata_trail.append([])

        if len(self.cstrs_db.propagators_events_trail) == self.state.decision_level:
            self.cstrs_db.propagators_events_trail.append([])

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def on_solver_backtrack_one_decision_level(self) -> None:
        """
        See `Reasoner.on_solver_backtrack_one_decision_level`.
        """

        self.propagators_pending_for_activation.clear()

        for ev in reversed(self.propagation_metadata_trail[self.state._decision_level+1]):
            if ev is None:
                self.theory_propagation_causes.pop()
            else:
                propagator_group = self.cstrs_db.propagators[ev]
                self.propagators_active[propagator_group.source].pop()
                propagator_group.enabler = None

        self.propagation_metadata_trail[self.state.decision_level+1].clear()

        self.next_solver_event_to_process_index = self.state.num_events_at_current_decision_level

        for ev in reversed(self.cstrs_db.propagators_events_trail[self.state.decision_level+1]):

            if ev is None:
                propagator_group_id = self.cstrs_db.propagators_list.pop()
                propagator_group = self.cstrs_db.propagators.pop(propagator_group_id)
                
                pg_src = propagator_group.source
                pg_tgt = propagator_group.target

                if ((pg_src, pg_tgt) in self.cstrs_db.propagators_source_and_target
                    and len(self.cstrs_db.propagators_source_and_target[(pg_src, pg_tgt)]) > 0
                ):
                    self.cstrs_db.propagators_source_and_target[(pg_src, pg_tgt)].pop()
                # NOTE: no need to reset/update self.cstrs_db.next_new_constraint_index !

            else:
                (propagator_group_id, enabler) = ev
                self.cstrs_db.watches.remove((propagator_group_id, enabler), enabler.active)
                self.cstrs_db.watches.remove((propagator_group_id, enabler), enabler.valid)
                propagator_group = self.cstrs_db.propagators[propagator_group_id]
                self.cstrs_db.intermittent_propagators[propagator_group.source].pop()

        self.cstrs_db.propagators_events_trail[self.state.decision_level+1].clear()

    #############################################################################
    #  PROPAGATION
    #############################################################################

    def propagate(self) -> Optional[InvalidBoundUpdate | ReasonerBaseExplanation]:
        """
        Main propagation method of the Difference Logic reasoner.

        Returns:
            A base explanation for a conflict, if one is encountered. \
                None if propagation is successful.

        Note:
            See `_propagate` for more complete documentation.
        """
        return self._propagate(("bounds",))
        # return self._propagate(solver, ("bounds", "edges"))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _propagate(self,
        theory_propagation_levels: Tuple[str, ...]=("bounds",),
    ) -> Optional[InvalidBoundUpdate | ReasonerBaseExplanation]:
        """
        Propagates all edges / propagator groups that have been marked as
        active since the last propagation.

        (1) First, processes each newly added inactive(*) edge / propagator
        group once, to check if it can be added to the solver based on the literals
        of its extremities (i.e. minimal and maximal possible values for the edge).
        If not make its enablers false. This step is equivalent to "bound theory propagation",
        but needs to be done independenty because we do not have events for
        the initial domain bound values of variables.

            (*) A newly added edge / propagator group can be active
            (see `add_reified_difference_constraint`), in which case
            it is added to pending propagator activations.

        (2):
        (2.1) Then, propagate all literals changes.
        
        (2.2) And then process / loop through the edges / propagator groups pending for activation
        (including those that were enqueued at step 2.1). This is done by:
            
            - Checking if the edge / propagator group is a self loop:
                
                - A positive self loop is ignored (move on to next edge / propagator)
                
                - A negative self loop is a contradiction, for a which a ReasonerExplanation
                is returned (to build an explanation later)
            
            - If not a self-loop, mark the edge / propagator group as active and propagate it with
            the Cesta96 algorithm (which runs an incremental Bellman-Ford algorithm over active
            edges / propagator groups).
            The assumptions needed to do this (i.e. the edge / propagator group must be newly 
            inserted and the constraint network / STN must be consistent) are indeed satisfied.
        
        Finally, doing step (2.1) before (2.2) is necessary because cycle detection on the
        insertion of a new edge / propagator group requires a consistent constraint
        network (STN) and no interference of external bound updates.
        """

        # Step (1) (see function documentation).
        if "bounds" in theory_propagation_levels:

            while (self.cstrs_db.next_newly_added_inactive_propagators_to_process_index
                   < len(self.cstrs_db.propagators_list)
            ):

                propagator_group = self.cstrs_db.propagators[
                    self.cstrs_db.propagators_list[
                        self.cstrs_db.next_newly_added_inactive_propagators_to_process_index]]
                self.cstrs_db.next_newly_added_inactive_propagators_to_process_index += 1
                
                if propagator_group.enabler is not None:
                    continue

                target_new_lb = Bound(self.state.bound_of(propagator_group.source)
                                      + propagator_group.weight)
                target_current_ub = self.state.bound_of(propagator_group.target.opposite)

                # If the lower bound implied by the propagator for the target is greater
                # than its current upper bound, then the edge is impossible / is a contradiction.
                # Add a theory propagation cause to allow explanation, and make all potential
                # enablers of the edge / propagator group false.
                if target_new_lb + target_current_ub < 0:

                    self.theory_propagation_causes.append(
                        DiffReasoner.InvalidBoundsTheoryPropCause(
                            Lit(propagator_group.source, self.state.bound_of(propagator_group.source)), 
                            Lit(propagator_group.target.opposite, target_current_ub)))
                    self.propagation_metadata_trail[self.state.decision_level].append(None)
                    
                    inference_info = DiffReasoner.TheoryPropInferenceCause(len(self.theory_propagation_causes)-1)
                    cause = Causes.ReasonerInference(id(self), inference_info)

                    for enabler in propagator_group.potential_enablers:

                        res = self.state.set_literal(enabler.active.neg, cause)

                        if isinstance(res, InvalidBoundUpdate):
                            return res

        # Step (2) (see function documentation).
        while (self.next_solver_event_to_process_index
               < self.state.num_events_at_current_decision_level
               or self.propagators_pending_for_activation
        ):
            
            # Step (2.1) (see function documentation).
            while (self.next_solver_event_to_process_index
                   < self.state.num_events_at_current_decision_level
            ):

                ev = self.state._events_trail[self.state.decision_level][self.next_solver_event_to_process_index]
                self.next_solver_event_to_process_index += 1
                
                # If a watched literal was newly entailed, check if makes enabling conditions of an edge / propagator
                # group true. If so, enqueue such edges / propagator groups to pending active propagators.
                for propagator_group_id, enabler in self.cstrs_db.watches.elements_guarded_by(Lit(ev.signed_var, ev.bound)):

                    if (self.state.entails(enabler.active)
                        and self.state.entails(enabler.valid)
                    ):
                        self.propagators_pending_for_activation.insert(0, (propagator_group_id, enabler))
                
                if "bounds" in theory_propagation_levels:

                    res = self._theory_propagate_bound(Lit(ev.signed_var, ev.bound))

                    if res is not None:
                        return res
                
                if (isinstance(ev.cause, Causes.ReasonerInference)
                    and ev.cause.reasoner_id == id(self)
                    and isinstance(ev.cause.inference_info, DiffReasoner.EdgePropInferenceCause)
                ):
                    # We generated this event ourselves by edge propagation, we can safely
                    # ignore it as it would been handled immediately    
                    continue

                # Propagate bound change
                if (ev.signed_var in self.propagators_active
                    and len(self.propagators_active[ev.signed_var]) > 0
                ):

                    res = self._run_propagation_loop(ev.signed_var, False)

                    if res is not None:
                        return res

            # Step (2.2) (see function documentation).
            while self.propagators_pending_for_activation:

                (propagator_group_id, enabler) = self.propagators_pending_for_activation.pop()
                propagator_group = self.cstrs_db.propagators[propagator_group_id]

                if propagator_group.enabler is not None:
                    continue

                propagator_group.enabler = enabler

                # If we are in a self loop, we handle it separately here,
                # since it is trivial and not supported by the propagation loop.
                if propagator_group.source == propagator_group.target:

                    if propagator_group.weight >= 0:
                        continue    # positive self-loop: useless / can be ignored
                    else:
                        return ReasonerBaseExplanation((propagator_group.enabler.active,
                                                        self.state.presence_literal_of(propagator_group.enabler
                                                                                       .active.signed_var.var)))

                # The edge / propagator group is not a self loop:

                self.propagators_active.setdefault(propagator_group.source, []).append((propagator_group.target,
                                                                                        propagator_group.weight,
                                                                                        propagator_group_id))

                self.propagation_metadata_trail[self.state.decision_level].append(propagator_group_id)

                # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

                # Propagate new edge: implementation of the Cesta96 algorithm.
                # (Amedeo Cesta and Angelo Oddi, ‘Gaining Efficiency and Flexibility in the Simple Temporal Problem.’, in TIME, pp. 45–50, (1996).)
                # Propagates a **newly inserted** edge / propagator group
                # into a **consistent** constraint network / STN.
                # Does not support self loops (handled above).

                tgt_bound_val = Bound(self.state.bound_of(propagator_group.source) + propagator_group.weight)
                inference_info = DiffReasoner.EdgePropInferenceCause(propagator_group_id)
                res = self.state.set_bound(propagator_group.target,
                                           tgt_bound_val,
                                           Causes.ReasonerInference(id(self), inference_info))
                match res:

                    case InvalidBoundUpdate():
                        return res
                    
                    case True:
                        res = self._run_propagation_loop(propagator_group.target, True)

                        if res is not None:
                            return res

                # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

                if "edges" in theory_propagation_levels:

                    res = self._theory_propagate_edge(propagator_group_id)

                    if res is not None:
                        return res

        return None
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _run_propagation_loop(self,
        original: SignedVar,
        cycle_on_update: bool,
    ) -> Optional[InvalidBoundUpdate | ReasonerBaseExplanation]:
        """
        Runs an incremental Bellman-Ford algorithm over the active edges.
        It is an adaptation of the incremental propagation algorithm for STNs by Cesta and Oddi.

        See: Bit-Monnot, Arthur. "Enhancing Hybrid CP-SAT Search for Disjunctive Scheduling." 26th European Conference on Artificial Intelligence (ECAI 2023)). 2023
        """

#        self.num_propagations += 1

        for vb in self.internal_pending_bounds_to_update_queue:
            self.pending_bounds_to_update.remove(vb)
        self.internal_pending_bounds_to_update_queue.clear()

        assert len(self.pending_bounds_to_update) == 0

        self.pending_bounds_to_update.add(original)
        self.internal_pending_bounds_to_update_queue.insert(0, original)

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def extract_cycle(
            vb: SignedVar
        ) -> Tuple[Lit,...]:
            
            explanation_literals: List[Lit] = []
            curr = vb
            cycle_length = 0
            while True:
                value = self.state.bound_of(curr)

                ev = self.state.get_first_event_entailing(Lit(curr, value))
                assert ev is not None
                assert ev.index[0] == self.state.decision_level

                if not (isinstance(ev.cause, Causes.ReasonerInference)
                        and isinstance(ev.cause.inference_info, DiffReasoner.EdgePropInferenceCause)
                ):
                    assert False

                edge = self.cstrs_db.propagators[ev.cause.inference_info.propagator_group_id]
                if edge.enabler is None:
                    assert False
                curr = edge.source
                cycle_length += edge.weight

                explanation_literals.append(edge.enabler.active)
                explanation_literals.append(self.state.presence_literal_of(edge.enabler.active.signed_var.var))

                if curr == vb:
                    return tuple(explanation_literals)

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        while self.internal_pending_bounds_to_update_queue:
            source = self.internal_pending_bounds_to_update_queue.pop()
            source_bound = self.state.bound_of(source)

            # If the bound was already updated, ignore and move on to next
            if source not in self.pending_bounds_to_update:
                continue

            # Remove immediately even if we are not done with the update yet.
            # This allows to keep the `internal_pending_bounds_to_update_queue`
            # and `pending_bounds_to_update` in sync: if an element is
            # in `pending_bounds_to_update`, then it is also in `internal_pending_bounds_to_update_queue`.
            self.pending_bounds_to_update.remove(source)

            if not source in self.propagators_active:
                continue

            for target, weight, group_id in self.propagators_active[source]:
                assert source != target

                candidate = Bound(source_bound + weight)
                inference_info = DiffReasoner.EdgePropInferenceCause(group_id)

                res = self.state.set_bound(target,
                                           candidate,
                                           Causes.ReasonerInference(id(self), inference_info))

                match res:

                    case InvalidBoundUpdate():
                        return res
                    
                    case True:
    #                    self.num_distance_updates += 1
                        if cycle_on_update and target == original:
                            return ReasonerBaseExplanation(extract_cycle(target))
                        
                        self.internal_pending_bounds_to_update_queue.insert(0, target)
                        self.pending_bounds_to_update.add(target)

        return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _theory_propagate_bound(self,
        literal: Lit,
    ) -> Optional[InvalidBoundUpdate | ReasonerBaseExplanation]:
        """
        Perform the theory propagation that follows
        from the addition of a new bound on a variable.

        A bound on X indicates a shortest path O -> X in an STN
        (where 0 is a virtual timepoint that represents the time
        origin in the STN). For any timepoint Y we also know the
        length of the shortest path Y -> 0 (value of the symmetric
        bound / bound of the opposite signed variable). Thus, we check
        that for each potential edge X -> Y that it would not create
        a negative cycle 0 -> X -> Y -> O. If that's the case, we
        disable this X -> Y edge by setting its enabler (or rather
        its `active` literal) to false.
        """
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def potential_out_edges(
            src: SignedVar,
        ) -> List[Tuple[SignedVar, Bound, Lit]]:
            return self.cstrs_db.intermittent_propagators.get(src, [])

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def dist_to_origin(
            lit: Lit,
        ) -> Bound:
            return lit.bound #REVIEW

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        x = literal.signed_var
        dist_o_x = dist_to_origin(literal)

        for out_target, out_weight, out_presence in potential_out_edges(x):

            if self.state.entails(out_presence.neg):
                continue

            y, w = out_target, out_weight
            y_neg_lit = Lit(y.opposite, self.state.bound_of(y.opposite))
            dist_y_o = dist_to_origin(y_neg_lit)

            cycle_length = dist_o_x + w + dist_y_o

            if cycle_length >= 0:
                continue

            # If 0 -> X -> Y -> 0 forms a negative cycle, there is a contradiction and
            # we record its cause so we can retrieve it if an explanation is needed.
            # Here, we know that the update on the bound value of `literal`'s variable
            # triggered the propagation. However, it is possible that a less constraint
            # bound would have triggered the propagation as well. We thus replace `literal`
            # with the smallest update that would have triggered the propagation.
            # The consequence is that the clauses inferred through explanation will be stronger.
            relaxed_literal = Lit(literal.signed_var, Bound(literal.bound - cycle_length - 1))
            # The relaxed literal would have triggered a proapgation with the cycle having exactly length -1
            assert dist_to_origin(relaxed_literal) + w + dist_y_o == -1

            self.theory_propagation_causes.append(
                DiffReasoner.InvalidBoundsTheoryPropCause(relaxed_literal, y_neg_lit))
            self.propagation_metadata_trail[self.state.decision_level].append(None)

            # Disable the edge

            inference_info = DiffReasoner.TheoryPropInferenceCause(len(self.theory_propagation_causes)-1)

            self.state.set_literal(out_presence.neg,
                                   Causes.ReasonerInference(id(self), inference_info))

        return None

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _theory_propagate_edge(self,
        propagator_group_id: PropaGroupId,
    ) -> Optional[InvalidBoundUpdate | ReasonerBaseExplanation]:
        """
        Perform the theory propagation that follows
        from the addition of the given (new) edge.

        In essence, we find all shortest paths A -> B that contain
        the new edge. Then we check if there exist an inactive
        edge BA where `weight(BA) + dist(AB) < 0`.
        For each such edge, we set its enabler to false
        since its addition would result in a negative cycle.
        """

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def potential_out_edges(
            src: SignedVar,
        ) -> List[Tuple[SignedVar, Bound, Lit]]:
            return self.cstrs_db.intermittent_propagators.get(src, [])

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        edge = self.cstrs_db.propagators[propagator_group_id]

        source = edge.source
        target = edge.target
        
        successors = DiffReasoner.DijkstraState()
        predecessors = DiffReasoner.DijkstraState()

        # Find all nodes reachable from target(edge), including itself
        self._distances_from(target, successors)

        # Find all nodes that can reach source(edge), including itself
        # predecessors nodes and edge are in the inverse direction.
        self._distances_from(source.opposite, predecessors)

        # Iterate through all predecessors, they will constitute the source of our shortest paths
        for (pred_dist, pred) in predecessors.reached_nodes():

            # Find all potential edges that target this predecessor.
            # Note that the predecessor is the inverse view (opposite signed variable),
            # hence the potential out_edge are all inverse edges.
            for potential_target, potential_weight, potential_presence in potential_out_edges(pred):

                # potential is an edge W -> pred. Do we have X in the succesors ?
                forward_dist = successors.distance(potential_target.opposite)
                if forward_dist is None:
                    continue

                back_dist = pred_dist + potential_weight
                total_dist = back_dist + edge.weight + forward_dist

                # If this edge would be violated and is not inactive yet:
                if total_dist < 0 and not self.state.entails(potential_presence.neg):

                    # careful: we are doing batched eager updates involving optional variable
                    # When doing the shortest path computation, we followed any edge that was
                    # not proven inactive yet. The current theory propagation, might have been
                    # preceded by an other affecting the network. Here we thus check that 
                    # path we initially computed is still active, i.e., that no other propagation
                    # made any of its edges inactive. This is necessary because we need to
                    # be able to explain any change and explanation would not follow
                    # any inactive edge when recreating the path.
                    active = self._will_get_theory_propagation_path_succeed(pred.opposite,
                                                                           potential_target.opposite,
                                                                           propagator_group_id,
                                                                           successors,
                                                                           predecessors)
        
                    # If the shortest path would be made inactive, ignore this update
                    # Note that on a valid constraint network, making this change should be
                    # either a noop or redundant with another constraint.
                    if not active:
                        continue

                    # Record the cause so we can explain the
                    # changes resulting from making the edge inactive.
                    self.theory_propagation_causes.append(
                        DiffReasoner.ShortestPathTheoryPropCause(pred.opposite,
                                                                 potential_target.opposite,
                                                                 propagator_group_id))
                    self.propagation_metadata_trail[self.state.decision_level].append(None)
                    
                    # Update to force this edge to be inactive

                    inference_info = DiffReasoner.TheoryPropInferenceCause(len(self.theory_propagation_causes)-1)

                    res = self.state.set_literal(potential_presence.neg,
                                                 Causes.ReasonerInference(id(self), inference_info))

                    if isinstance(res, InvalidBoundUpdate):
                        return res

        return None

    #############################################################################
    # EXPLANATION | DOC: OK 25/10/23
    #############################################################################

    def explain(self,
        explanation: List[Lit],
        literal: Lit,
        inference_cause: Causes.ReasonerInference,
    ) -> None:
        """
        See `Reasoner.explain`.
        """
        
        match inference_cause:

            case DiffReasoner.EdgePropInferenceCause():

                self._explain_bound_propagation(explanation,
                                                literal,
                                                inference_cause.propagator_group_id)

            case DiffReasoner.TheoryPropInferenceCause():

                theory_propagation_cause = \
                    self.theory_propagation_causes[inference_cause.theory_propagation_cause_index]

                if isinstance(theory_propagation_cause, DiffReasoner.ShortestPathTheoryPropCause):
                    # We need to replace ourselves in exactly the context
                    # in which this theory propagation occurred.
                    # Undo all events until we are back in the state
                    # where this theory propagation cause had not occurred yet.
                    # FIXME: KNOWN PROBLEM: this prevents the explanation of arbitrary literals which is required by some heuristics (e.g. LRB)
                    while (inference_cause.theory_propagation_cause_index
                           < len(self.theory_propagation_causes)
                    ):
                        # get an event to undo
                        propagator_group_id = self.propagation_metadata_trail[self.state.decision_level].pop()

                        # NOTE: this is copied from `on_solver_backtrack_one_decision_level`
                        if propagator_group_id is None:
                            self.theory_propagation_causes.pop() 
                        else:
                            propagator_group = self.cstrs_db.propagators[propagator_group_id]
                            self.propagators_active[propagator_group.source].pop()
                            propagator_group.enabler = None
                
                self._explain_theory_propagation(explanation, theory_propagation_cause)

            case _:
                assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _explain_bound_propagation(self,
        explanation: List[Lit],
        literal: Lit,
        propagator_group_id: DiffReasoner.PropaGroupId,
        deep_explanation: bool=False,
    ) -> None:

        propagator_group = self.cstrs_db.propagators[propagator_group_id]
        val = literal.bound

        enabler = propagator_group.enabler

        assert enabler is not None

        explanation.append(enabler.active)
        explanation.append(self.state.presence_literal_of(enabler.active.signed_var.var))

        cause_lit = Lit(propagator_group.source, Bound(val-propagator_group.weight))

        if deep_explanation:
            pass    # TODO

        explanation.append(cause_lit)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _explain_theory_propagation(self,
        explanation: List[Lit],
        cause: DiffReasoner.TheoryPropCause,
    ) -> None:
        """
        Explains an update (entailment of `literal`) that was caused
        by theory propagation, either on edge addition or bound update.
        """
        
        match cause:

            case DiffReasoner.ShortestPathTheoryPropCause():

                path = self._get_theory_propagation_path(cause.source,
                                                        cause.target,
                                                        cause.triggering_propagator_group_id)

                for edge in path:
                    enabler = self.cstrs_db.propagators[edge].enabler

                    assert enabler is not None

                    explanation.append(enabler.active)
                    explanation.append(self.state.presence_literal_of(enabler.active.signed_var.var))

            case DiffReasoner.InvalidBoundsTheoryPropCause():

                assert self.state.entails(cause.source_lit) and self.state.entails(cause.target_lit)

                explanation.append(cause.source_lit)
                explanation.append(cause.target_lit)
            
            case _:
                assert False

    #############################################################################
    # UTILITIES | DOC: OK 25/10/23
    #############################################################################

    def _get_theory_propagation_path(self,
        source: SignedVar,
        target: SignedVar,
        through_propagator_group_id: DiffReasoner.PropaGroupId,
    ) -> List[DiffReasoner.PropaGroupId]:
        """
        Returns:
            A (shortest) path that triggered a theory propagation from `source` \
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
            out: List[DiffReasoner.PropaGroupId],
        ):
            dijkstra_state.clear()
            dijkstra_state.enqueue(from_, Bound(0), None)
        
            # Run Dijkstra until exhaustion to find all reachable nodes
            self._run_dijkstra(dijkstra_state, lambda curr: curr == to)

            # Go up the predecessors chain to extract the shortest path and append the edge to `out`.
            curr = to
            while curr != from_:
                edge = dijkstra_state.predecessor(curr)
                
                assert edge is not None

                out.append(edge)
                assert self.cstrs_db.propagators[edge].target == curr
                curr = self.cstrs_db.propagators[edge].source

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
        res = []

        e = self.cstrs_db.propagators[through_propagator_group_id]
        dijkstra_state = DiffReasoner.DijkstraState()

        # Add `e.source -> e.target` edge to path
        res.append(through_propagator_group_id)

        # Add `e.target -> target` subpath to path
        shortest_path_from_to(e.target, target, dijkstra_state, res)

        # Add `source -> e.source` subpath to path, computed in th reverse direction.
        shortest_path_from_to(e.source.opposite, source.opposite, dijkstra_state, res)

        return res

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _will_get_theory_propagation_path_succeed(self,
        source: SignedVar,
        target: SignedVar,
        through_propagator_group_id: DiffReasoner.PropaGroupId,
        successors: DijkstraState,
        predecessors: DijkstraState,
    ) -> bool:
        """
        This method checks whether the `get_theory_propagation_path`
        method would be able to find a path for explaining a theory propagation.
        
        For efficiency reasons, we do not run the dijkstra algorithm.
        Instead we accept two prefilled Dijkstra state:
        - `successors`: one-to-all distances from `through_edge.target`
        - `predecessors`: one-to-all distances from `through_edge.source.opposite_signed_var`
        Complexity is linear in the length of the path to check.
        """
    
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        # A path is active (i.e. findable by Dijkstra) if all nodes in it are not shown absent
        # We assume that the edges themselves are active (since it cannot be made inactive once activated).
        def path_active(src: SignedVar, tgt: SignedVar, dij: DiffReasoner.DijkstraState):
            curr = tgt
            if self.state.entails(self.state.presence_literal_of(curr.var).neg):
                return False
            while curr != src:
                pred_edge = dij.predecessor(curr)
                assert pred_edge is not None
                ee = self.cstrs_db.propagators[pred_edge]
                curr = ee.source
                if self.state.entails(self.state.presence_literal_of(curr.var).neg):
                    return False
            return True
        
        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        e = self.cstrs_db.propagators[through_propagator_group_id]

        # The path is active if both its prefix and its postfix are active
        active = (path_active(e.target, target, successors)
            and path_active(e.source.opposite, source.opposite, predecessors))

        # REVIEW assert not active or self.get_theory_propagation_path(source, target, through_propagator_group_id, solver)

        return active

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _run_dijkstra(self,
        dijkstra_state: DiffReasoner.DijkstraState,
        stop_condition: Callable[[SignedVar], bool],
    ) -> None:
        """
        Runs the Dijkstra algorithm from a pre-initialized queue.
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
            
            if self.state.entails(self.state.presence_literal_of(curr_node.var).neg):
                continue
                
            curr_bound = self.state.bound_of(curr_node)

            # Process all outgoing edges
            if curr_node not in self.propagators_active:
                continue
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
                if (not dijkstra_state.is_final(prop_target)
                    and self.state.entails(self.state.presence_literal_of(prop_target.var))
                ):
                    
                    # We do not have a shortest path to this node yet, so compute a the reduced cost of the edge.

                    target_bound = self.state.bound_of(prop_target)
                    cost = prop_weight

                    reduced_cost = cost + (curr_bound - target_bound)   # rcost(curr, tgt) = cost(curr, tgt) + val(curr) - val(tgt)
                    assert reduced_cost >= 0

                    reduced_dist = curr_rdist + reduced_cost    # rdist(orig, tgt) = dist(orig, tgt) + val(tgt) - val(orig)
                                                                #                  = dist(orig, curr) + cost(curr, tgt) + val(tgt) - val(orig)
                                                                #                  = [rdist(orig, curr) + val(orig) - val(curr)] + [rcost(curr, tgt) - val(tgt) + val(curr)] + val(tgt) - val(orig)
                                                                #                  = rdist(orig, curr) + rcost(curr, tgt)
                    dijkstra_state.enqueue(prop_target, Bound(reduced_dist), prop_id)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def _distances_from(self,
        origin: SignedVar,
        dijkstra_state: DiffReasoner.DijkstraState,
    ) -> None:
        """
        Computes the one-to-all shortest paths in an STN.
        The shortest paths are:
        - in the forward graph if the origin is the upper bound of a variable
        - in the backward graph is the origin is the lower bound of a variable
        
        The functions expects a `dijkstra_state` parameter that will be
        cleared and contains datastructures that will be used to compute the result.
        The distances will be set in the `distances` field of this state.
        
        The distances returned are in the BoundVal format, which is agnostic of whether
        we are computing backward or forward distances. The computed distance to a
        node `A` is simply the sum of the edge weights over the shortest path.
        
        Assumptions:

        The STN is consistent and fully propagated.
        
        Internals:
        
        To use Dijkstra's algorithm, we need to ensure that all edges are positive.
        We do this by using the reduced costs of the edges.
        Given a function `value(SignedVar)` that returns the
        current value of a variable bound, we define the *reduced distance*
        `red_dist` of a path `source -- dist --> target` as   
        - `red_dist = dist - value(target) + value(source)`
        - `dist = red_dist + value(target) - value(source)`
        If the STN is fully propagated and consistent, the
        reduced distance is guaranteed to always be positive.
        """

        origin_bound = self.state.bound_of(origin)

        dijkstra_state.clear()
        dijkstra_state.enqueue(origin, Bound(0), None)

        # Run Dijkstra until exhaustion to find all reachable nodes
        self._run_dijkstra(dijkstra_state, lambda _: False)

        # Convert all reduced distances to true distances.
        for (dist, curr_node) in dijkstra_state.reached_nodes():
            curr_bound = self.state.bound_of(curr_node)
            true_distance = dist + (curr_bound - origin_bound)
            dijkstra_state.distances[curr_node] = (Bound(true_distance), dijkstra_state.distances[curr_node][1])
            # FIXME line above: ugly...  direct modification of dijkstra_state.distances...
            # in the original, a pointer is used... but those don't exist in python :'(

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #