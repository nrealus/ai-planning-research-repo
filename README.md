# nrealus' AI Planning Research Repository

A long-term personal research project in AI planning and acting, which began in spring of 2020 (with a somewhat of a break in 2021-2022). This file is **WORK IN PROGRESS**, so there **will** be blanks, unclear wording, and other imperfections below.

## Introduction

The main aim of this long-term project is to build a system/architecture/framework for **integrated planning and acting** (aka integrated planning, execution, and monitoring) with a particular focus on the aspects of **time** and **uncertainty**. In the last few years, a lot of progress has been made on the integration of planning, execution, and monitoring. Also, the notions of time and uncertainty have been studied for a long time in planning, but only individually or in limited combination. Thus there's an **extremely exciting gap to fill** in combining advances on planning, acting (execution, monitoring...), time, and uncertainty. We believe that filling this gap will allow AI systems to tackle a very wide range of real-world problems in a general, comprehensive fashion.

In no particular order, here is a list of (possibly overlapping) general (high-level) features / deliberation capabilities that we would like to see combined (in theory, as it may be too ambitious in practice...):
- **A**: Hierarchical (aka refinement) and generative planning
- **B**: Temporal planning
- **C**: Numeric planning (resources support)
- **D**: Temporal and non temporal uncertainty (formalised in a probabilistic framework, for example bayesian networks) for "risk bounded" plans
- **E**: Integrated (interleaved) planning and acting (monitoring and execution)
- **F**: Online (reactive) plan repair / replanning
- **G**: Conditional / contingent planning
- **H**: Conformant planning or planning with incomplete knowledge or sensing capabilities
- **I**: Use of policies allowing to make planning and execution choices online, instead of plans with fixed choices
- **J**: Optimal (in terms of (maximal) expected utility) planning and execution (dispatching) choices of (temporal) plans (policies)

Also, there are two other important capabilities that we think a general system such as the one we envision should support. However, we defer them and **do not** consider addressing them, as we think they are quite independent (except maybe **L**) of the features from the list above:
- **K**: In addition to descriptive planning models, use of operational planning models as well.
- **L**: Partial observability (which we think is "fairly reframable" into full observability)
- **M**: Goal reasoning in the form of the following capabilities: addition, retraction, or modification of a (or set of) top level task/goal to pursue.

Again, note that many of the high-level features we listed **overlap** and **intertwine**, and so in our effort to combine them, we should not approach them all individually.

We believe that together, these features are enough (or even more than enough) to describe a very general (or at least autonomous) AI system, that should (in theory) be able to tackle a very wide variety of problems in a comprehensive fashion. Indeed, additional features (like motion planning, for example) could be integrated into such a system either natively or using some already supported features.

The combination of the features, even just from the first list, is an **extremely (perhaps overly) ambitious** research problem.

Here's a list of the sources which we're particularly inspired by, with an indication of the features (from the list above) for which we're inspired by it:
- [[1]]()
  - **A**, ...
- [[2]]()
  - **A**, ...
- [[3]]()
  - **A**, ...
- [[4]]()
  - **A**, ...
- [[5]]()
  - **A**, ...
- [[6]]()
  - **A**, ...
- [[7]]()
  - **A**, ...
- [[8]]()
  - **A**, ...
- [[9]]()
  - **A**, ...
- [[10]]()
  - **A**, ...
- [[11]]()
  - **A**, ...
- [[12]]()
  - **A**, ...
- [[13]]()
  - **A**, ...

## Research directions and ideas

The baseline for our work is the [Aries](https://github.com/plaans/aries) project. It is a hybrid CP/SAT solver aimed at tackling planning problems by encoding them into constraint satisfaction problems. Aries is able to address hierarchical temporal and numeric planning. A project developed alongside Aries is [SOMPAS](https://github.com/plaans/aries), which is an acting system inspired by RAE, and whose focus is on: guidance of online acting using continuous planning, resource management, and conversion of operational models (defined by a custom acting language) into (hierarchical) chronicles, which are (temporal) descriptive models used by Aries.

Uncertainty is the only important capability not addressed by these projects, which is understandable since it is very hard. Indeed, taking uncertainty into account leads to lots of intertwined questions and issues, affecting almost all aspects of planning and acting, and even the "philosophy" of what a planning and acting AI system should do. As such, uncertainty is almost always studied in very restricted settings, for example only temporal or non-temporal uncertainty. We want to address both!

To do that, we will actually have to design a new acting system, for which we already have some ideas that we will present below. But first, a few words about what kinds of uncertainty we want to address.

### Temporal uncertainty (planning aspect)

Temporal uncertainty is about contingent (aka uncontrollable) temporal variables (aka timepoints), which the system cannot control (i.e. cannot what value to set them / when to schedule them). Their scheduled time, set by Nature, can only be observed by us. Note that we assume full observability of contingent timepoints, because we think that the case of partial controllability can be reframed into full observability.

Temporal uncertainty is relevant and omnipresent in real-world problems, since in many cases we cannot predict when we will finish a certain action. We actually think that any contingent timepoint can be reframed as the end timepoint of task or action marked as contingent. To represent temporal information, we use temporal networks. Usually to adress uncertainty, Simple Temporal Networks with Uncertainty (STNU) are used. However, we're more interested in Probabilistic Simple Temporal Networks (PSTN) which extend STNUs with a probability distribution attached to contingent durations.

The main problem with temporal uncertainty is that depending on the outcome / scheduled time of a contingent timepoint, the temporal network (and by extension the plan) becomes inconsistent. To help with that, the notion of controllability is defined (strong, dynamic, weak). In practice, dynamic controllability is the most interesting, but also the most complex. When no indication is given, assume that we're meaning dynamic controllability. In the case of PSTNs, where probabilities are involved, the problem is not just to assess controllability. Some works opt to quantify it with a metric [X]. Another one [X] instead suggests to assess risk-bounded controllability.

The quanitification approach is interesting for online optimal execution / dispatching of temporal plans. However, for the planning part, we're more interested in the risk-bounded controllability assessment approach. Briefly, given a set of temporal chance constraints (difference constraints between two timepoints), the idea is to ensure that the network is indeed controllable with a probability "bounded" by a given "risk". In [X], this is done with a "risk allocation" approach, which reframes the PSTN into an STNU. Dynamic execution policies for PSTNs are also defined, extending those for STNUs. In our project, we want to allow the same chance constraints for temporal constraints in chronicles. We have actually already implemented (separately, in [this repository]()) the algorithm from [X], but with support for multiple joint chance constraints (instead of a single global one). Without the support for multiple joint chance constraints, which is (at least it seems so) absolutely required for our case, as we want to be able to define such chance constraints locally in chronicles (or rather chronicle templates).

However, it is important to keep in mind that what we described is irrelevant during the main CSP search / solving phase. Indeed, during the main search phase, it doesn't seem like there is much we can do to deal with temporal uncertainty, if we're using probabilistic durations / PSTNs. If we were using STNUs with set-bounded uncertainty, we could add a simple extension to the solver, to check whether the domain (interval) size for a contingent variable becomes smaller than the smallest contingent duration it participates (which would be a conflict). Also, still in the case of STNUs, the difference logic engine of the solver could be used to check for "pseudo-controllability", as not satisfying it would give an early indication of uncontrollability. But in our PSTN case, the only approach that we see for now is to defer the temporal uncertainty problem to the end of the solving. The steps would be the following:
-solve the planning problem as if there was no contingent timepoints (assume they're controllable)
-"lift back" the assignments to timepoints that the solver did (while keeping the assignments to non-temporal variables), obtaining a PSTN
-check risk-bounded / chance constrained dynamic controllability of that PSTN.

### Non temporal uncertainty (planning aspect)

Intuitively, we want to have contingent / uncontrollable / random non temporal variables in chronicles, with a bayesian network (or influence diagram) describing their conditional probability tables / trees. The motivation for that is that we want to be able to specify chance constraints in the chronicle's constraints and/or optimization of expected utilities / costs, instead of deterministic ones.

In the general case of stochastic constraint problems / programming, chance constraints can be very difficult to address. As such, we have thought about a few different possible directions to pursue.

- 1st direction. As we've said, in the general case chance constraints are difficult to address directly and efficiently at the same time. To avoid these difficulties another approach is often used instead: "penalty" functions or terms are incorporated into utilities/costs, which leads us to a problem of expected utility optimization without chance constraints. Or rather, in our case, satisfaction of a lower bound for an expected utility. This direction is motivated by the fact that expected utility optimization is far more common in stochastic constraint literature, and by the fact that the Aries project supports (deterministic) metrics (i.e. utilities/costs) attached to chronicles (with the aim of optimizing the total metric of solutions). Adapting this to the probabilistic framework appears to be possible. We have thought about several possibly complimentary avenues for that.
  - In the worst / most naive case, this could be done by relying on approaches based on sampling (hindisght optimization, SAA (MCTS...?), Evaluate & Cut (possibly with scenario grouping and/or sampling)...?). This type of approaches would also be motivated by the fact that in the deterministic cases, continuous planning can already be used to help acting.
  - And/or branch and bound search [X]. However, we are worried that "forking" the search algorithm on AND nodes could be very detrimental. But who knows, it might not be that bad in practice. Moreover, we could always resort to halting the search preemptively if we think that we are at a good enough level of (bounds, in our Aries-like case) consistency.
  - Numeric functions (linear sums in Aries) approximating cumulative distributions of random variables present in utility functions, and "standard" / deterministic solving (setting literals on bounds) ? This would bear some similarity to the risk allocation approach for temporal uncertainty.
  - Extensions taking into account (approximated) cumulative probability to filtering / (bounds) consistency based approaches
  - ...?

It is also worth noting that the 2 last avenues could also be applied to the "direct" approach to chance constraints (not through reframing into expected utility optimization / lower bound guarantee).

### Mixed temporal & non temporal uncertainty

We haven't thought this a lot for now, but we believe it may be possible to make our approaches for temporal and non temporal uncertainty "collaborate".

### Acting

To our knowledge, there no actors yet that are able to support temporal and non-temporal uncertainty in an online, interleaved planning and acting setting. Indeed, the notions of policies, temporal plans, and contingent plans, can be difficult to stitch together. Indeed, for now the only "unified" mathematical framework for this would be that of POMDPs, which are very often computationally intractable.

First, we would like to note that despite its age, the work of Bidot [...] is very enlightening for us. Almost all actors / acting systems that we encountered could indeed be seen as concrete instantiations of the general framework he described. As such, his work is very interesting to us as it may help to find a common ground between acting capabilities that couldn't be combined in a principled manner yet.

In our effort, we are by the general framework of Bidot for stochasting scheduling [...], FAPE (the skill handlers system in particular) [...], RAE & UPOM [...] (and SOMPAS [...] which can be seen as their extension), Riker [...], Lila [...], and Restricted Time-Based Dynamic Controllability (R-TDC) strategies of Osanlou [...]. The general idea is to for acting to perform continuous "growth" / lookahead (or "refineahead" as in [...]) of a policy tree (or, perhaps in the far future, decision diagram) adapted from R-TDC strategies/policies. The main extension to R-TDC strategies would be in the "reactive strategies" that can be launched during "wait" periods (see [...]). The "basic" reactive stratgies in [...] are a mapping from contingent timepoints that may happen during the wait to controllable timepoints which should be reactively scheduled at the same time as the contingent timepoints are executed/observed. We could also consider observations of non-temporal exogenous changes with those reactive strategies, and map them to "Add\Del" operations on the current chronicle network (corresponding to the current node in the policy). Indeed, instead of associating policy nodes to temporal networks as in [...], we could do that for chronicle networks (i.e. the "plans"), attached with 1. a table or "acting process tree" (like in SOMPAS), specifying the remaining known allowable instantiations for (non-temporal) variables, and 2. the (risk-bounded) PSTN at the current state of execution. With such an approach, we believe it may be possible to take the best of both worlds from "policy" and "plan" representations (such as chronicles), allowing for reactive replanning / plan repair, looking ahead / planning proactively, and making online (possibly (approximately) optimal) choices during execution, while taking temporal and non-temporal uncertainty into account.

...
