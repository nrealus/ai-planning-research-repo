# nrealus' AI Planning Research Repository


A long-term personal research project in AI planning and acting, which began in spring of 2020 (with a somewhat of a break in 2021-2022).

Documentation (**WIP**) is available [here](https://nrealus.github.io/ai-planning-research-repo/).

The following is **WIP** and is subject to change. Blanks, unclear wording and other imperfections are to be expected.


# Introduction


The main aim of this long-term project is to build a system / architecture / framework for **integrated planning and acting** (aka integrated planning, execution, and monitoring) with a particular focus on the aspects of **time** and **uncertainty**. In the last few years, a lot of progress has been made on the integration of planning, execution, and monitoring. The notions of time and uncertainty have also been studied for a long time in planning, but often only individually or in limited combination. Thus there's an **extremely exciting gap to fill** in combining advances on (online) planning, (online) acting, time, and uncertainty. We believe that filling this gap is very important to take AI systems to the next level, allowing them to tackle a very wide range of real-world problems in a general, comprehensive fashion.

In no particular order, here is a list of **possibly overlapping**, general, high level deliberation capabilities / features that we would like to see combined (in theory, as it may be too ambitious in practice...):
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

Also, there are two other important aspects that we think a general system such as the one we envision should support. However, we defer them and **do not** plan to address them yet, as we think they are quite independent (except maybe **L**) of the features from the list above:
- **K**: In addition to descriptive planning models, use of operational planning models as well.
- **L**: Partial observability (which may be reframable into full observability, at least partially)
- **M**: Goal reasoning in the form of the following capabilities: addition, retraction, or modification of a (or set of) top level task/goal to pursue.

Again, note that many of the high level features we listed overlap and intertwine, and so in our effort to combine them, we should not approach them all individually.

We believe that together, these features are enough (or even more than enough) to describe a very general AI system that should (in theory) be able to tackle a very wide variety of problems in a comprehensive fashion, while still remaining extendable.

The combination of the features, even just from the first list, is an **extremely (perhaps overly) ambitious** research problem.

Here's a list (in no particular order) of the sources which we're particularly inspired by, with an indication of the features (from the list above) for which we're inspired by it:
- [[1]: S.Levine. Risk-bounded Coordination of Human-Robot Teams through Concurrent Intent Recognition and Adaptation]()
  - **E**, **G**, **H**, **I**, **J**, **D**
- [[2]: A.J.Wang. Risk-Bounded Dynamic Scheduling of Temporal Plans]()
  - **D**, **I**
- [[3]: K.Osanlou. Solving Disjunctive Temporal Networks with Uncertainty under Restricted Time-Based Controllability Using Tree Search and Graph Neural Networks]()
  - **I**
- [[4]: M.Saint-Guillain. Lila: Optimal Dispatching in Probabilistic Temporal Networks using Monte Carlo Tree Search]()
  - **I**, **J**, **G**
- [[5]: A.Bit-Monnot. FAPE: MODELES TEMPORELS ET HIERARCHIQUES POUR LA PLANIFICATION ET L'ACTION EN ROBOTIQUE]()
  - **A**, **B**, **F**, **E**, **L**
- [[6]: R.Godet. Chronicles for Representing Hierarchical Planning Problems with Time]()
  - **A**, **B**, **C**
- [[7]: J.Turi. Enhancing Operational Deliberation in a Refinement Acting Engine with Continuous Planning]()
  - **A**, **E**, **F**, **K**
- [[8] S.Patra. Deliberative Acting, Online Planning and Learning with Hierarchical Operational Models]()
  - **E**, **F**, **J**, **K**
- [[9] A.Bit-Monnot. Enhancing Hybrid CP-SAT Search for Disjunctive Scheduling]()
  - ...
- [[10]]()
  - ...
- [[11]]()
  - ...
- [[12]]()
  - ...
- [[13]]()
  - ...


# Research directions and ideas


The baseline for our work is the [Aries](https://github.com/plaans/aries) project [9]. It is a hybrid CP/SAT solver aimed at tackling planning problems by encoding them into constraint satisfaction problems. Aries is able to address hierarchical temporal and numeric planning. A project developed alongside Aries is [SOMPAS](https://github.com/plaans/aries) [7], which is an acting system inspired by RAE [8], and whose focus are: guidance of online acting using continuous planning, resource management, and conversion of operational models (defined by a custom acting language) into (hierarchical) chronicles [6], which are (temporal) descriptive models used by Aries.

Uncertainty is the only important capability not addressed by these projects, which is understandable since it is very hard. Indeed, taking uncertainty into account leads to lots of intertwined questions and issues, affecting almost all aspects of planning and acting, and even the "philosophy" of what a planning and acting AI system should do. As such, uncertainty is almost always studied in very restricted settings, for example only temporal or non-temporal uncertainty. We want to address both!


## Temporal uncertainty (planning aspect)


Temporal uncertainty is about contingent (aka uncontrollable, aka random) temporal variables (aka timepoints), which the system cannot control: it cannot set their value (i.e. schedule a time for their execution). Indeed their schedule time is set by Nature and can only be observed by us. Note that (for now) we assume full observability of contingent timepoints, as we think the case of partial controllability can largely (but maybe not completely) be reframed into full observability.

Temporal uncertainty is relevant and omnipresent in real-world problems, since in many cases we cannot predict when we will finish a certain action. To represent temporal information, we use temporal networks. Usually to adress uncertainty, Simple Temporal Networks with Uncertainty (STNU) are used. However, we're more interested in Probabilistic Simple Temporal Networks (PSTN) which extend STNUs with a probability distribution attached to contingent durations.

The main problem with temporal uncertainty is that depending on the outcome / scheduled / executed time of a contingent timepoint, the temporal network (and by extension the plan) can become inconsistent. To deal with that, the notion of controllability is defined (strong, dynamic, weak). In practice, dynamic controllability is the most interesting, but also the most complex. When no specific indication is given, assume that we're talking about dynamic controllability. In the case of PSTNs, where probabilities are involved, the problem is not just to assess controllability. Some works opt to quantify it with a metric [4]. Another one [2] instead suggests to assess "risk bounded" controllability.

The 1st approach is interesting for online optimal execution / dispatching of temporal plans. However, for the planning part, we're more interested in the 2nd approach (risk bounded controllability assessment). Briefly, given a set of "requirements" (which must be differentiated from "activities"!) of the PSTN, a temporal chance constraint can be defined. The idea then is to ensure that the network is indeed controllable with a probability "bounded" by a given "risk". In [2], this is done with a "risk allocation" approach, where the goal is to find bounds for the duration of probabilistic durations, which yield a dynamically controllable STNU, when replaced in the PSTN. Dynamic execution policies for PSTNs are also defined, extending those for STNUs.

In our project, we want to allow specifying similar "temporal chance constraints" (or "temporal chance specifications"?) on chronicles. As a first step for that, we have implemented the algorithm from [2], but with 1 notable extension: support for multiple joint chance constraints (instead of a single global one), following the insights given in chapter 8 of [2]. Without the support for multiple joint chance constraints, it wouldn't be possible to extend this approach to our case, as we'd need to define such chance constraints locally in chronicles (or rather chronicle templates). Our motivation is to require solutions to planning problems to guarantee that certain parts of it can fail / become inconsistent with a probability lower than a certain "risk" threshold.

What we described is relevant for planning (i.e. solving / search phase of the CSP into which the planning problem is converted). Now, how can we integrate these "risk bounds" on temporal uncertainty to it ? We're still exploring this, but the current main idea is the following:
- simply perform "normal" (deterministic) CSP solving, ignoring anything related to uncertainty
- once such a "uncertainty-relaxed" solution is found, "lift back" the assignments to temporal values: this will yield a PSTN that we can tackle with the approach of [2].
- if the result is successful, great.
- if it isn't, the "dynamic controllability conflicts" (which are disjunctive linear constraints) returned by the algorithm can be reinjected into the CSP.

This idea is fairly simple, which is a good thing. However we're not sure how efficient Aries is at dealing with linear (pseudo-boolean?) constraints. Maybe it is unrecommended to have a large amount of linear constraints... Another idea could be to extend the algorithm from [2] to support "PSTNs with choices". The same authors had already worked on problems where a problems with possible "choices" (cc-CCTPU ?) were addressed (BCDR algorithm). It could also be interesting to try integrating the algorithm from [2] a bit more deeply into Aries, and try to take advantadge of its native support of optional variables (through "presence" variables/literals).

We also have some other ideas, but they're more suited for the STNU case, and it isn't clear to us yet how they could be adapted to PSTNs. Indeed, if we were in the STNU setting ("set bounded", not probabilistic uncertain durations), it could be possible to indicate to the CSP solver to not choose contingent random / variables during its decision phase (at least before all other variables have been set?), and to check whether (as a result of propagation) the domain size (interval) fo a contingent variable becomes smaller that the biggest contingent duration it participates it. This could be an extended "InvalidBoundUpdate" conflict in Aries. Another idea (still in STNU setting) could be to enhave the difference logic engine of the solver to check for "pseudo-controllability" during search, as not satisfying it would give an early indication of uncontrollability.

There is also one accept that we haven't investigated yet, and hope that it's not going to introduce too much complexity. It's the possibility of specifying durations to be equal to a some function (for example, representing a duration, whose value may be calculated by some external module (?)). What impact would it have on our approach if this is done for controllable durations ? What would it be if it was done for uncontrollable durations (would we need to, for example, use conditional probabilities in our [2]-inspired algorithm ? and if so, would it even work ?)


## Non temporal uncertainty (planning aspect)


"Non-temporal" uncertainty can actually be very broadly interpreted. Usually in planning, it is understood as a setting in which action effects are probabilistic or non deterministic. Depending on whether these effects are observable (as well as other complicated stuff), there can be several problems of interest. The most intuitive to imagine is the problem of finding a plan that whose execution is most likely to succeed.

However, we are interested in a richer setting. Our motivation has two axes:
- Similarly to the case for temporal uncertainty, allow constraining the sought solutions of a planning problem to satisfy "local" specification related to uncertainty. In other words, we want to be able to restrict solutions to our planning problem to satisfy certain constraints with a certain level of confidence (or, similarly a certain allowed level of risk - this distinction between risk and confidence is similar to that for temporal uncertainty in [2]).
- Have stochastic / probabilsitic cost / utility functions for the chronicle, and seek to optimize (or guarantee a lower bound for) its expected utility.

Below, we focus on the 1st axis.

As such, in our proposed setting, we suggest to allow chronicles to have random / uncontrollable / contingent variables, with the possibility of specifying probability distributions (possibly in the form of conditional probability tables / trees / Bayesian networks / influence diagrams) in the "constraints" **(!)** of a chronicle (set `X` in [6]). This allows to specify "probabilistic effects" simply by setting a such a random variable to be the "value" of an "effect" of the chronicle. Moreover, if we want "probabilistic effects" to be "structurally" different, we can use "subtasks" of the chronicle instead, with refinement methods / chronicles for that subtasks containing describing those effects. These refinement methods / chronicles would be specified with "preference weights" reflecting the probabilities. Finally, similarly to the "temporal requirements chance constraints" from above, we suggest to attach a threshold value to subsets of "conditions" or "subtasks" of a chronicle. The meaning is that we want to require the instantiation (for the decision / non random variables) of the chronicle in the solution to be such that the probability of these conditions being unsatisfied and these tasks being failed / inconsistent / incorrect must be less than the specified "risk" threshold. (or alternatively, the probability for satisfaction / success to be greater than a "confidence" threshold). We think that the specification on a subtask should be interpreted as "all conditions of the refinement chronicle / method for that subtask". As such, our suggestion boils down to "chance specifications" on conditions of chronicles.

We think that these specifications should be interepreted as chance constraints for the CSP into which the planning problem has been encoded. These chance constraints would have the following form: "probability of the negation of the conjunction of the 'supported' constraints for these conditions must be lower than the 'risk'" (or alternative with 'confidence' instead of 'risk').

And now, to the complicated part: how can we deal with such chance constraints ??? Indeed, we now have a stochastic constraint satisfaction problem, and chance constraints are notoriously hard to address... They are even often left out in the stochastic constraint satisfaction literature because of that, and expected utility optimization is addressed more often. However, it would seem that chance constraints like these could "translated" into utility / cost / penalty function, which perhaps could make things easier for us (or not). Nevertheless, here are our ideas on how to tackle this:
- Assuming we can reframe the chance constraint into an expected utility optimization / bound satisfaction problem, we could address it with a variety of approaches:
  - Approaches based on sampling (hindisght optimization, SAA (MCTS...?), Evaluate & Cut (possibly with scenario grouping and/or sampling)...?).
  - And/or branch and bound search [X]. However, we are worried that "forking" the search algorithm on AND nodes (corresponding to different possible values for random variables) could be very detrimental. But who knows, it might not be that bad in practice. Moreover, we could always resort to halting the search preemptively if we think that we are at a good enough level of (bounds, in our Aries-like case) consistency.
  - Numeric functions (linear sums in Aries) approximating cumulative distributions of random variables present in utility functions, and "standard" / deterministic solving (setting literals on bounds) ? This would bear some similarity to the risk allocation approach for temporal uncertainty.
  - Extensions taking into account (approximated) cumulative probability to filtering / (bounds) consistency based approaches
  - Encoding a bayesian network into a pseudo boolean numeric function, which Aries could address ? [i]
- Addressing the chance constraints directly, without resorting to reformulation into an expected utility optimization / bound satisfaction problem:
  - The 2 cases from the list above: indeed, they could be applicable for this case too
  - Studying the "support" constraints in more detail, and maybe (since they're highly structured) derive a special filtering algorithm for bounds consistency ?
    - We could take advantadge of some of the algorithms we found for "stochastic arc consistency" (?) / filtering algorithms for stochastic global constraints.

Finally, another important issue is that the order in which we consider the variables / parameters in the "support" constraints is important, because it impacts the probability and the way we compute it. Moreover, during online execution, these variables / parameter may not all be set yet, and in theory, a value could be given to them (either by assignment or observation) in any order...! For this whole problem, we probably should take inspiration from [1], and define some sort of "worst case" order for variables. A "Weight Model Counting"-inspired approach (like in [1]) could also be of interest...

Final important note !! In Aries, chronicle "conditions" defined on "resource" are encoded not with "support" constraints, but with special "resource" constraints. We haven't really looked at them yet, but know that they are basically encoded as a series of linear (pseudo-boolean? need to check) constraints.
We should look into them to check that our reasoning can still apply to them.

[[i]](https://dilkas.github.io/pdf/cw.pdf)

### UPDATE (04/11/23)

After thinking again, we came to the conclusion that "chance specifications" (or "risk specifications" as we want to call them now to avoid confusion with "actual" chance constraints) should be extended to all types of elements of a chronicle, so not only conditions and subtasks, but also effects, and maybe even constraints from X too. So we make an attempt at (sort of) formalizing them.

In addition to its sets V, X, C, E, S, a chronicle should also come with a set R (for "risk"). The elements of R should be tuples (K, Delta) where Delta is a real (actual fractionary/rational/fixed point) value in [0,1], and K is a set of elements from C, E, S, and X (not yet sure about X). We call these elements of R "risk specifications" of the chronicle. It should be interpreted as a chance constraint for the CSP into which the planning problem is encoded: P(!coherent(eff, eff') for all effect eff in R (and any eff' != eff), !supported(cond) for all conditions cond in R, [? !cstr for all constraints cstr in R ?], all effects, constraints, and conditions of the refinement chronicle that will be chosen for subtasks in R) <= Delta

Such chance constraints will be way too complex to deal with. And even though some of the ideas from above may still be relevant (approaches based on sampling...), we actually want to take a slightly different approach than that which we initially wanted. The idea is to follow the same approach as in [2] for risk bounded dynamic controllability of PSTNs, i.e. a risk allocation approach. In this setting, our goal will be to set bounds on random / contingent / uncontrollable variables such that we know that the constraints (including chance constraints) hold for them, and such that the total probability mass outside of these bounds is less than Delta. This approach is interesting because it seems like it may lead us to a simplified problem, and because it may be interesting for the acting part, as we could make use of the risk allocations to make some acting decisions when observing that some random variables outcomes don't fall into the bounds that were allocated for it. By "acting decisions" here we mean applying some sort of reactive dispatching or instantiation, plan repairing, or searching for new planning solutions with specific assumptions. (see below for notes on acting)

But how could we make this work ? The simplest approach would be to defer this risk allocation step to the very end of the solving, just as we considered doing with for temporal uncertainty. Another more exciting idea would be try integrating it into the solver, possibly through a new "probabilistic" reasoner. Its purpose would be to propagate updates/events to the chance constraints, when an event/update modifies the domain of a variable from a chance constraint. But how exactly would that work ? Our current idea is to "watch" the Fréchet bounds for the chance constraints' probabilities, as well as the probabilities corresponding to the cumulative probability mass for the literals appearing in them. Indeed, we think that there's something interesting to be done with bound literals and cumulative probability masses. By the way, these cumulative probability masses would (hopefully?) be easily obtainable from conditional probability tables / trees / bayesian networks / influence diagrams attached to the chronicles. Also, we are motivated by the fact that there seems to already be support for max / min / sum constraints in Aries, because Fréchet bounds use max and min

Also, all of this begs another question: could this be "unified" with the approach for temporal uncertainty ?


### On the interactions between temporal and non temporal uncertainty (planning aspect)


A priori, we have a feeling that it should be possible to consider these temporal and non temporal "chance specifications" independently. However, support constraints have 2 temporal ordering constraints in them ! So we should think about whether the temporal chance specifications would be affected by it... A priori, we think that there shouldn't be too much trouble because of this, but we should still be careful.


## Acting (and acting aspects of temporal and non temporal uncertainty)


To our knowledge, there no actors yet that are able to support temporal and non-temporal uncertainty in an online, interleaved planning and acting setting. Indeed, the notions of policies, temporal plans, and contingent plans, can be difficult to stitch together. Indeed, for now the only "unified" mathematical framework for this would be that of POMDPs, which unfortunately are often intractable because of huge state or action spaces.

We also want to point out that in acting, the interest in uncertainty is a bit different than in planning. As we saw above, our interest in planning is to ensure that solutions satisfy some chance constraints of "chance specifications". In acting, we want our dispatching / execution choices be optimal, in the sense that we want them to be as likely to end succesfully as we can. This corresponds to following the maximum expected utility principle. So in other words, during acting, online, we want to make execution decisions that are the most likely to a higher value for the utility of the final "history" (i.e. "past" plan, i.e. "history" chronicle). In order to enable such online deliberation, allowing to make "the best" (both temporal and non temporal) choices on the fly, we are interested in a "policy-like" representation for our actor.

Before continuing further, we would like to note that despite its age, the work of Bidot [...] is very enlightening for us. Almost all actors / acting systems that we encountered could indeed be seen as concrete instantiations of the general framework he described. As such, his work is very interesting to us as it may help to find a common ground between acting capabilities that couldn't be combined in a principled manner yet.

In our effort, we are inspired by the general framework of Bidot for stochasting scheduling [...], FAPE (the skill handlers system in particular) [...], RAE & UPOM [...] (and SOMPAS [...] which can be seen as their extension), Riker [...], Lila [...], and Restricted Time-Based Dynamic Controllability (R-TDC) strategies of Osanlou [...].

Our general idea is to try and "stitch together" a "policy" tree inspired by the tree-like R-TDC strategies of Osanlou [...], the general acting loop with possible revision / reactive replanning / plan repair, as well as the use of "skill handlers" from FAPE [...], the continuous planning approach of SOMPAS to continuously "grow" the set of known possible solutions / choices [...], and the "lookahead" from RAE+UPOM [...] or Lila [...].

We think that we could extend the tree in [...] in several ways. First, instead of DTNUs, nodes should "contain" the current "plan belief" (i.e. current allowed values for planning problems, which map to instantiated plans i.e. "chronicle networks"). Second, outgoing edges from "d-OR" nodes should also be able to set non temporal (controllable/decision) variables (including presence variables and parameters of chronicles), not only schedule (controllable) timepoints (at the current time). Third, "reactive strategies" and "AND" should be extended to take into account observations (of a value for a certain variable) and "plan updates" that may happen during the wait period. More generally, maybe we could define "reactive strategies" as mappings from observations (and plan updates?) to "\ Del U Add" operations on chronicles, by analogy with the "reactive strategies" in the paper (mapping from sets of uncontrollable timepoints to controllable timepoints to schedule at the same time, if these uncontrollable timepoints were to be observed during the wait). Plan repair / replanning could be integrated as either a special type of reactive strategy, or a special type of outgoing edge from "d-OR" nodes.

Additionally, we would need to think about how to tie "continuous planning" into this: how can we make the planner and actor interact in this setting ? A priori, nodes of the "policy" tree should also contain a data structure holding the (remaining) possible instantiations for (non temporal) variables. These correspond to solution that have been found by the planner per continuous planning. In SOMPAS, the "acting tree" is such a structure. Would it be possible "interalize" nodes of our "policy" tree with "acting trees" from SOMPAS (or something similar) ?

Another issue is "how to choose the best decisions to take" ? We may run MCTS or some kind of sampling approach over the "policy" tree. Techniques mentioned above in the paragraph about non temporal uncertainty could be applicable to this problem as well.

Also, do we need to maintain and update probabilistic knowledge online ? If so, can we do it (efficiently) ? And even if we can, won't the price of "converting" to more efficient forms / structures be worth it ?

Is there a way to avoid the "policy" tree from growing too large ? Is it possible to leverage ideas from decision diagrams ? Perhaps adapt BDDs to use bounds on literals instead of 0/1 values ? And even if it was possible, would it be worth it ?

Do we need an "order" in which to consider variables ? As it might be impactful for efficiency, for example for probabilistic knowledge representation and manipulation. Or maybe it may be useful as a "pessimistic"/"conservative" order in which we should constrain the actor to make decisions, to avoid the tree from getting too large because of "redundant" nodes / exploration ?. In case this issue ends up being relevant, we think that a good idea would be the following: order presence variables by the order of their earliest possible start time ; then, right after each presence variable, place the variables appearing in that chronicle, in the order of the earliest possible start time of the condition/effect/subtask they're involved in, and in case of ambiguity with the controllable variables before uncontrollable ones.

Anyway, despite the fact that our general idea is still very crude, we believe that it may guide us (if we're lucky...) to an online acting architecture combining "proactive", "revision", and "progressive" approaches (as per the terminology of Bidot [...]) with support for complex temporal, numerical, and uncertainty specifications.


## ...