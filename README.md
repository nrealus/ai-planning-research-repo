# nrealus' AI Planning Research Repository


## **UPDATE: 13/04/2024** ##

**This repository is now discontinued / unmaintained, because I started a PhD on this same subject (AI planning)! As such, working on this repository has not only been very fun and interesting, but also very useful for my career!**

**The notes below are now old (10/2023) - and still very messy - but they may still be of interest and use for the future, as a possible source of inspiration.**

##

A long-term personal research project in AI planning and acting, which began in spring of 2020 (with a somewhat of a break in 2021-2022).

Documentation (**WIP**) is available [here](https://nrealus.github.io/ai-planning-research-repo/).

The following is **WIP** and is subject to change. Blanks, unclear wording and other imperfections are to be expected.


**General objective**: Integrated planning and acting with rich support for uncertainty, both temporal and non-temporal.

**Current general ideas**:

- Uncertainty specifications / representation / modelling:

  - Allow chronicles to define uncontrollable variables and chance constraints

    - Specify conditional probability distributions (depending on values both uncontrollable and controllable variables) through an influence diagram (without utility nodes, for now at least) attached to the chronicle. The influence diagram could be either denoted as `I` or considered to be implicitly part of `V`

      - This means that state variables become probabilistic as well: could be useful to compute and attach to each of them a joint probability distribution (possibly conditionally to controllable variable parameters) for their possible parametrisations

      - Uncontrollable durations / temporal constraints should be defined as `t_e - t_s = dur` where `dur` is an uncontrollable variable appearing in the influence diagram (possibly conditionned on other variables), and `t_s` and `t_e` are controllable (even though `t_e` isn't *really* controllable)

      - The (numeric) "cost" of a chronicle becomes probabilistic as well
        - Need to think more about what that means how we could deal with it - couldn't we just consider a determinstic cost, which would be the expectation of the probabilistic one ?
    
    - Specify a set `R` of chance constraints attached to the chronicle

      - We will also call them "risk specifications", to avoid using the word "constraint" too often

      - The set `X` would now be the set of "hard constraints", instead of simply "constraints"

      - A risk specification (i.e. chance constraint) would be a tuple `(RR, risk)`. `RR` would be a set of constraints OR chronicle conditions (set `C`), and `risk` would be a value indicating the maximum tolerated probability for the (conjunction of) constraints `RR` to not hold.
        - The chronicle conditions would be implicitly interpreted as their `supported` constraints.

  - However, I don't really know how (and even if...) similar uncertainty specifications could be integrated in a operational model / acting language like that of SOMPAS.
    - Maybe extending some primitives like "exec" with a value describing the acceptable failure risk of the task ?
      - But what about other acting primitives ?
    - This could be very important... but I'm not sure how to tackle this (I'm bad with formal languages)

- Uncertainty (planning aspect)

  - With the uncertainty specifications described above, the goal of planning becomes more complex. The idea is that we want solutions to controllable variables such that the risk specifications are satisfied.

  - This makes everything much, **MUCH** more difficult. The issues of dynamic controllability (alternatively, dynamic consistency) become more complex than in the case of purely temporal uncertainty. Also, the notion of risk awareness (chance constraints / risk specifications) adds a supplementary layer of complexity...

  - We suggest to take inspiration from Risk Allocation approaches ([?], [?], [?], ...)
    
    - The idea is to "allocate the risk budget" by searching for some lower and upper bounds in the domains of uncontrollable variables, such that:
      1. the constraints from each risk specification are satisfied when uncontrollable variables' values are all within those bounds
      2. the total probability mass outside of these bounds is less than the risk value of each risk specification
    
    - This is done by reformulating the risk specifications / chance constraints into a "reformulated chance constraint". This "reformulated chance constraint" is a sum of probability masses (in the literature, a simple upper bound of the actual probability (Boole inequality))
      - It uses the cumulative distribution function, making it non linear. However, we can linearize or even discretize it.
      - We could bridge the gap with the "optional variables" of our Aries-like framework by making the reformulated chance constraint pseudo-boolean

    - There is also some literature on risk aware probabilistic planning / risk aware chance constrained POMDPs / the RAO* algorithm, ([?], [?], [?], ...) which could be interesting to investigate. We could adapt some aspects, for example by considering the states of the MDPs to assignments to all variables, and actions to be instantiations of controllable variables
 
    - Our main inspiration is the PSTN risk-aware dynamic controllability work of Wang [?]. However, it addresses only temporal uncertainty, so more work is needed to adapt it.
      - Also, what Wang left for future work (chapter 8 of [?]) could be very precious to us (like incrementality, optimization, and multiple chance constraints).
        - The support for multiple chance constraints is actually **indispensable**, because even with one risk specification per chronicle, their conjunction yields multiple risk specifications (aka chance constraints).
          - The key is determining which uncontrollable variables are "relevant" for the risk specification. In our implementation of Wang's algorithm, we made multiple chance constraints work (at least we think so...) based on Wang's insights in chapter 8. But adapting that to the context of planning with chronicles (with an Aries-like solver) won't be trivial, because of optional variables...

    - At the same time, the work of Cui [?] deals with dynamic controllability of CCTPUs (with some conservative assumptions which we actually consider reasonable). Its foundations are shared with the work of Wang. However, there is no probabilities nor risk, and choices / non-temporal variables are all controllable there.

      - There is also a simpler approach, which would be to have dynamic controllability on the temporal aspect, but "only" strong consistency for the non-temporal aspect, as is done in another line of work on CCTPUs ([?], [?], [?], ...)

    - As such, we should investigate the algorithm of Cui and see if we could adapt it to handle:
      1. uncontrollable choice variables (which would make the search space be "AND/OR", instead of just "OR"...)
         - adapt with some sort of (stochastic) local search ? determinization, sampling (hindsight optimization?) ? maybe even take inspiration from (R)AO* ? 
      2. risk allocation
          - it won't be enough to run Wang's algorithm at the leaves of the tree, as that would account for risk allocation of only temporal uncontrollable variables.
            - some sort of "two-stage" approach, with 1st stage corresponding to non-temporal uncontrollable variables, and the 2nd stage corresponding to temporal ones ? 

    - It could also be very interesting to consider using some form of decision diagram instead of tree, as it is very likely that a large part of the leaf temporal problems / networks will be the same

    - Let's also mention the original work of Tsamardinos [?] on CTPs, where we could look for insights on the early approaches to dynamic consistency

    - In everything discussed above, we assume that the Aries-like solver is used in an "uncertainty-relaxed" way (i.e. considering uncontrollable variables to be controllable). Everything we discussed above was considered to be performed on a "uncertainty-relaxed" solution given by the solver, where we then "lift" this relaxation, leading us to a new problem aimed at risk-aware controllability checking
      - In other words, the solver would be used to give initial candidate solutions to an algorithm which would be responsible of checking risk-aware dynamic controllability.
      - If we were to adapt the work of Cui, we would even need to have multiple "initial" candidate solutions. This is why we suggested some sort of local search to deal with the "AND/OR" search space which we would have when considering uncontrollable choice variables.
        - The "local search" ideas actually remind us of the "anytime bdd construction" of Levine. Indeed, just like in his case, our search space may be very big, so we are very interested in an anytime approach. Which seems to be quite compatible with "local search - like" approaches we had in mind (because of the "iterated" consideration of fully instantiated candidate solutions)
          - One idea for this local search could be to count the probability mass of infeasible candidate solutions obtained by switching values for uncontrollable variables. If the total probability mass for all of these exceeds a risk value, then the cocntrollable variables assignment doesn't satisfy a risk specification, and thus is bad
            - ...isn't this just... the same as forward checking for stochastic constraint satisfaction problems ?!
          - Another idea could be to alternate between neighborhoods for controllable and uncontrollable variables (i.e, look for candidates by changing values for uncontrollable variables, until the candidate is infeasible, then take a new candidate by changing values for a controllable variables). (Idk yet how exactly this could be useful, but I'm still writing it down to remember it).

    - However, we could also extend the solver with new reasoners (or "sub-reasoners"?), aimed at detecting bad cases early, in a non-complete fashion.
      - The simplest would be to catch as conflicts cases when propagation makes domains of uncontrollable variables smaller than the "largest" constraint they participate in
      - It could also be interesting to adapt an incremental (temporal) dynamic controllability algorithm for STNUs (however it becomes unclear how we would deal with probabilities and risk, then) as a "sub-reasoner" of the difference logic reasoner.
        - However, there would have to be some black magic to support optionals... Maybe we could take inspiration from the CSTNU propagation rules... (even though they're complex and the CSTNU DC-checking algorithms are exponential and far from ready in "practical" use) or make some (acceptable) assumptions like those of Cui
      - A "probabilistic reasoner" was also among our ideas. We could take advantadge of the fact that our literals are "bound literals" and cumulative distribution functions are monotonous (and therefore bijective) to attach variables with a new variable or literal representing the probability mass for their current bounds

- Uncertainty (acting aspect):

  - The actor must be able to make choices that must be:
    1. made online (i.e. during execution)
    2. non-temporal
       - i.e. "online refinement" - choice of refinement chronicle to use, and instantiation (choice of value) for its controllable parameters
    3. temporal
       - i.e. dispatching, with possibilitiy of defering the instantiation of an enabled/alive controllable timepoint
    4. (approximately) "optimal" with regards to a metric
       - notably the expected utility of "success" (i.e. consistency of the final history that may be obtained as a result of the choices)
    5. make the choices based on lookahead (see 1. and 4.) while allowing for plan repair and replanning
       - this would allow the combination of proactive, reactive, and progressive acting capabilities (as per the terminology of Bidot [?])

  - In a nutshell, what we're describing is a "super-eRAE" actor

  - Our current idea is to have a structure containing solutions given by the planner (after processing by a risk-awareness controllability checker? see above) - like the Acting Tree in SOMPAS - which could be seen as an "oracle".
    - it would be updated after execution choices / dispatching is made, or after receiving observations of the environment, or after receives updates from "skill handlers"
      - Notably, probabilistic knowledge would thus also be updated by "filtering" conditional probability "rows" in the influence diagrams of the solutions' chronicle instances

  - The structure in which lookahead would be performed is inspired by Lila [?] and R-TDC strategies [?]. The actor would be exploring a tree of possibles choices, possibly up until a certain horizon, 

  - The acting would consist of performing lookahead in a tree of choices, like those of R-TDC [?] - which discretized time and "wait" actions / choices. The available choices in this tree would be those exposed by the "oracle" (see above). The exploration could be done with some form of MCTS.
    - Alternatively, the nodes of the tree could correspond to "plan beliefs", i.e. chronicles. The "edges" of the tree could then correspond to (. \ Del) U Add operations on the parent chronicle.

  - The notion of "reactive strategies" from [?] could be kept as well, and even extended to non-temporal uncontrollable variables, and even "preemptive" planning for some conditions that may happen in the future, or simply replanning / repair on the spot.

  - As such, we hope to keep the flexibility of the actor from FAPE and extend it with both temporal and non-temporal lookahead capabilities
