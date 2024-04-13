# Cleaner notes on uncertainty

## Introduction

We suggest an extension to the chronicle formalism in [1], to allow for specifications on both temporal and non-temporal uncertainty. We also propose an approach to address these new specifications in the constraint satisfaction problem (CSP) encoding the planning problem.

Our suggestions are inspired by the "risk allocation" approach from [2]. In [2], "risk allocation" was used to address the problem of assessing risk-bounded dynamic controllability in temporal networks with uncontrollable probabilistic durations for some activities. Our aim is to expand the risk allocation approach from [2] to planning problems in order to support both temporal and non-temporal uncertainty, as well as probability distributions that may be defined conditionally.

## Formalism extension

A (hierarchical) chronicle from [1] is defined as a tuple `(V, tau, X, C, E, S)`. We propose an extended definition `(V, I, tau, X, C, E, S, R)` where:
- `V, tau, X, C, E, S` are the same as before (variables, refined task, conditions, effects, subtasks).
- `I` is an influence diagram (without utility nodes) on variables from `V`, expressing conditional probability relationships on them. With this definition, the uncontrollable (aka contingent, aka random) variables in `V` are those that appear in "uncertainty nodes" of the influence diagram. All other variables are assumed to be controllable (aka decision variables). 
- `R` is a set of "risk specifications". What we call a risk specification is a tuple `(req, delta)`, where `req` is a subset of constraints from `X`, which we refer to as the "requirements" of the risk specification, and `delta` is a value between 0 and 1, which we refer to as its risk bound.

Note that there are no formal restrictions on uncontrollable variables: they are allowed to parametrise any element of the chronicle ("refined task" `tau`, "constraints" `X`, "conditions" `C`, effects `E`, subtasks `S`). This means that we could model uncontrollable choices of refinement chronicles for subtasks. This could be done by (1) introducing an uncontrollable parameter variable to task symbols, and (2) restricting possible refinement chronicles for those task symbols to specific ranges in that uncontrollable parameter variable's domain. This could be useful to specify uncontrollable alternatives in plans. Additionally, this could be useful to specify "structurally different" effects for an action chronicle, by attaching it with a "dummy subtask" with an uncontrollable parameter, and whose possible refinements would represent the different kinds of effects.


Intuitively, the meaning of a risk specification `(req, delta)` is that in the solution plan (which consists of full assignments to controllable variables), when the chronicle is present, the requirements `req` (which is a subset of constraints from the set `X` of the chronicle) are allowed to fail (i.e. be inconsistent) only with a probability less than `delta`. This could be expressed in the CSP encoding the planning problem as a chance constraint `presence(chronicle) => P(\/!constr (for constr in req)) < delta`.

However, addressing such a chance constraint directly would be very difficult. This is where the concept of risk allocation, which we adapt from [2], comes into play. The idea of the risk allocation approach is, for a given full instantiation of controllable variables, to search for "risk allocated bounds" (or simply "risk allocations") on the domains of uncontrollable variables "relevant" to the constraints in `req`, such that (1) the constraints in `req` are satisfied for the given full instantiation of controllable variables and for instantiations of (uncontrollable) "relevant" variables lying inside their "risk allocated bounds", and (2) the total probability mass outside of the "risk allocated bounds" for the (uncontrollable) "relevant" variables is less than `delta`. We will define what "relevant" variables are further below. For now, we simply denote them as `relevant(req)`.



 it can be defined as it can be defined recursively, starting from a 

As such, for all "relevant" uncontrollable variables, the risk allocation problem introduces two new controllable variables, corresponding to the lower and upper risk allocation bounds. Then, given a full instantiation of controllable variables, risk allocation can be expressed as the chance constaint `P(\/ (v_lra < v \/ v < v_ura) (for v in relevant(req) such that presence(v) /\ presence(req.chronicle))) < delta` (in addition to the satisfaction of the CSP encoding the planning problem, for the given full instantiation of controllable variables and for all instantiations lying inside `[v_lra, v_ura]`, for variables `v` in `relevant(req)`).


Now, what are "relevant" variables ? Intuitively, the set of "relevant" variables `relevant(req)` is the aggregation of uncontrollable variables that may affect the satisfaction of any constraint in `req`. More formally, we can define it as `relevant(req) = \/relevant(constr) (for constr in req)`. And for a constraint `constr` in `req`, `relevant(constr)` can be recursively defined as containing:
- all uncontrollable variable appearing in `constr`
- for each variable `v` in `relevant(constr)`, all its uncontrollable ancestors in the influence diagrams where it appears must be in `relevant(constr)` as well
- all ancestor (uncontrollable) variables of uncontrollable variable `v` in the influence diagrams in which it appears.





The probability expression above is difficult to evaluate, because it is equal to a sum with a factorial number of terms (inclusion-exclusion formula)... Therefore, as in [2], we opt to consider an upper bound for it instead. The consequence of this is that we're overestimating the true risk - in other words, we take a conservative approach to the problem. In [2], the basic union bound is used 


 Indeed, the requirements `req` of the risk specification implicitly represent a subset of constraints of the planning problem. We denote this subset of constraints as `req_constrs`. It can be defined as `req_constrs = { supported(cond) for condition cond in req, coherent(eff, eff') for effect eff in req and any other effect eff' on the same state function, refined(subt) for subtask subt in req, presence(chronicle) => /\constr for all constraints constr in req }`. In other words, each condition `cond` in `req` implicitly represents its `supported(cond)` constraint, each effect `eff` in `req` implicitly represents all the `coherent(eff,*)` constraints involving it, each subtask `subt` in `req` implicitly represents its `refined(subt)` constraint, and each constraint `constr` (element of `X`) in `req` is implicitly grouped into a constraint `presence(chronicle) => /\x (for all x in constr)`. Note that all the constraints in `req_constrs` contain `presence(chronicle)` as one of their implicants (the only one, actually, except for `coherent` constraints which have two implicants, the second of which may be different).

The risk allocation approach to uncertainty consists in finding "risk allocated bounds" (or simply "risk allocations") on the domains of uncontrollable variables that may be "relevant" to a risk specification's requirements `req`, such that these "relevant" variables' total probability mass outside of the "risk allocated bounds" is less than `delta`. We say that an (uncontrollable) variable is relevant to a risk specification when it can affect the satisfaction of the constraints in `req_constrs`. We denote the relevant variables for a risk specification's requirements as `relevant(req)`.

The relevant variables are actually difficult to define without full assignments to presence variables. Indeed, depending on the assignments to presence variables, the "structure" of the solution plans may be very different, and therefore the relevant variables (i.e. uncontrollable variables that may affect the satisfaction of the constraints in `req_constrs`) may be very different as well. So we consider 

As such the risk allocation approach adds to the planning problem a "reformulated chance constraint" `rcc`, defined as `P(\/((P /\ presence(vu)) => (vu < vu_lra \/ vu_ura < v)) (for all vu in relevant(req))) < delta`, where `vu_lra` (respectively `vu_ura`) are controllable variables representing the lower (respectively upper) "risk allocated bounds" to find for relevant uncontrollable variable `vu`. By `P` we refer to 







Rigorously defining risk specifications without full assignments to (controllable) presence variables would be very complex and many ambiguous situations would arise. Presence variables assignments' dictate what chronicles are present in the solution, in other words, what chronicles are part of the plan. This means that the "general context" or plan structure could be very different depending on assignments to presence variables. At the same time however, depending on the plan structure, the variables "relevant" to a risk specification for a chronicle could theoretically be very different for different plans, even if they contain chronicle defining the considered risk specification. As such, there is no real way of determining the variables "relevant" to a risk specification in different "contexts". Fortunately, rigorously defining risk specifications when the plan structure is known is much easier. Let, for a assignment



In [1], it is shown how chronicles can be used to describe a planning problem, and how that planning problem can be encoded as a CSP. Our risk specifications `(rho, delta)` are interpreted as chance constraints on a set `A_rho` of constraints from the CSP, involving elements from the requirements `rho`. Formally,`A_rho = { support constraints for conditions in rho, all coherence constraints for effects in rho, refinement constraints for subtasks in rho, partial internal consistency constraints for constraints in rho (i.e. presence(chronicle) => constr, for constr in rho) }`. 

^^^ BUGBUGBUG ^^^: some sort of "relevancy" should be defined... because it is not trivial -> see Wang multiple chance constraints (or maybe we should "branch" on the set of relevant elements, depending on presences / presence literals values ?) Or maybe (this seems to be the most straightforward) we should explicitly formalize things for already given controllable variables instantiations. Indeed, without options, it's much easier to define what the "relevancy" is.



Then, the chance constraint described by the risk specification `(rho, delta)` is `P(!A_rho) <= delta` or, alternatively, `P(A_rho) >= 1-delta`. We may refer to it as `CC`.

Now, tackling such a complex chance constraint directly would be extremely difficult, if not impossible. This is where the risk allocation approach comes into play. For a given instantiation of controllable variables, risk allocation consists in finding "risk allocated bounds" on the domains of uncontrollable variables involved in constraints `A_rho` such that (1) the constraints in `A_rho` are satisfied for any outcome (or instantation) of uncontrollable variables inside these bounds, and (2) the total probability mass outside these bounds is less than `delta`. This can be expressed through a "reformulated chance constraint" replacing `CC`, which we may refer to as `RCC`. `RCC` can be written as `P( \/(for uncontrollable variables v_unctr involved in constraints in A_rho) ((presence(v_unctr) /\ presence(chronicle containing the element of A_rho)) => (v_unctr < v_unctr_lra \/ v_unctr_ura < v_unctr)) <= delta` where `v_unctr_lra` (respectively `v_unctr_ura`) is the lower (respectively upper) risk allocated bound for `v_unctr`.

However, `RCC` is still too difficult to address directly. This is why we will replace the probability expression in it by an upper bound of it. The consequence of this is that we will be overestimating the risk probability, which corresponds to a "conservative" approach. The simplest upper bound for the probability of a union is the "union bound" (from Boole's inequality). In our case, it could be written as pseudo-boolean expression `sum(for uncontrollable variables v_unctr involved in constraints in A_rho) (F_v_unctr(v_unctr_lra)[presence(v_unctr)] 1 -  )`
 In other words, an instantiation to uncontrollable variables (which could be obtained by sampling the probabilities described by the influence diagram `I`) is allowed to make the risk specifications `rho` inconsistent only with a probability less than than the risk bound `delta`. The concrete and rigorous interpretation of a risk specification is given below.

In [1], it is shown how chronicles can be used to describe a planning problem, and how that planning problem can be encoded as a CSP. Our risk specifications are interpreted are as 


Our risk specification extension to the chronicle formalism comes with an adaptation of the risk allocation approach from [2] to the encoding of chronicle-based planning problems as a CSP. In the risk allocation approach, the objective is to 

## References

[[1] Godet2022]()

[[1] Wang2022]()
