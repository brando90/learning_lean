# Learning to write Lean

[Opening a lean project in VSCODE.](https://proofassistants.stackexchange.com/questions/2760/how-does-one-create-a-lean-project-and-have-mathlib-import-work-when-not-creatin/3779#3779)

We start of the bat recommending good sources for learning Lean 4:
- [documentation, some links there copied bellow](https://lean-lang.org/documentation/)
- [Theorem proving in Lean](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean, nice tutorial using maths on how to use Lean!](https://leanprover-community.github.io/mathematics_in_lean/)
- [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/)
- [Lean4 manual](https://lean-lang.org/lean4/doc/whatIsLean.html)
- [The Mechantics of Proof](https://hrmacbeth.github.io/math2001/)

Tactics refs
- [Lean 3](https://leanprover.github.io/reference/tactics.html)
- [Lean tactic Reference neu cs280](https://course.ccs.neu.edu/cs2800sp23/ref.html)

The goal will be to give an overview of useful tips for proving in Lean

## Unicode

For unicode use `\` backslash so that `\to` becomes an arrow. 
- `\^-1` for inverse e.g., `2⁻¹`
- `\l` for back arrow e.g., in rewrite
- `to` for arrow/implication
- TODO: iff
- `\R` for `ℝ`

## Tactics
tip: seems mathlib_4 documentation (& Moogle) are the best to find tactic docs.

### Entering tactic mode

- use `by` afte thm declaration e.g., `theorem thm_name : \forall n, n = n := by sorry` I think it works since `:=` expects you to write a function/proof term and then `by ...` enters tactic mode. `#print thm_name` TODO or something prints the proof term.

## Intro & Intros tactic
- TODO: intro intros

- `intro` introduces one or more hypotheses, optionally naming and/or pattern-matching them. For each hypothesis to be introduced, the remaining main goal's target type must be a let or function type.
  - it seems it also unfolds definitions for you (and yes introduces hypothesis.)
ref: [intro](https://leanprover-community.github.io/mathlib4_docs/Init/Tactics.html#Lean.Parser.Tactic.intro)

- `intros` Introduces zero or more hypotheses, optionally naming them.
  - intros is equivalent to repeatedly applying intro until the goal is not an obvious candidate for intro, ...
ref: [intros](https://leanprover-community.github.io/mathlib4_docs/Init/Tactics.html#Lean.Parser.Tactic.intros)

### Rewrite Tactic

My understanding is that rewrites is the substitution (rewrite a term) tactic when we have an equality. 
How tactic `rw` works:
- `rw [t]` applies from left to right on first term wrt to equality term `t` on goal
  - rw tactic closes/discharges any goals of the form `t = t`.
- rw [ <- t] or rw [ \l t ] to apply equality form left to right (on 1st term) on goal
- rw to rewrite hypothesis `h` do `rw [t] at h` 
- (rw to rewrite everything I assume rw [*] but then proof harder to read!)
- to apply tactic at specific loc do rw `[Nat.add_comm b]` if `a + (b + c)` --> `a + (c + b)`
  - tip: hover over Nat.add_comm to see how tactic and arg interact.
- rewrite using compund expression `rw [h1 h2]` <--> `rw [h1]; rw [h2]`
- rewrite can also rewrite terms that aren't equalities 
  - e.g., if `h_k_eq_0: k = 0` then `t : Pair 1 k` --> `t : Pair 1 0` with `rw [h_k_eq_0] at t`
ref: https://leanprover.github.io/theorem_proving_in_lean4/tactics.html

- `rwa` calls `rw`, then closes any remaining goals using `assumption`. Note: found by writing `rwa` in tactic mode then using vscode to get to it's def. Mathlib4 search, Moogle, didn't help surprisingly.

### Apply tactic

> `H` must be a **hypothesis** or **theorem** with type `P1 -> P2 -> ... -> PN -> Q`, where the **goal** has type `Q`. This tactic will replace the goal with `N` separate goals, `P1`, through `PN`, as it corresponds to deciding to prove the premises of `H` and then using it to prove the goal. In the simply case where you just have `P -> Q` this will replace `Q` with `P`.

remark: theorem/hypothesis are "applied"/treated as "inference rules" (if they have if, iff, mp, mpr).

Q: can apply be applied to hypothesis or how can it interact with hypothesis? (afaik only though elim rule as in CS477)

### Constructor tactic

- `constructor` If the main goal's target type is an inductive type, constructor solves it with the first matching constructor, or else fails.
  -tactic introduces a certain number of new proof obligations/goals to discharge/close according to each term in the constructor of the goal. 
  - e.g., if we have `... |- a \and k = 0 -> c` the constructor will open two goals where you need to prove `a` and `k = 0`. i.e., to have arrived at that goal you must have had a proof/evidence that `a` and `k=0` had proves e.g., `k = 0` might be a simple assumption in your "local context"/hypothesis space (TODO lean official lingo)

### Simp

Key facts about `simp` Lean3:
> The simplifier is what is known as **a conditional term rewriting system**: all it does is **repeatedly replace (or rewrite) subterms of the form A by B** (`B->A`), for all applicable facts of the form `A = B` or `A ↔ B`. The simplifier mindlessly rewrites until it can rewrite no more. The simp lemmas are all oriented, with **left-hand sides always being replaced by right-hand sides, and never vice versa**. 
> we would like the database of facts to be confluent, meaning the order in which the simplifier considers rewrites does not matter. Again, we aim to be close to confluent where possibl


Thoughts/Qs: "conditional term rewriting system" means to me it's a rewrite system. So it's more like how rewrite works to substitute/rewrite terms (automatically) -- than what apply would do. So if there are implications/iffs I think it should work more like rewrite, which is an equality rewrite tactic.
TODO: would be nice to understand the difference between `apply` vs `simp` vs `rewrite`.

```lean
set_option trace.simplify.rewrite true
```

refs:
  - https://leanprover-community.github.io/extras/simp.html
  - https://leanprover-community.github.io/mathlib4_docs/Init/Conv.html#Lean.Parser.Tactic.Conv.simp
  - coq's `simpl`: https://coq.inria.fr/doc/V8.19.0/refman/proofs/writing-proofs/equality.html?highlight=simpl#coq:tacn.simpl
  - you'd expect this to be useful but not super useful: https://leanprover-community.github.io/mathlib4_docs/Init/Conv.html#Lean.Parser.Tactic.Conv.simp


TODO: `dsimp`
> dsimp is the definitional simplifier in conv-mode. It differs from simp in that it only applies theorems that hold by reflexivity. (when is this ever useful, needed?)

### Conv
TODO: https://leanprover-community.github.io/extras/conv.html

> one way is to use a more precise tool : the conversion mode.

### Have
- `have : t := e` := "introduces theorem with proof `e` e.g., `e` can be `by tactics...` or the exact `proof term`
e.g.,
```lean
have h_pos : 0 < x⁻¹ := inv_pos.mpr h_x_pos
```

### Cases tactic

> if `id` is **a hypothesis (Hs)** of some inductive type, perform case analysis on it, either constructing **multiple hypotheses (if it (Hs) is a product type \and, x cartesian)** or **multiple goals (Gs) (if it is a sum type)**.
Q: todo, what does constructing multiple hypothesis means? Does this mean multiple hs to same proof state or more proof states are constructed with the "splitting" of Hs in original proof state?
> Notice that and-introduction and and-elimination are similar to the pairing and projection operations for the Cartesian product. The difference is that given hp : p and hq : q, And.intro hp hq has type p ∧ q : Prop, while Prod hp hq has type p × q : Type. The similarity between ∧ and × is another instance of the Curry-Howard isomorphism, but in contrast to implication and the function space constructor, ∧ and × are treated separately in Lean.

Remark: curry-howard isomorphism & logical ops e.g., `\and` <-> correspondance with product/cartesian product `x`. `\or` <-> sum type (idk what this is yet).

Tips:
> 1. The (unstructured) cases is particularly useful when you can close several subgoals using the same tactic. https://leanprover.github.io/theorem_proving_in_lean4/tactics.html#more-tactics

Q: "The cases tactic can be used to decompose any element of an inductively defined type; constructor always applies the first applicable constructor of an inductively defined type."

> Lean 3: For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `cases n` produces one goal with hypothesis `h : P 0` and `target Q 0`, and one goal with hypothesis `h : P (nat.succ a)` and target `Q (nat.succ a)`. Here the name a is chosen automatically.

Q: cases applied to a sum seems to produce multiple goals/proof states to completed.

> Q: There are two constructors for Or, called Or.inl : a → a ∨ b and Or.inr : b → a ∨ b, and you can use match or cases to destruct an Or assumption into the two cases (from Or msg in vscode hovering)

- naming new hypothesis with `cases h with`, ref: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/how.20to.20name.20new.20hypothesis.20using.20cases.20h.20with.20in.20Lean.204/near/425170964 
> TODO

ref:
  - https://leanprover.github.io/theorem_proving_in_lean4/tactics.html#more-tactics
  - https://course.ccs.neu.edu/cs2800sp23/ref.html


### Dot deperator for cases .
Do `.` to handle each case e.g., in induction.


### Tacticals
Note: `;` is not a tactical. TODO what is?
TODO: tactical vs combinators `tac1 <;> tac2`

### Options

```lean4
set_option pp.implicit true
set_option pp.universes true
set_option pp.notation false
set_option pp.numerals false
```

ref: https://leanprover.github.io/reference/other_commands.html#options

### Expressions

TODO: `\forall x : R, x < 0'

### Mathlib tips

- use less than (lt) in terms (e.g., thms) so it's easier to prove things.
- `m_lt_m_right` TODO: what is tip?

### Seeing Propositional Constructors
ref: [How do I explicitly see the propositional or logical constructors in Lean 4?](https://proofassistants.stackexchange.com/questions/3794/how-do-i-explicitly-see-the-propositional-or-logical-constructors-in-lean-4)

TODO: precedence of exists, forall vs And, implicaiton. 

And < (less precedence than) Implcation <==> `A /\ B -> B` means `(A /\ B) -> B`.
Exists delta, P delta -> P' delta <==>

### Terminology

- argument vs parameter -> argument (calling) the argument of f is 2, parameter (declaration) of f is n: Nat
- elaboration
- proof term
- proof obligation
- discharge vs closed in context of target vs goal/proof state etc
- goal vs proof term vs target: sometimes a doc will say a new "goal" which in my terminology means a proof state (=local context, + goals). The target is the actual thing to be proved (what I used to "confusingly" used to call goal). So careful what things mean in each context.

### Questions:
Q: what is a macro again?
Q: why is there this Init.Tactics vs Std.Tactic.Rcases 
https://leanprover-community.github.io/mathlib4_docs/Std/Tactic/RCases.html#Std.Tactic.rintro
https://leanprover-community.github.io/mathlib4_docs/Init/Tactics.html#Lean.Parser.Tactic.constructor
Q: destructing patterns, rcases, rintro & rcases vs constructor
Q: apply but to the hypothesis, how it works? afaik only elim tactic can do it and apply always matches goal to do anything
Q: def of induction (and program) and how it's a rule in the context of apply vs induction n. Compare them.