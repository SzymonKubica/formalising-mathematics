/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!
# Logic in Lean, example sheet 1 : "implies" (`→`)
We learn about propositions, and implications `P → Q` between them. You can get
this arrow by typing `\to` or `\r`. Mathematicians usually write the
implication arrow as `P ⇒ Q` but Lean prefers a single arrow.
## The absolute basics
`P : Prop` means that `P` is a true-false statement. `h : P` means
that `h` is a proof that `P` is true, or you can regard `h` as an
assumption that `P` is true; logically these are the same. Stuff above
the `⊢` symbol is your assumptions. The statement to the right of it is
the goal. Your job is to prove the goal from the assumptions.
## Tactics you will need
To solve the levels on this sheet you will need to know how to use the
following three tactics:
* `intro`
* `exact`
* `apply`
You can read the descriptions of these tactics in Part C of the online course
notes here https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_C/tactics/tactics.html
In this course we'll be learning about 30 tactics in total; the goal of this
first logic section is to get you up to speed with ten very basic ones.
## Worked examples
Click around in the proofs to see the tactic state (on the right) change.
The tactic is implemented and the state changes just before the comma.
I will use the following conventions: variables with capital
letters like `P`, `Q`, `R` denote propositions
(i.e. true/false statements) and variables whose names begin
with `h` like `h1` or `hP` are proofs or hypotheses.
-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variables (P Q R : Prop)

-- Here are some examples of `intro`, `exact` and `apply` being used.

-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.
example (hP : P) (hQ : Q) (hR : R) : P :=
begin
  -- note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.
  exact hP
end

-- Same example: assume that `P` and `Q` and `R` are true, but this time
-- give the assumptions silly names. Deduce that `P` is true.
example (fish : P) (giraffe : Q) (dodecahedron : R) : P :=
begin
  exact fish
end

-- Assume `Q` is true. Prove that `P → Q`.
example (hQ : Q) : P → Q :=
begin
  -- The goal is of the form `X → Y` so we can use `intro`
  intro h,
  exact hQ
  -- now `h` is the hypothesis that `P` is true.
  -- Our goal is now the same as a hypothesis so we can use `exact`
  -- note `exact Q` doesn't work: `exact` takes the *term*, not the type.
end

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q :=
begin
  -- our goal is `⊢ Q` which matches with the conclusion of `h` so `apply` works
  -- apply h,
  apply h,
  exact hP,
  -- now our goal has changed to `P` which is an assumption
  -- exact hP,
end

/-
## Examples for you to try
Delete the `sorry`s and replace them with comma-separated tactic proofs
using `intro`, `exact` and `apply`.
-/

/-- Every proposition implies itself. -/
example : P → P :=
begin
  intro h,
  exact h,
end

/-
Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.
So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, this means that to deduce `R` you will need to prove both `P`
and `Q`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and then you have to prove `Pn`.
So the next level is asking you prove that `P → (Q → P)`.
-/
example : P → Q → P :=
begin
  intro h,
  intro h1,
  exact h,
end

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q :=
begin
  intro h,
  intro h1,
  apply h1,
  exact h,
end

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/
example : (P → Q) → (Q → R) → (P → R) :=
begin
  intro h,
  intro h1,
  intro h2,
  apply h1,
  apply h,
  exact h2,
end

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
-- two goals! Note that tactics operate on only the first goal.
example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  intro h1,
  intro h2,
  intro h3,
  apply h1,
  exact h3,
  apply h2,
  exact h3,
end

--example : (P → Q → R) → (P → Q) → (P → R) :=
--λ hPQ hQR hP, hPQ (hQR hP)

/-
Here are some harder puzzles. They won't teach you anything new about
Lean, they're just trickier. If you're not into logic puzzles
and you feel like you understand `intro`, `exact` and `apply`
then you can just skip these and move onto the next sheet
in this section, where you'll learn some more tactics.
-/

variables (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T :=
begin
  intro h1,
  intro h2,
  intro h3,
  intro h4,
  intro h5,
  apply h3,
  apply h4,
  apply h2,
  exact h5,
end

example : (P → Q) → ((P → Q) → P) → Q :=
begin
  intro h1,
  intro h2,
  apply h1,
  apply h2,
  exact h1,
end

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P :=
begin
  intro h1,
  intro h2,
  intro h3,
  apply h2,
  intro h4,
  apply h1,
  intro h5,
  exact h4,
end

example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
begin
  intro h1,
  intro h2,
  intro h3,
  apply h1,
  intro h4,
  apply h3,
  apply h2,
  exact h4,
end

example : (((P → Q) → Q) → Q) → (P → Q) :=
begin
  intro h1,
  intro h2,
  apply h1,
  intro h3,
  apply h3,
  exact h2,
end

example :
  (((P → Q → Q) → ((P → Q) → Q)) → R) →
  ((((P → P) → Q) → (P → P → Q)) → R) →
  (((P → P → Q) → ((P → P) → Q)) → R) → R :=
begin
  intro h1,
  intro h2,
  intro h3,
  apply h2,
  intro h4,
  intro h5,
  intro h5,
  apply h4,
  intro h5,
  exact h5,
end
