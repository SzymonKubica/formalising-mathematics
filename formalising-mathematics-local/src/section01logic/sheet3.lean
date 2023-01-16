/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

-- Random code from lectures

def D : Prop := 2 + 2 = 5

#check D
#print D

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro h,
  change true -> false at h,
  apply h,
  triv,
end

example : false → ¬ true :=
begin
  intro h,
  exfalso,
  exact h,
end

example : ¬ false → true :=
begin
  intro h,
  triv,
end

example : true → ¬ false :=
begin
  intro h0,
  by_contra,
  exact h,
end

example : false → ¬ P :=
begin
  intro h0,
  by_contra,
  exact h0,
end

lemma EM : P ∧ ¬ P -> false :=
begin
  intro h1,
  cases h1,
  change P -> false at h1_right,
  apply h1_right,
  exact h1_left,
end

lemma EM_2 : (P ∧ ¬ P) -> false :=
begin
  intro h1,
  cases h1,
  change P -> false at h1_right,
  apply h1_right,
  exact h1_left,
end

example : P → ¬ P → false :=
begin
  intro h1,
  intro h2,
  have h3 : P ∧ ¬ P,
  split,
  exact h1,
  exact h2,
  apply EM,
  exact h3,
end

example : P → ¬ (¬ P) :=
begin
  intro h,
  change not P -> false,
  intro h1,
  have h2 : P ∧ ¬ P,
  split,
  exact h,
  exact h1,
  apply EM,
  exact h2,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro h1,
  intro h2,
  by_contra,
  change Q -> false at h2,
  apply h2,
  apply h1,
  exact h,
end

example : ¬ ¬ false → false :=
begin
  intro h1,
  change ¬ false → false at h1,
  apply h1,
  change false -> false,
  intro h2,
  exact h2,
end

example : ¬ ¬ P → P :=
begin
  intro h1,
  change ¬ P → false at h1,
  by_contra,
  apply h1,
  exact h,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intro h1,
  intro h2,
  by_contra,
  have h3: ¬ P :=
  begin
    apply h1,
    exact h,
  end,
  have h4: P ∧ ¬ P,
  split,
  exact h2,
  exact h3,
  apply EM,
  exact h4,
end
