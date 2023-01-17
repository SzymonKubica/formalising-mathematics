/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro h,
  cases h1: h,
  exact left,
end

example : P ∧ Q → Q :=
begin
  intro h,
  cases h1: h,
  exact right,
end


example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intros h1 h2,
  cases h2,
  apply h1,
  exact h2_left,
  exact h2_right,
end

-- !!!!!!!!
-- Bad code !!!!!! Don't do that
example : P → Q → P ∧ Q :=
begin
  intro h1,
  intro h2,
  split,
  exact h1,
  exact h2,
end

-- Better code style below:
example : P → Q → P ∧ Q :=
begin
  intros h1 h2,
  split,
  { exact h1, },
  { exact h2, },
end

-- Or even more fancy:
example : P → Q → P ∧ Q :=
begin
  intros h1 h2,
  split,
  exacts [h1, h2],
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro h1,
  split,
  cases h1,
  exact h1_right,
  cases h1,
  exact h1_left,
end

example : P → P ∧ true :=
begin
  intro h,
  split,
  exact h,
  triv,
end

example : false → P ∧ false :=
begin
  intro h,
  split,
  exfalso,
  repeat {exact h},
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intro h1,
  intro h2,
  cases h1,
  cases h2,
  split,
  exact h1_left,
  exact h2_right,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intro h1,
  intro h2,
  intro h3,
  apply h1,
  split,
  exact h2,
  exact h3,
end
