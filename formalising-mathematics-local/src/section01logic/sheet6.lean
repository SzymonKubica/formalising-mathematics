/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro h,
  left,
  exact h,
end

example : Q → P ∨ Q :=
begin
  intro h,
  right,
  exact h,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intro h1,
  intro h2,
  intro h3,
  cases h1,
  apply h2,
  exact h1,
  apply h3,
  exact h1,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro h,
  cases h,
  right,
  exact h,
  left,
  exact h,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  intro h1,
  cases h1,
  cases h1,
  left,
  exact h1,
  right,
  left,
  exact h1,
  right,
  right,
  exact h1,
  intro h2,
  cases h2,
  left,
  left,
  exact h2,
  cases h2,
  left,
  right,
  exact h2,
  right,
  exact h2,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intro h1,
  intro h2,
  intro h3,
  cases h3,
  left,
  apply h1,
  exact h3,
  right,
  apply h2,
  exact h3,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intro h1,
  intro h2,
  cases h2,
  left,
  apply h1,
  exact h2,
  right,
  exact h2,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intro h1,
  intro h2,
  split,
  intro h3,
  cases h3,
  left,
  cases h1,
  apply h1_mp,
  exact h3,
  right,
  cases h2,
  apply h2_mp,
  exact h3,
  intro h3,
  cases h3,
  left,
  cases h1,
  apply h1_mpr,
  exact h3,
  right,
  cases h2,
  apply h2_mpr,
  exact h3,
end

lemma EM : P ∧ ¬ P -> false :=
begin
  intro h1,
  cases h1,
  change P -> false at h1_right,
  apply h1_right,
  exact h1_left,
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
 split,
 intro h1,
 split,
 change P → false,
 intro h2,
 have h3: P ∨ Q → false,
 intro h4,
 have h5: (P ∨ Q) ∧ ¬ (P ∨ Q),
 split,
 exact h4,
 exact h1,
 apply EM,
 exact h5,
 apply h3,
 left,
 exact h2,
 change Q → false,
 intro h2,
 have h3: P ∨ Q → false,
 intro h4,
 have h5: (P ∨ Q) ∧ ¬ (P ∨ Q),
 split,
 exact h4,
 exact h1,
 apply EM,
 exact h5,
 apply h3,
 right,
 exact h2,
 intro h1,
 by_contra,
 cases h1,
 cases h,
 have h3: P ∧ ¬ P,
 split,
 exact h,
 exact h1_left,
 apply EM,
 exact h3,
 have h3: Q ∧ ¬ Q,
 split,
 exact h,
 exact h1_right,
 apply EM,
 exact h3,
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  intro h1,
end
