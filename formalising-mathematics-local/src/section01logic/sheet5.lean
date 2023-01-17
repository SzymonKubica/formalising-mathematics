/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  split,
  cases h,
  exact h_mpr,
  cases h,
  exact h_mp,
end

lemma L1 : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  split,
  cases h,
  exact h_mpr,
  cases h,
  exact h_mp,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro h1,
  apply L1,
  exact h1,
  intro h2,
  apply L1,
  exact h2,
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro h1,
  intro h2,
  cases h1,
  cases h2,
  split,
  intro h3,
  apply h2_mp,
  apply h1_mp,
  exact h3,
  intro h4,
  apply h1_mpr,
  apply h2_mpr,
  exact h4,
end

lemma L2 : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h,
  split,
  exact h_right,
  exact h_left,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  repeat {
    intro h1,
    apply L2,
    exact h1,
  },
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  intro h1,
  cases h1,
  split,
  cases h1_left,
  exact h1_left_left,
  cases h1_left,
  split,
  exact h1_left_right,
  exact h1_right,
  intro h1,
  split,
  cases h1,
  cases h1_right,
  split,
  exact h1_left,
  exact h1_right_left,
  cases h1,
  cases h1_right,
  exact h1_right_right,
end

example : P ↔ (P ∧ true) :=
begin
  split,
  intro h,
  split,
  exact h,
  triv,
  intro h,
  cases h,
  exact h_left,
end

example : false ↔ (P ∧ false) :=
begin
  split,
  intro h,
  exfalso,
  exact h,
  intro h,
  cases h,
  exact h_right,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intro h1,
  intro h2,
  cases h1,
  cases h2,
  split,
  intro h3,
  split,
  cases h3,
  apply h1_mp,
  exact h3_left,
  cases h3,
  apply h2_mp,
  exact h3_right,
  intro h,
  cases h,
  split,
  apply h1_mpr,
  exact h_left,
  apply h2_mpr,
  exact h_right,
end

lemma EM : P ∧ ¬ P -> false :=
begin
  intro h1,
  cases h1,
  change P -> false at h1_right,
  apply h1_right,
  exact h1_left,
end


example : ¬ (P ↔ ¬ P) :=
begin
  change (P ↔ ¬ P) → false,
  intro h,
  cases h,
  by_cases P,
  have h2: ¬ P :=
  begin
    apply h_mp,
    exact h,
  end,
  apply EM,
  have h3: P ∧ ¬ P :=
  begin
    split,
    exact h,
    exact h2,
  end,
  exact h3,
  have h2: P :=
  begin
    apply h_mpr,
    exact h,
  end,
  apply EM,
  have h3: P ∧ ¬ P :=
  begin
    split,
    exact h2,
    exact h,
  end,
  exact h3,
end
