/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ∪ A = A :=
begin
  ext x,
  split,
  {
    intro h,
    cases h;
    exact h,
  },
  {
    intro h,
    left,
    exact h,
  },
end

example : A ∩ A = A :=
begin
  ext x,
  split,
  {
    intro h,
    exact h.left,
  },
  {
    intro h,
    split;
    exact h,
  },
end

example : A ∩ ∅ = ∅ :=
begin
  ext x,
  split,
  {
    intro h,
    exact h.right,
  },
  {
    intro h,
    split,
    {
      exfalso,
      exact h,
    },
    {
      exact h,
    },
  },
end

example : A ∪ univ = univ :=
begin
  ext x,
  split,
  {
    intro h,
    triv,
  },
  {
    intro h,
    right,
    triv,
  },
end

example : A ⊆ B → B ⊆ A → A = B :=
begin
  intros hab hba,
  ext x,
  split,
  {
    intro h,
    apply hab,
    exact h,
  },
  {
    intro h,
    apply hba,
    exact h,
  },
end

example : A ∩ B = B ∩ A :=
begin
  ext x,
  split;
  repeat {
    intro h,
    split,
    { exact h.right },
    { exact h.left },
  },
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  ext x,
  split,
  {
    intro h,
    split,
    {
      split,
      { exact h.left },
      { exact h.right.left },
    },
    {
      exact h.right.right
    },
  },
  {
    intro h,
    split,
    {
      exact h.left.left,
    },
    {
      split,
      { exact h.left.right },
      { exact h.right },
    },
  },
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with ha hbc,
    {
      left,
      left,
      exact ha,
    },
    {
      cases hbc with hb hc,
      {
        left,
        right,
        exact hb,
      },
      {
        right,
        exact hc,
      },
    },
  },
  {
    intro hx,
    cases hx with hab hc,
    {
      cases hab with ha hb,
      {
        left,
        exact ha,
      },
      {
        right,
        left,
        exact hb,
      },
    },
    {
      right,
      right,
      exact hc,
    },
  },
end

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  ext x,
  split,
  {
    intro hx,
    split,
    {
      cases hx with ha hbc,
      { left, exact ha },
      { right, exact hbc.left },
    },
    {
      cases hx with ha hbc,
      { left, exact ha },
      { right, exact hbc.right },
    },
  },
  {
    intro hx,
    cases hx with hab hac,
    cases hab with ha hb,
    {
      left,
      exact ha,
    },
    {
      cases hac with ha hc,
      {
        left,
        exact ha,
      },
      {
        right,
        split,
        { exact hb },
        { exact hc },
      },

    },

  },
end

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with ha hbc,
    cases hbc with hb hc,
    {
      left,
      split,
      { exact ha },
      { exact hb },
    },
    {
      right,
      split,
      { exact ha },
      { exact hc },
    },
  },
  {
    intro hx,
    cases hx with hab hac,
    {
      split,
      { exact hab.left },
      { left, exact hab.right },
    },
    {
      split,
      { exact hac.left },
      { right, exact hac.right },
    },
  },
end

