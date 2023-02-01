/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import group_theory.subgroup.basic -- imports the theory of subgroups

/-!

# Subgroups

In Lean, a subgroup is not a group. This is for the same reason that a subset
is not a type. The way subgroups work is that if `G` is a group:

`variables (G : Type) [group G]`

then the type of *all* subgroups of `G` is called `subgroup G`. So if you want
one subgroup of G:

`variable (H : subgroup G)`

then, as you can see, `H` is not a type (we don't write `H : Type`), it's a term.
So how do we do elements of `H` then? It's just the same as sets: an element `x` of
`H` is a term `x` of type `G`, such that the proposition `x ∈ H` holds.

Here's the basic API for subgroups.

-/

-- Let `G` be a group, let `a` and `b` be elements of `H`, and let `H` and `K` be subgroups of `G`.
variables (G : Type) [group G] (a b : G) (H K : subgroup G)

-- The basic API for subgroups
example : (1 : G) ∈ H := one_mem H
example (ha : a ∈ H) : a⁻¹ ∈ H := inv_mem ha
example (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := mul_mem ha hb


-- Examle from lecture on 01.02.2023
example (ha : a ∈ H) : false :=
begin
  -- H has been promoted to a type.
  -- let's make the term of type ↑H corresponding to
  let b : H := ⟨a, ha⟩,

  cases b,


  sorry,
end

-- Let's use these axioms to make more API for subgroups.

-- First, see if you can put the axioms together to prove subgroups are closed under "division".
example (ha : a ∈ H) (hb : b ∈ H) : a * b⁻¹ ∈ H :=
mul_mem ha (inv_mem hb)

-- Now try these. You might want to remind yourself of the API for groups as explained
-- in an earlier section, or make use of the `group` tactic.

-- This lemma is called `inv_mem_iff` but try proving it yourself
example : a⁻¹ ∈ H ↔ a ∈ H :=
begin
  refine ⟨_, inv_mem⟩,
  intro h,
  convert inv_mem h,
  group,
end

-- this is `mul_mem_cancel_left` but see if you can do it from the axioms of subgroups.
-- Again feel free to use the `group` tactic.
example (ha : a ∈ H) : a * b ∈ H ↔ b ∈ H :=
begin
  sorry,
end

/-

## Complete lattice structure on subgroups of G

Subgroups of a group form a complete lattice. Let's just check this:

-/

example : complete_lattice (subgroup G) := infer_instance

/-

The "type class inference system" (the system which deals with square bracket inputs to
functions) already knows this. `infer_instance` means "find this construction in the
database".

Because subgroups are a complete lattice, there will be a smallest subgroup `⊥` of `G`
and a largest subgroup `⊤`. You can guess what these are (note that `⊥` isn't the empty set,
this isn't a subgroup). Let's get the hang of these subgroups. Here's their API
(by the way, I don't have a clue about these APIs, I don't have them all committed to memory,
I just write down the natural statements and then either guess the names of the proofs or
use `library_search`):

-/

example : a ∈ (⊥ : subgroup G) ↔ a = 1 := subgroup.mem_bot
example : a ∈ (⊤ : subgroup G) := subgroup.mem_top a

/-

# Conjugating a subgroup by an element.

Let's define the conjugate `xHx⁻¹` of a subgroup `H` by an element `x`. To do this we
are going to have to know how to *make* subgroups, not just prove things about subgroups.

To create a subgroup of `G`, you need to give a subset of `G` and then a proof
that the subset satisfies the three axioms `one_mem`, `inv_mem` and `mul_mem` for subgroups.
If `H : subgroup G` and `x : G` then the *conjugate* of `H` by `x` is
the set `{a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}`. So let's show that this set
satisfies the axioms for a subgroup.

-/

variables {G H} {x : G}

variables (y z : G)

lemma conjugate.one_mem : (1 : G) ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} :=
begin
  use 1,
  split,
  { apply one_mem, },
  { group, },
end

lemma conjugate.inv_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
  y⁻¹ ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} :=
begin
  rcases hy with ⟨g, hg, rfl⟩,
  change ∃ h, _,
  use g⁻¹,
  split,
  { exact inv_mem hg, },
  { group, },

end

lemma conjugate.mul_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹})
  (hz : z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
  y * z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} :=
begin
  rcases hy with ⟨g, hg, rfl⟩,
  rcases hz with ⟨k, hk, rfl⟩,
  exact ⟨g * k, mul_mem hg hk, by group⟩,
end

-- Now here's the way to put everything together:
def conjugate (H : subgroup G) (x : G) : subgroup G :=
{ carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹},
  one_mem' := conjugate.one_mem,
  inv_mem' := conjugate.inv_mem,
  mul_mem' := conjugate.mul_mem, }

/-

## The cost of a definition

You might think "we're done, we made conjugates"! But not so fast!

If we were putting the definition of `conjugate` into mathlib then the next thing we would have to
do would be to prove a whole bunch of things about it. Every definition in a formalised system
comes with a cost. If you just make the definition and don't prove theorems about it,
then other people can't use your definition easily in their theorems.

What kind of theorems would we want to prove about conjugates? We might want to prove
that if `H ≤ K` then `conjugate H x ≤ conjugate K x`. We might want to prove
that `conjugate ⊥ x = ⊥` and `conjugate ⊤ x = ⊤`. And we might want to prove
that if `G` is abelian then `conjugate H x = H` for all `H`. Before we embark on this,
I had better tell you how to prove that two subgroups of a group are equal in Lean.
To check two subgroups are equal it suffices to prove they have the same elements:
this is called "extensionality" for subgroups, and you can make this step using the `ext`
tactic. I'll show you below.

Let's make some API for conjugates. I'll suggest some names for the lemmas.

-/

-- This one is always handy: you will be able to `rw` it when faced with goals
-- of the form `a ∈ conjugate H x`.

lemma mem_conjugate_iff : a ∈ conjugate H x ↔ ∃ h, h ∈ H ∧ a = x * h * x⁻¹ :=
begin
  -- true by definition!
  refl,
end

lemma conjugate_mono (H K : subgroup G) (h : H ≤ K) : conjugate H x ≤ conjugate K x :=
begin
  -- start with `intro g` because the goal is definitionally
  -- `∀ g, g ∈ conjugate H x → g ∈ conjugate K x`
  sorry,
end

lemma conjugate_bot : conjugate ⊥ x = ⊥ :=
begin
  -- recall that ⊥ is the trivial subgroup and I showed you the basic API for it above.
  -- Start this proof with `ext a`.
  sorry,
end

lemma conjugate_top : conjugate ⊤ x = ⊤ :=
begin
  sorry,
end

lemma conjugate_eq_of_abelian (habelian : ∀ a b : G, a * b = b * a) : conjugate H x = H :=
begin
  sorry,
end
