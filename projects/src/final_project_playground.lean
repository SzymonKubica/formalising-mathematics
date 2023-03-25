
-- AIM: do something in functional analysis.

-- TODO:
-- → ask the people on Zulip chat what can be done in functional analysis
-- → get proficient with the toolkit provided by the mathlib library.
-- → go through the notes for FANA and find something interesting yet manageable.


import tactic
import analysis.normed_space.lp_space -- theory of ℓᵖ spaces

open_locale ennreal -- to get notation ℝ≥0∞


-- The setup is the following: in order to interact with elements of ℓᵖ we need
-- to define some index set I and a function E which maps from I to Type and
-- for all i ∈ I after applying E to i we get an alement of a normed additive
-- commutative group and so we have a norm ‖x‖ which induces a metric dist(x, y) = ‖x - y‖
-- we also need to have a member of ennreal to be able to talk about ℓᵖ

variables (I : Type) (E : I → Type) [∀ i, normed_add_comm_group (E i)] (p : ℝ≥0∞)

-- This is a function which effectively represents a member of ℓᵖ.
variable (v : Π i, E i)

example (v : Π i, E i) : Prop := mem_ℓp v p

-- We can for example show that any sequence which has a finite support is in ℓᵖ.
example : mem_ℓp v 0 ↔ set.finite {i | v i ≠ 0} :=
begin
  exact mem_ℓp_zero_iff,
end


-- Let's try to do it from first principles.
example : mem_ℓp v 0 ↔ set.finite {i | v i ≠ 0} :=
begin
  exact mem_ℓp_zero_iff,
end

