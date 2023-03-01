import tactic
import measure_theory.measurable_space

import measure_theory.function.uniform_integrable

namespace measure_theory
open_locale classical measure_theory nnreal ennreal topological_space


open set filter topological_space


/-- Statement of the theorem
    If X has finite measure and 'f : ℕ → a → ℝ is a sequence of functions and
    g : a → ℝ is a function and all of them are in L_1(μ) then f n → g in measure
    and {f n | n ∈ ℕ } has uniformly absolutely continuous integrals iff the integral
    of |f n - g| dμ → 0 as n → ∞
 -/

variables {X : Type} {m : measure_space X}

def tendsto_in_measure {m : measure_space X}
  (μ : measure X) (f : ℕ → X → ℝ) (l : filter ℕ) (g : X → ℝ) : Prop :=
∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ dist (f i x) (g x)}) l (𝓝 0)

def unif_abs_cont_integrals {I : Type} (m : measure_space X) (μ : measure X) (f : I → X → ℝ) : Prop :=
∀ ⦃ε : ℝ⦄ (hε : 0 < ε), ∃ (δ : ℝ) (hδ : 0 < δ), ∀ i s, measurable_set s → μ s ≤ ennreal.of_real δ →
snorm (s.indicator (f i)) 1 μ ≤ ennreal.of_real ε

-- We need to show that any finite family of functions in L_1(μ) has uniformly
-- absolutely continuous integrals as this fact will be used in the main statement
-- of the theorem.

theorem fin_family_has_uaci {m: measure_space X} {μ : measure X} (f : finset ℕ → X → ℝ):
unif_abs_cont_integrals m μ f :=
begin
  sorry,
end

#check measure_theory.unif_integrable


theorem vitali_theorem {X : Type} {m : measure_space X} {μ : measure X} [is_finite_measure μ] [normed_add_comm_group ℝ≥0∞]
(f : ℕ → X → ℝ) (g : X → ℝ) (hf : ∀ (n : ℕ), mem_ℒp (f n) (1 : ℝ≥0∞)) (hg : mem_ℒp g 1):
tendsto_in_measure μ f filter.at_top g ∧ unif_abs_cont_integrals m μ f ↔ filter.tendsto (λ (n : ℕ), snorm (f n - g) 1 μ) filter.at_top (𝓝  0) :=
begin
  split,
  { sorry,  },
  { intro h_tendsto_in_L1,
    split,
    {  }, -- Follows quickly from 2.43 -> fill in later.
    { intros ε hε,
      rw tendsto_def at h_tendsto_in_L1,



      --specialize h_tendsto_in_L1 (Ioo (0) (ennreal.of_real (ε/2))),
      --have hIoo: Ioo (0) (ennreal.of_real (ε/2)) 𝓝 0,
      { },




    },},
end

/--
theorem vitali (hμ : is_finite_measure μ) (f : ℕ → α → ℝ) (g : α → ℝ)
(hf : ∀ n, integrable (f n) μ ) (integrable g μ) : tendsto_in_measure f g
begin
end
--/

