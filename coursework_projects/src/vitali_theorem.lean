import tactic
import measure_theory.measurable_space

import measure_theory.function.uniform_integrable
import measure_theory.function.lp_space
import topology.metric_space.basic

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


-- Additional notation for convergence in L1 which makes the code more readable :
def tendsto_in_L1 {m : measurable_space X}
(μ : measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
filter.tendsto (λ (n : ℕ), snorm (f n - g) 1 μ) filter.at_top (𝓝  0)


-- In the main theorem we need to know that convergence in L1 implies convergence
-- in measure. The theorem below proves this :

lemma dist_eq_nnorm (x : ℝ) (y : ℝ) : dist x y = ‖x - y‖₊ :=
begin
  rw real.dist_eq,
  simp,
end

lemma lift_ennreal_to_nnreal (a : ℕ → ℝ≥0∞) (ha : ∀ (n : ℕ), a n < ∞) :
∀ (i : ℕ), a i ≠ ⊤ :=
begin
  intro n,
  specialize ha n,
  rw ← lt_top_iff_ne_top,
  exact ha,
end

theorem squeeze_nnreal (a b : ℕ → ℝ≥0) (hbge0 : ∀ n, 0 ≤ b n) (hblta : ∀ n, b n ≤ a n) (haconv : tendsto a at_top (𝓝 0)) :
tendsto b at_top (𝓝 0) :=
begin
  rw ← nnreal.tendsto_coe at *,
  exact squeeze_zero hbge0 hblta haconv,
end

theorem squeeze (a b : ℕ → ℝ≥0∞) (ha : ∀ (n : ℕ), a n < ∞) (hb : ∀ (n : ℕ), b n < ∞)
(hbge0 : ∀ n, 0 ≤ b n) (hblta : ∀ n, b n ≤ a n) (haconv : tendsto a at_top (𝓝 0)) :
tendsto b at_top (𝓝 0) :=
begin
  lift a to ℕ → ℝ≥0,
  {exact lift_ennreal_to_nnreal a ha },
  lift b to ℕ → ℝ≥0,
  {exact lift_ennreal_to_nnreal b hb },
  rw ← ennreal.coe_zero,
  rw ennreal.tendsto_coe,
  simp at hblta,
  dsimp at hbge0,
  rw ← ennreal.coe_zero at haconv,
  rw ennreal.tendsto_coe at haconv,
  rw ← ennreal.coe_zero at hbge0,
  have hbge0: ∀ (n : ℕ), 0 ≤ b n,
  { intro n,
    specialize hbge0 n,
    rw ← ennreal.coe_le_coe,
    exact hbge0, },
  exact squeeze_nnreal a b hbge0 hblta haconv,
end

theorem sub_strongly_measurable (m : measurable_space X) (μ : measure X) [is_finite_measure μ]
(f g : X → ℝ) (hf : mem_ℒp f (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ) : ae_strongly_measurable (f - g) μ :=
begin
  let l:  list (X → ℝ) := f :: [-g],
  have hg2: ae_strongly_measurable (-g) μ,
  { exact ae_strongly_measurable.neg hg.left },
  have hl: ∀ (f : X → ℝ), f ∈ l → ae_strongly_measurable f μ,
  { intros k k_in_l,
    by_cases k = f,
    { rw h,
      exact hf.left,},
    { have hkg : k = -g,
      { have h_eq_or_ne_mem_of_mem : k = f ∨ k ≠ f ∧ k ∈ [-g],
        { exact list.eq_or_ne_mem_of_mem k_in_l, },
        cases h_eq_or_ne_mem_of_mem,
        { exfalso,
          apply h,
          exact h_eq_or_ne_mem_of_mem, },
        { exact list.mem_singleton.mp h_eq_or_ne_mem_of_mem.right }, },
      rw hkg,
      exact hg2, }, },
    have h_list_sum: ae_strongly_measurable (λ (x : X), (list.map (λ (f : X → ℝ), f x) l).sum) μ,
    { exact list.ae_strongly_measurable_sum l hl, },
    simp at h_list_sum,
    exact h_list_sum,
end

theorem tendsto_in_measure_of_tendsto_L1 (m : measurable_space X) (μ : measure X) [is_finite_measure μ]
(f : ℕ → X → ℝ) (g : X → ℝ) (hf : ∀ (n : ℕ), mem_ℒp (f n) (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ)
(h : tendsto_in_L1 μ f g) :
tendsto_in_measure μ f filter.at_top g :=
begin
  -- We need to use Markov's inequality.
  intros ε hε,
  have h2 : ∀ (ε : ℝ≥0∞), ε ≠ 0 →  ∀ (n : ℕ), μ { x | ε ≤ ‖(λ x, f n x - g x) x‖₊} ≤ ε⁻¹ ^ ennreal.to_real(1) * snorm ((f n) - g) 1 μ ^ ennreal.to_real(1),
  { intros ε hε,
    intro n,
    have one_ne_top : (1 : ℝ≥0∞) ≠ ⊤,
    { simp, },
    have h3 : ae_strongly_measurable (λ x, f n x - g x) μ,
    { specialize hf n,
      exact sub_strongly_measurable m μ (f n) g hf hg, },
    have hε_ne_zero : ε ≠ 0,
    { simp, exact hε },
    exact meas_ge_le_mul_pow_snorm μ one_ne_zero one_ne_top h3 hε_ne_zero, },
  simp at h2,
  specialize h2 (ennreal.of_real ε),
  have hε2 : (ennreal.of_real ε) ≠ 0,
  { simp, linarith, },
  specialize h2 hε2,
  have h4 : ∀ n x,  dist (f n x) (g x) = ‖ (λ x, f n x - g x) x ‖₊ ,
  { intros n x,
    change dist (f n x) (g x) = ‖ f n x - g x ‖₊,
    exact dist_eq_norm (f n x) (g x), },
    -- Here we need a theorem that if we have two sequences and one is greater
    -- then the other for all ℕ and converges to 0 then so does the other

  let a : ℕ → ℝ≥0∞ := λ n, (ennreal.of_real ε)⁻¹ * snorm ((f n) - g) 1 μ,
  let b : ℕ → ℝ≥0∞ := λ n, μ {x : X | ε ≤ dist (f n x) (g x)},

  have h5 : ∀ n, b n ≤ a n,
  { intro n,
    specialize h2 n,
    specialize h4 n,
    have h5b : {x : X | ε ≤ dist (f n x) (g x)} = {x : X | ennreal.of_real(ε) ≤ ‖(λ x, f n x - g x) x ‖₊},
    { ext,
      split,
      { intro hx,
        simp,
        simp at hx,
        rw real.ennnorm_eq_of_real_abs,
        apply ennreal.of_real_le_of_real,
        rw real.dist_eq at hx,
        exact hx, },
      { intro hx,
        simp,
        simp at hx,
        rw real.ennnorm_eq_of_real_abs at hx,
        rw real.dist_eq,
        have h_nonneg : 0 ≤ | f n x - g x |,
        { exact abs_nonneg (f n x - g x)},
        exact (ennreal.of_real_le_of_real_iff h_nonneg).mp hx, },},
    -- Here we need to use change to unwrap the definition back.
    change μ {x : X | ε ≤ dist (f n x) (g x)} ≤ (ennreal.of_real ε)⁻¹ * snorm ((f n) - g) 1 μ,
    rw h5b,
    exact h2, },

  have hε_ne_top: (ennreal.of_real ε)⁻¹ ≠ ⊤,
    { rw ennreal.inv_ne_top,
      simp,
      exact hε, },

  have h6 : tendsto a filter.at_top (𝓝  0),
  { -- Here I need to show that if fₙ converges to g in L1 then if we multiply it by
    -- 1/ε then it also converges
    rw tendsto_in_L1 at h,
    change tendsto (λ n, (ennreal.of_real ε)⁻¹ * snorm ((f n) - g) 1 μ) filter.at_top (𝓝  0),
    have htendsto : tendsto (λ n, (ennreal.of_real ε)⁻¹ * snorm ((f n) - g) 1 μ) filter.at_top (𝓝 ((ennreal.of_real ε)⁻¹ * 0)),
    have hε_good: (0 : ℝ≥0∞) ≠ 0 ∨ (ennreal.of_real ε)⁻¹ ≠ ⊤,
    { right, exact hε_ne_top, },
    { exact ennreal.tendsto.const_mul h hε_good, },
    simp at htendsto,
    exact htendsto, },

  -- in order to apply the squeeze we also need to show that for all n the measure
  -- of the set ε ≤ ... is non-negative, which follows from definition so simp will work.
  have h7 : ∀ n, 0 ≤ b n, { simp, },

  have h8 : ∀ (n : ℕ), a n < ∞,
  { intro n,
    change (ennreal.of_real ε)⁻¹ * snorm ((f n) - g) 1 μ < ⊤,
    apply ennreal.mul_lt_top,
    { exact hε_ne_top },
    { have hfg: mem_ℒp ((f n) - g) 1 μ,
      { exact mem_ℒp.sub (hf n) hg, },
      rw ← lt_top_iff_ne_top,
      exact hfg.right, }, },
  have h9 : ∀ (n : ℕ), b n < ∞,
  { intro n,
    change μ {x : X | ε ≤ dist (f n x) (g x)} < ⊤,
    exact measure_lt_top μ ({x : X | ε ≤ dist (f n x) (g x)}), },

  exact squeeze a b h8 h9 h7 h5 h6,
end

theorem vitali_theorem {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
(f : ℕ → X → ℝ) (g : X → ℝ) (hf : ∀ (n : ℕ), mem_ℒp (f n) (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ) :
tendsto_in_measure μ f filter.at_top g ∧ unif_integrable f 1 μ ↔
filter.tendsto (λ (n : ℕ), snorm (f n - g) 1 μ) filter.at_top (𝓝  0) :=
begin
  split,
  { sorry,  },
  { intro h_tendsto_L1,
    split,

    { exact tendsto_in_measure_of_tendsto_L1 m μ f g hf hg h_tendsto_L1},
    { intros ε hε, sorry, },},
end

/--
theorem vitali (hμ : is_finite_measure μ) (f : ℕ → α → ℝ) (g : α → ℝ)
(hf : ∀ n, integrable (f n) μ ) (integrable g μ) : tendsto_in_measure f g
begin
end
--/
