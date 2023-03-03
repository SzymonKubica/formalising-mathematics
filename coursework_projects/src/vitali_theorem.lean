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

/-- This theorem allows to use squeeze_zero theorem on two sequences of non-negative
    real numbers. It is used by ennreal_squeeze_zero. -/
theorem nnreal_squeeze_zero {a b : ℕ → ℝ≥0} (hbge0 : ∀ n, 0 ≤ b n) (hblta : ∀ n, b n ≤ a n) (haconv : tendsto a at_top (𝓝 0)) :
tendsto b at_top (𝓝 0) :=
begin
  rw ← nnreal.tendsto_coe at *,
  exact squeeze_zero hbge0 hblta haconv,
end

/-- This lemma allows us to coerce from a sequence of extended non-negative real
    numbers to a sequence of non-negative numbers given that neither of the terms
    of the sequence is equal to ∞ -/
lemma lift_ennreal_to_nnreal {a : ℕ → ℝ≥0∞} (ha : ∀ (n : ℕ), a n < ∞) :
∀ (i : ℕ), a i ≠ ⊤ :=
begin
  intro n,
  exact lt_top_iff_ne_top.mp (ha n),
end

/-- This theorem allows us to use squeeze_zero on the extended non-negative
    real numbers (ℝ≥0∞) provided that both of these sequences consist purely of
    real numbers. -/
theorem ennreal_squeeze_zero {a b : ℕ → ℝ≥0∞}
(ha : ∀ (n : ℕ), a n < ∞) (hb : ∀ (n : ℕ), b n < ∞)
(h0b : ∀ n, 0 ≤ b n) (hba : ∀ n, b n ≤ a n) (ha_to_0 : tendsto a at_top (𝓝 0)) :
tendsto b at_top (𝓝 0) :=
begin
  -- First we need to coerce the sequences to apply nnreal_squeeze_zero on them.
  lift a to ℕ → ℝ≥0, {exact lift_ennreal_to_nnreal ha },
  lift b to ℕ → ℝ≥0, {exact lift_ennreal_to_nnreal hb },
  -- Now we need to rewrite to get rid of coercions from ℝ≥0 to ℝ≥0∞
  rw [← ennreal.coe_zero, ennreal.tendsto_coe] at *,
  simp at hba,
  dsimp at h0b,
  have h0b: ∀ (n : ℕ), 0 ≤ b n,
  { -- Here we need to artificially rewrite
    -- so that h0b unifies with what nnreal_squeeze_zero expects.
    intro n,
    exact ennreal.coe_le_coe.mp (h0b n), },
  exact nnreal_squeeze_zero h0b hba ha_to_0,
end

/-- This theorem proves that if we have a list of two ae_strongly_measurable
    functions, then all functions belonging to that list are ae_strongly_measurable.
    It seems trivial but it was a good exercise of working on finite lists and
    illustrates how finiteness can be a bit tricky in lean. -/
lemma list_elem_ae_strongly_measurable {m : measurable_space X} {μ : measure X}
{f g : X → ℝ} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
{l : list (X → ℝ)} (hl : l = [f, g]) :
∀ (k : X → ℝ), k ∈ l → ae_strongly_measurable k μ :=
begin
  -- First let k be an arbitrary element of l perform case analysis depending on
  -- whether or not it is equal to the first element in the list.
  intros k k_in_l,
  by_cases k = f,
  { rw h, exact hf},
  { -- Here we show that if it is not equal to f then it must be equal to g
    -- as l has only two elements. As stated above it wasn't trivial.
    have hkg : k = g,
    { have h_cases : k = f ∨ k ≠ f ∧ k ∈ [g],
      { rw hl at k_in_l, exact list.eq_or_ne_mem_of_mem k_in_l, },
      cases h_cases,
      { exfalso, exact h h_cases, },
      { exact list.mem_singleton.mp h_cases.right }, },
    rw hkg,
    exact hg, },
end

/-- This theorem asserts that if we subtract two functions in L1, then
    the resulting function is ae_strongly_measurable. It is used in the proof of
    the theorem that if a sequence of functions converges in L1 then it also
    converges in measure. After proving this statement I realised that it is
    actually already present in the mathlib library. However, I've decided to keep
    it here as it has a slightly more convenient signature (the hypotheses that
    it requires are easily accessible in the main theorem) and also it required
    some list manipulations and proving something for a finite list which I found
    quite interesting and more difficult than anticipated. -/
theorem sub_strongly_measurable {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
{f g : X → ℝ} (hf : mem_ℒp f (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ) : ae_strongly_measurable (f - g) μ :=
begin
  -- In order to apply ae_strongly_measurable_sum we need a list.
  let l :  list (X → ℝ) := [f, -g],
  have hg2: ae_strongly_measurable (-g) μ,
  { exact ae_strongly_measurable.neg hg.left },
  have hl_def : l = [f, -g], { simp, }, -- Need this to apply the lemma
  have hl: ∀ (f : X → ℝ), f ∈ l → ae_strongly_measurable f μ,
  { exact list_elem_ae_strongly_measurable hf.left hg2 hl_def },
  have h_list_sum: ae_strongly_measurable (λ (x : X), (list.map (λ (f : X → ℝ), f x) l).sum) μ,
  { exact list.ae_strongly_measurable_sum l hl, },
  simp at h_list_sum,
  exact h_list_sum,
end

/-- This is a special case of the Markov's inequality when p=1 it is used in the
    next theorem. -/
theorem markov_ineq_L1 {m : measurable_space X} (μ : measure X)
{f : X → ℝ} (hf : ae_strongly_measurable f μ) :
∀ (ε : ℝ≥0∞), ε ≠ 0 → μ { x | ε ≤ ‖ f x ‖₊ } ≤ ε⁻¹ * snorm f 1 μ :=
begin
  intros ε hε,
  -- Before we apply the Markov's inequality in the special case where p = 1,
  -- we need to show 1 ≠ ∞ and ε ≠ 0 so that the theorem can be applied.
  have one_ne_top : (1 : ℝ≥0∞) ≠ ⊤, { simp, },
  have hε_ne_zero : ε ≠ 0, { simp, exact hε },
  -- This library function produces unnecessary ennreal.to_real(1) and so exact
  -- doesn't work immediately, I need to assign it to a hypothesis h2 and simplify.
  let h2 :=  meas_ge_le_mul_pow_snorm μ one_ne_zero one_ne_top hf hε_ne_zero,
  simp at h2,
  exact h2,
end

/-- This lemma shows that if we have two functions f and g then for any ε the set:
    { x | ε ≤ dist (f x) (g x) } is equal to { x | ennreal.of_real(ε) ≤ ‖f - g‖₊ }
    it looks trivial but it doesn't follow from definitional equality. -/
lemma set_ε_le_dist_eq_set_ε_le_nnorm (f g: X → ℝ) (ε : ℝ) :
{x : X | ε ≤ dist (f x) (g x)} = {x : X | ennreal.of_real(ε) ≤ ‖f x - g x‖₊} :=
begin
  ext,
  split,
  { intro hx,
    simp at *,
    rw real.ennnorm_eq_of_real_abs,
    apply ennreal.of_real_le_of_real,
    rw real.dist_eq at hx,
    exact hx, },
  { intro hx,
    simp at *,
    rw real.ennnorm_eq_of_real_abs at hx,
    rw real.dist_eq,
    exact (ennreal.of_real_le_of_real_iff (abs_nonneg (f x - g x))).mp hx, },
end

/-- This lemma shows that snorm of a difference of two functions in L1 when multiplied
    by a constant is less that ∞. -/
lemma const_mul_sub_snorm_lt_top {m : measurable_space X} {μ : measure X} {f g : X → ℝ}
(k : ℝ≥0∞) (hk : k ≠ ⊤) (hf : mem_ℒp f 1 μ) (hg : mem_ℒp g 1 μ) :
k * snorm (f - g) 1 μ < ⊤ :=
begin
  apply ennreal.mul_lt_top,
  { exact hk },
  { have hfg: mem_ℒp (f  - g) 1 μ,
    { exact mem_ℒp.sub hf hg, },
    rw ← lt_top_iff_ne_top,
    exact hfg.right, },
end

/--In the main theorem we need to know that convergence in L1 implies convergence
   in measure. The theorem below proves this: -/
theorem tendsto_in_measure_of_tendsto_L1 {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
{f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ (n : ℕ), mem_ℒp (f n) (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ)
(h : tendsto_in_L1 μ f g) :
tendsto_in_measure μ f filter.at_top g :=
begin
  -- Here we aim to apply the Markov's inequality to fₙ - g for all n ∈ ℕ.
  -- The ennreal.to_real
  have h2 : ∀ (ε : ℝ≥0∞), ε ≠ 0 →  ∀ (n : ℕ), μ { x | ε ≤ ‖f n x - g x‖₊ } ≤
    ε⁻¹  * snorm ((f n) - g) 1 μ ,
  { intros ε hε n,
    -- We use sub_strongly_measruable to show that fₙ - g is ae_strongly_measurable.
    exact markov_ineq_L1 μ (sub_strongly_measurable (hf n) hg) ε hε, },
  simp at h2,

  intros ε hε,
  -- We need to cast ε and it's hypothesis into ℝ≥0∞ because that's what h2 expects.
  have hε2 : (ennreal.of_real ε) ≠ 0, { simp, linarith, },
  specialize h2 (ennreal.of_real ε) hε2,

  have h4 : ∀ n x,  dist (f n x) (g x) = ‖f n x - g x‖₊ ,
  { intros n x, exact dist_eq_norm (f n x) (g x), },

  -- Here I define two sequences of numbers in ℝ≥0∞ to make the rest of the
  -- proof more readable.
  let a : ℕ → ℝ≥0∞ := λ n, (ennreal.of_real ε)⁻¹ * snorm ((f n) - g) 1 μ,
  let b : ℕ → ℝ≥0∞ := λ n, μ {x : X | ε ≤ dist (f n x) (g x)},

  -- In order to apply the squeeze_zero theorem, we need to show the below:
  have h_b_le_a : ∀ n, b n ≤ a n,
  { intro n,
    have h_set_eq : {x : X | ε ≤ dist (f n x) (g x)} =
                    {x : X | ennreal.of_real(ε) ≤ ‖f n x - g x‖₊},
    { exact set_ε_le_dist_eq_set_ε_le_nnorm (f n) g ε },

    -- Here we need to use change to unwrap the definition back and make rw work.
    change μ {x : X | ε ≤ dist (f n x) (g x)} ≤ (ennreal.of_real ε)⁻¹ * snorm ((f n) - g) 1 μ,
    rw h_set_eq,
    exact h2 n, },

  -- This hypothesis will be used in two places in the later part of the proof,
  -- that's why it was placed here.
  have hε_ne_top: (ennreal.of_real ε)⁻¹ ≠ ⊤,
  { rw ennreal.inv_ne_top,
    simp,
    exact hε, },

  have h_a_tendsto_0 : tendsto a filter.at_top (𝓝  0),
  { -- Here we need to show that if fₙ converges to g in L1 then if we multiply it by
    -- 1/ε then it also converges

    -- ennreal.tendsto.const_mul requires that either the limit is not zero or
    -- the inverse of the constant that we want to multiply by is ≠ ∞.
    -- We prove this by showing the second disjunct.
    have hε_inv_ne_top: (0 : ℝ≥0∞) ≠ 0 ∨ (ennreal.of_real ε)⁻¹ ≠ ⊤,
    { right, exact hε_ne_top, },

    let htendsto := ennreal.tendsto.const_mul h hε_inv_ne_top,
    simp at htendsto,
    exact htendsto, },

  -- In order to apply the squeeze we also need to show that for all n the measure
  -- of the set ε ≤ ... is non-negative, which simp will give us.
  have h_0_le_b : ∀ n, 0 ≤ b n, { simp, },

  -- Before we apply the ennreal_squeeze_zero we need to show that both sequences
  -- a and b consist of only real numbers, that way the theorem can cast them to
  -- nnreal later on.
  have h_a_lt_top : ∀ (n : ℕ), a n < ∞,
  { intro n,
    change (ennreal.of_real ε)⁻¹ * snorm ((f n) - g) 1 μ < ⊤,
    exact const_mul_sub_snorm_lt_top (ennreal.of_real ε)⁻¹ hε_ne_top (hf n) hg, },
  have h_b_lt_top : ∀ (n : ℕ), b n < ∞,
  { intro n, exact measure_lt_top μ ({x : X | ε ≤ dist (f n x) (g x)}), },

  exact ennreal_squeeze_zero h_a_lt_top h_b_lt_top h_0_le_b h_b_le_a h_a_tendsto_0,
end

/-- This is a special case of the Vitali's theorem in L1. -/
theorem vitali_theorem {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
(f : ℕ → X → ℝ) (g : X → ℝ) (hf : ∀ (n : ℕ), mem_ℒp (f n) (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ) :
tendsto_in_measure μ f filter.at_top g ∧ unif_integrable f 1 μ ↔
filter.tendsto (λ (n : ℕ), snorm (f n - g) 1 μ) filter.at_top (𝓝  0) :=
begin
  split,
  { sorry,  },
  { intro h_tendsto_L1,
    split,
    { exact tendsto_in_measure_of_tendsto_L1 hf hg h_tendsto_L1},
    { intros ε hε,
      sorry,
    },},
end

end measure_theory
