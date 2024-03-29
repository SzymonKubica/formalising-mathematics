import tactic
import measure_theory.measurable_space
import measure_theory.function.uniform_integrable
import measure_theory.function.lp_space
import topology.metric_space.basic

open_locale classical measure_theory nnreal ennreal topological_space

open set filter topological_space measure_theory

/-- Szymon Kubica (CID: 01871147, college username sk4520) March 6, 2023

This file contains a proof of the Vitali's theorem as well as all of the
lemmas that I needed to prove it.

Statement of the theorem :
  If X has finite measure and 'f : ℕ → a → ℝ is a sequence of functions and
  g : a → ℝ is a function and all of them are in L_1(μ) then fₙ  → g in measure
  and {fₙ | n ∈ ℕ } has uniformly absolutely continuous integrals iff the integral
  of |f n - g| dμ → 0 as n → ∞ (i.e. fₙ → g in L_1(μ))  -/

variables {X : Type}

/-- I decided to add alias definitions for the two notions of convergence that
    we deal with in the proof. They improve readability at a cost of sometimes
    introducing an additional rewrite step. -/
def tendsto_in_L1 {m : measurable_space X}
(μ : measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
filter.tendsto (λ (n : ℕ), snorm (f n - g) 1 μ) filter.at_top (𝓝 0)

/-- This is a custom aliasing definition for convergence μ-a.e. -/
def tendsto_μ_ae {m : measurable_space X} (μ : measure X)
(f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
∀ᵐ (x : X) ∂μ, filter.tendsto (λ (n : ℕ), f n x) filter.at_top (𝓝 (g x))

-- I also introduced new domain-specific notation to make the code a bit more
-- human-readable
reserve infix `}`:65
reserve infix `{`:65
reserve infix `-→`:65
reserve infix `in_L1{`:65
reserve infix `in_measure{`:65
reserve infix `}_a-e`:65
reserve infix `∈_L1{`:65

-- Now three notions of convergence can be expressed using a consistent notation.
notation f `-→` g `in_L1{` μ `}` := tendsto_in_L1 μ f g
notation f `-→` g `in_measure{` μ `}` := tendsto_in_measure μ f at_top g
notation f `-→` g `{` μ `}_a-e` := tendsto_μ_ae μ f g

-- Also the notion of being a member of L1 is somewhat hard to decipher.
notation f `∈_L1{` μ `}` :=  mem_ℒp f 1 μ

-- When dealing with snorm it is nicer to be able to see them written as integrals
-- One thing to note is that sometimes the whole expression for the integrals
-- needs to be wrapped in a set of brackets as those custom operators have a low
-- precedence so that they don't interfere with other syntax.
reserve prefix `∫|`:55
reserve infix `|d`:55
notation `∫|` f `|d` μ :=  (snorm (f) 1 μ)

-- Also integrals over subsets are supported.
reserve prefix `∫_{`:55
reserve infix `}_|`:55
reserve infix `|d`:55
notation `∫_{` s `}_|` f `|d` μ :=  snorm (s.indicator f) 1 μ

-- I also found that I was using ennreal.of_real very frequently in the code
-- which sometimes made it overly verbose and cluttered. I decided to introduce
-- this shortcuts:
reserve prefix `ennreal{`:65
reserve postfix `}`:65
notation `ennreal{` a `}` := ennreal.of_real(a)

reserve prefix `real{`:65
reserve postfix `}`:65
notation `real{` a `}` := ennreal.to_real(a)

/-- This theorem allows to use squeeze_zero theorem on two sequences of non-negative
    real numbers. It is used by ennreal_squeeze_zero. -/
theorem nnreal_squeeze_zero {a b : ℕ → ℝ≥0}
(hbge0 : ∀ n, 0 ≤ b n) (hblta : ∀ n, b n ≤ a n) (haconv : tendsto a at_top (𝓝 0)) :
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
  have h0b : ∀ (n : ℕ), 0 ≤ b n,
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
theorem sub_strongly_measurable {m : measurable_space X} {μ : measure X}
{f g : X → ℝ} (hf : f ∈_L1{μ}) (hg : g ∈_L1{μ}) : ae_strongly_measurable (f - g) μ :=
begin
  -- In order to apply ae_strongly_measurable_sum we need a list.
  let l :  list (X → ℝ) := [f, -g],
  have hg2 : ae_strongly_measurable (-g) μ,
  { exact ae_strongly_measurable.neg hg.left },
  have hl_def : l = [f, -g], { simp, }, -- Need this to apply the lemma
  have hl : ∀ (f : X → ℝ), f ∈ l → ae_strongly_measurable f μ,
  { exact list_elem_ae_strongly_measurable hf.left hg2 hl_def },
  have h_list_sum : ae_strongly_measurable (λ (x : X), (list.map (λ (f : X → ℝ), f x) l).sum) μ,
  { exact list.ae_strongly_measurable_sum l hl, },
  simp at h_list_sum,
  exact h_list_sum,
end

/-- This is a special case of the Markov's inequality when p=1 it is used in the
    next theorem. -/
theorem markov_ineq_L1 {m : measurable_space X} (μ : measure X)
{f : X → ℝ} (hf : ae_strongly_measurable f μ) :
∀ (ε : ℝ≥0∞), ε ≠ 0 → μ { x | ε ≤ ‖ f x ‖₊ } ≤ ε⁻¹ * ∫|f|dμ  :=
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
lemma set_ε_le_dist_eq_set_ε_le_nnorm (f g : X → ℝ) (ε : ℝ) :
{x : X | ε ≤ dist (f x) (g x)} = {x : X | ennreal{ε} ≤ ‖f x - g x‖₊} :=
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
(k : ℝ≥0∞) (hk : k ≠ ⊤) (hf : f ∈_L1{μ}) (hg : g ∈_L1{μ}) : k * (∫|f - g|dμ) < ⊤ :=
begin
  apply ennreal.mul_lt_top,
  { exact hk },
  { have hfg : (f  - g) ∈_L1{μ},
    { exact mem_ℒp.sub hf hg, },
    rw ← lt_top_iff_ne_top,
    exact hfg.right, },
end

/--In the main theorem we need to know that convergence in L1 implies convergence
   in measure. The theorem below proves this: -/
theorem tendsto_in_measure_of_tendsto_L1 {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
{f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ (n : ℕ), f n ∈_L1{μ}) (hg : g ∈_L1{μ})
(h : f -→ g in_L1{μ}) : f -→ g in_measure{μ} :=
begin
  -- Here we aim to apply the Markov's inequality to fₙ - g for all n ∈ ℕ.
  have h2 : ∀ (ε : ℝ≥0∞), ε ≠ 0 →  ∀ (n : ℕ), μ { x | ε ≤ ‖f n x - g x‖₊ } ≤
    ε⁻¹  * ∫|(f n) - g|dμ,
  { intros ε hε n,
    -- We use sub_strongly_measruable to show that fₙ - g is ae_strongly_measurable.
    exact markov_ineq_L1 μ (sub_strongly_measurable (hf n) hg) ε hε, },
  simp at h2,

  intros ε hε,
  -- We need to cast ε and it's hypothesis into ℝ≥0∞ because that's what h2 expects.
  have hε2 : (ennreal{ε}) ≠ 0, { simp, linarith, },
  specialize h2 (ennreal{ε}) hε2,

  have h4 : ∀ n x,  dist (f n x) (g x) = ‖f n x - g x‖₊ ,
  { intros n x, exact dist_eq_norm (f n x) (g x), },

  -- Here I define two sequences of numbers in ℝ≥0∞ to make the rest of the
  -- proof more readable.
  let a : ℕ → ℝ≥0∞ := λ n, (ennreal{ε})⁻¹ * ∫|(f n) - g|dμ,
  let b : ℕ → ℝ≥0∞ := λ n, μ {x : X | ε ≤ dist (f n x) (g x)},

  -- In order to apply the squeeze_zero theorem, we need to show the below:
  have h_b_le_a : ∀ n, b n ≤ a n,
  { intro n,
    have h_set_eq : {x : X | ε ≤ dist (f n x) (g x)} =
                    {x : X | ennreal{ε} ≤ ‖f n x - g x‖₊},
    { exact set_ε_le_dist_eq_set_ε_le_nnorm (f n) g ε },

    -- Here we need to use change to unwrap the definition back and make rw work.
    change μ {x : X | ε ≤ dist (f n x) (g x)} ≤ (ennreal{ε})⁻¹ * ∫|(f n) - g|dμ,
    rw h_set_eq,
    exact h2 n, },

  -- This hypothesis will be used in two places in the later part of the proof,
  -- that's why it was placed here.
  have hε_ne_top : (ennreal{ε})⁻¹ ≠ ⊤,
  { rw ennreal.inv_ne_top,
    simp,
    exact hε, },

  have h_a_tendsto_0 : tendsto a filter.at_top (𝓝  0),
  { -- Here we need to show that if fₙ converges to g in L1 then if we multiply it by
    -- 1/ε then it also converges

    -- ennreal.tendsto.const_mul requires that either the limit is not zero or
    -- the inverse of the constant that we want to multiply by is ≠ ∞.
    -- We prove this by showing the second disjunct.
    have hε_inv_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ (ennreal{ε})⁻¹ ≠ ⊤,
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
    change (ennreal{ε})⁻¹ *  (∫|(f n) - g|dμ) < ⊤,
    exact const_mul_sub_snorm_lt_top (ennreal{ε})⁻¹ hε_ne_top (hf n) hg, },
  have h_b_lt_top : ∀ (n : ℕ), b n < ∞,
  { intro n, exact measure_lt_top μ ({x : X | ε ≤ dist (f n x) (g x)}), },

  exact ennreal_squeeze_zero h_a_lt_top h_b_lt_top h_0_le_b h_b_le_a h_a_tendsto_0,
end

/-- This lemma proves that if we take a single function in L1(μ) then it this set
    has uniformly absolutely continuous integrals. -/
theorem unif_integrable_singleton {m : measurable_space X} {μ : measure X}
{g : X → ℝ} (hg :g ∈_L1{μ}) :
∀ ⦃ε : ℝ⦄ (hε : 0 < ε), ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s
  → μ s ≤ ennreal{δ} → (∫_{s}_|g|dμ) ≤ ennreal{ε} :=
begin
  -- We define a finite set {g}.
  let G : fin 1 → X → ℝ := λ i, g,
  have hG : ∀ (i : fin 1), (G i) ∈_L1{μ}, { intro i, exact hg, },
  have hG_unif_integrable : unif_integrable G 1 μ,
  -- Here we show that it is has uniformly abs. cont. integrals.
  { exact unif_integrable_fin μ (le_refl 1) ennreal.one_ne_top hG, },
  intros ε hε,
  specialize hG_unif_integrable hε,
  rcases hG_unif_integrable with ⟨δ, hδ, hG⟩,
  use δ,
  split,
  { exact hδ },
  { intros s hs,
    specialize hG 1 s hs,
    exact hG, },
end

/-- This lemma allows for the usual manipulations of minimums within the world of
    ℝ≥0∞ numbers. It states that if we have two non-neg numbers a, b and we take the minimum
    of them, then ennreal.of_real(min a b) ≤ ennreal.of_real(a) and
    ennreal.of_real(min a b) ≤ ennreal.of_real(b) -/
lemma ennreal_min_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hmin : c = min a b) :
ennreal{c} ≤ ennreal{a} ∧ ennreal{c} ≤ ennreal{b} :=
begin
  rw hmin,
  split,
  { rw ennreal.of_real_le_of_real_iff,
    { exact min_le_left a b },
    { exact ha }, },
  { rw ennreal.of_real_le_of_real_iff,
    { exact min_le_right a b },
    { exact hb }, },
end

/-- This lemma allows us to use the triangle inequality on snorms over a specified
    set (i.e. the ones that have an indicator function inside). -/
lemma snorm_triangle_ineq {m : measurable_space X} {μ : measure X}
{ f g : X → ℝ } (hf :  ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
{s : set X} (hs : measurable_set s) :
( ∫_{s}_|f + g|dμ ) ≤ ( ∫_{s}_|f|dμ ) + ( ∫_{s}_|g|dμ ) :=
begin
  rw set.indicator_add',
      exact snorm_add_le (ae_strongly_measurable.indicator hf hs)
        (ae_strongly_measurable.indicator hg hs) (le_refl 1),
end

/-- This trivial lemma simplivies calculations in ennreal. -/
lemma two_halves_le_sum {a : ℝ} (ha : 0 < a) :
ennreal{a / 2} + ennreal{a / 2} ≤ ennreal{a} :=
begin
  have ha2 : 0 ≤ a / 2, {exact le_of_lt (half_pos ha), },
  rw ← ennreal.of_real_add,
  { simp, },
  { exact ha2 },
  { exact ha2 },
end

/-- This lemma allows us to get a δ := min δ₁ δ₂ such that if we get δ₁ from the
    u.a.c.i. statement for g and δ₂ from the statement for {fₙ | n ∈ ℕ} then
    both of the conclusions hold for sets of measure smaller than δ. The lemma
    is a bit specific and was extracted out only to improve the speed of computation
    when checking the main proof. If it were to be used in greater generality,
    one would have to remove the ε/3 and replace it with just ε but then in the
    main proof I would have to do some rearrangements which would slow down
    the compilation -/
lemma extract_δ_uaci {m : measurable_space X} {μ : measure X}
{ f : ℕ → X → ℝ } { g : X → ℝ }
(h_f_n_uaci : ∀ (ε : ℝ), 0 < ε →  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ (n : ℕ) s, measurable_set s →
              μ s ≤ ennreal{δ} → ( ∫_{s}_|f n|dμ ) ≤ ennreal{ε / 3})
(h_g_uaci : ∀ (ε : ℝ), 0 < ε →  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s →
            μ s ≤ ennreal{δ} → ( ∫_{s}_|g|dμ ) ≤ ennreal{ε / 3})
: ∀ (ε : ℝ), 0 < ε →  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal{δ} →
  ∀ (n : ℕ), ( ∫_{s}_|f n|dμ ) ≤ ennreal{ε / 3} ∧ ( ∫_{s}_|g|dμ ) ≤ ennreal{ε / 3} :=
begin
  intros ε hε,
  rcases h_g_uaci ε hε with ⟨δ₁, hδ₁, h_g_snorm⟩,
  rcases h_f_n_uaci ε hε with ⟨δ₂ , hδ₂, h_f_n_snorm⟩,
  use min δ₁ δ₂,
  split,
  { exact lt_min hδ₁ hδ₂ },
  {
    intros s hs hμs n,
    specialize h_g_snorm s hs,
    specialize h_f_n_snorm n s hs,
    split,
    { apply h_f_n_snorm,
      exact le_trans hμs (ennreal_min_le (le_of_lt hδ₁) (le_of_lt hδ₂)
                            (eq.refl (min δ₁ δ₂))).right, },
    { apply h_g_snorm,
      exact le_trans hμs (ennreal_min_le (le_of_lt hδ₁) (le_of_lt hδ₂)
                            (eq.refl (min δ₁ δ₂))).left, }, },
end

/-- This theorem states that if a function is in L1 then it has uniformly absolutely
    continuous integrals. --/
theorem unif_integrable_of_tendsto_L1 {m : measurable_space X} {μ : measure X}
{f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, (f n) ∈_L1{μ}) (hg : g ∈_L1{μ})
(hfg : f -→ g in_L1{μ}) : unif_integrable f 1 μ :=
begin
  intros ε hε,
  rw [tendsto_in_L1, ennreal.tendsto_at_top_zero] at hfg,
  have hε2 : ennreal{ε / 2} > 0,
  { simp, linarith },
  -- Here, given the fact that fₙ converges to g in L1, we extract a constant
  -- n₀ such that ∀ n ≥ n₀ we have ‖ fₙ - g ‖ < ε/2
  obtain ⟨n₀, hn₀⟩ := hfg (ennreal{ε / 2}) hε2,

  -- Now the idea is to show that the family {g, f₁, ..., fₙ₀} has uniformly
  -- absolutely continuous integrals. We need to first show it for the fₙ's and
  -- separately for g and then pick the minimum of the resulting deltas.

  -- Here we show that F = {f₁, ..., fₙ₀} has uniformly abs. cont. integrals.
  -- We need to add 1 to n₀ because fin only includes strictly smaller numbers.
  let F : fin (n₀ + 1) → X → ℝ := λ i, f i,
  have hF : ∀ (i : fin (n₀ + 1)), (F i) ∈_L1{μ}, { intro i, exact hf i, },
  have hF_unif_integrable : unif_integrable F 1 μ,
  { exact unif_integrable_fin μ (le_refl 1) ennreal.one_ne_top hF, },

  -- Here we use the fact that G = {g} has uniformly abs. cont. integrals
  -- to obtain the following expression:
  have hg_uaci : ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s →
      μ s ≤ ennreal{δ} → (∫_{s}_|g|dμ) ≤ ennreal{ε / 2},
  { exact unif_integrable_singleton hg (half_pos hε) },

  -- Now since we know that F and {g} have u.a.c.i, we can extract the corresponding
  -- δ's and take the minimum of them to get a δ such that for all s ∈ m with
  -- μ(s) < δ we have that for all functions in the family {g, f₁, ..., fₙ₀}
  -- we have that ∫ₛ|f|dμ < ε/2.
  have hε2' : 0 < ε/2, { exact half_pos hε, },
  specialize hF_unif_integrable hε2',
  rcases hg_uaci with ⟨δ₁, hδ₁, h_snorm1⟩,
  rcases hF_unif_integrable with ⟨δ₂, hδ₂, h_snorm2⟩,
  let δ := min δ₁ δ₂,
  have hδ' : δ = min δ₁ δ₂, { simp, }, -- Some lemmas used later need this explicit proposition.
  have hδ : 0 < δ, {rw lt_min_iff, exact ⟨hδ₁, hδ₂⟩},
  use [δ, hδ],
  intros n s hs hμs,
  -- At this point we need to handle two cases depeding on whether n ≤ n₀
  by_cases n ≤ n₀,
  { have hμs : μ s ≤ ennreal{δ₂},
    { exact le_trans hμs (ennreal_min_le (le_of_lt hδ₁) (le_of_lt hδ₂) hδ').right, },
    specialize h_snorm2 n s hs hμs,
    -- Here we need to coerce between the definition of F on fin (n₀ + 1) to ℕ.
    have hfF : ∀ n : ℕ, n ≤ n₀ → f n = F ↑n,
    { intros n hn,
      change f n = (λ i : fin (n₀ + 1), f ↑i) n,
      simp,
      have hn2 : n % (n₀ + 1) = n, {rw nat.mod_eq_of_lt, linarith, },
      rw hn2, },
    rw ← (hfF n h) at h_snorm2,
    have hε2_le : ennreal{ε / 2} ≤ ennreal{ε},
    { rw ennreal.of_real_le_of_real_iff; linarith, },
    exact le_trans h_snorm2 hε2_le, },
  { have h_manipulate : ∀ (n : ℕ), f n = g + (f n - g), { intro n, simp, },
    rw (h_manipulate n),
    -- Here we need to use the triangle inequality of snorm and distributivity
    -- of taking the indicator to get the desired inequality below.
    have h_snorm_le : ( ∫_{s}_|g + (f n - g)|dμ ) ≤ ( ∫_{s}_|g|dμ )  + ( ∫_{s}_|f n - g|dμ ),
    { exact snorm_triangle_ineq hg.left (ae_strongly_measurable.sub (hf n).left hg.left) hs, },

    have h_snorm_sum_le_ε : ( ∫_{s}_|g|dμ )  + ( ∫_{s}_|f n - g|dμ ) ≤ ennreal{ε},
    { have hn : n ≥ n₀, { linarith, },
      specialize hn₀ n hn,
      -- Here we need to use again the lemma which pushes a ≤ min a b into ennreal.
      have hμs : μ s ≤ ennreal{δ₁},
      { exact le_trans hμs (ennreal_min_le (le_of_lt hδ₁) (le_of_lt hδ₂) hδ').left, },

      -- The rest of the proof follows from specializing hypotheses and manipulating
      -- inequalities to show ≤ ε.
      specialize h_snorm1 s hs hμs,
      have hε2_sum_eq_ε : ennreal{ε / 2} + ennreal{ε / 2} ≤ ennreal{ε},
      { exact two_halves_le_sum hε, },
      have h_indicator_n₀ : ( ∫_{s}_|f n - g|dμ ) ≤ ennreal{ε / 2},
      { exact le_trans (snorm_indicator_le (f n - g)) hn₀, },
      exact le_trans (add_le_add h_snorm1 h_indicator_n₀) hε2_sum_eq_ε, },
    exact le_trans h_snorm_le h_snorm_sum_le_ε, },
end

/-- This theorem is the forward direction of the Vitali's theorem. -/
theorem tendsto_L1_of_unif_integr_of_tendsto_in_μ
{m : measurable_space X} {μ : measure X} [is_finite_measure μ]
{ f : ℕ → X → ℝ } { g : X → ℝ } (hf : ∀ n, (f n) ∈_L1{μ}) (hg : g ∈_L1{μ})
(h_tendsto_μ :  f -→ g in_measure{μ}) (h_unif : unif_integrable f 1 μ) :
f -→ g in_L1{μ} :=
begin
    -- We want to show convergence in L1 by proving that every subsequence of
    -- ∫|fₙ - f|dμ has a convergent subsequence.
    apply tendsto_of_subseq_tendsto,
    intros ns hns,
    -- First we need to deduce that any subsequence of f converges to g in measure.
    have hns_tendsto_μ : (λ i , f (ns i)) -→ g in_measure{μ},
    { intros ε hε,
      specialize h_tendsto_μ ε hε,
      exact h_tendsto_μ.comp hns, }, -- Here we compose the filters.

    -- Now we use the proposition that convergence in measure implies existence
    -- of a subsequence which converges μ-ae
    have h_ae : ∃ (Λ : ℕ → ℕ), strict_mono Λ  ∧ (λ (i : ℕ), f (ns (Λ i)) ) -→ g {μ}_a-e,
    {exact tendsto_in_measure.exists_seq_tendsto_ae hns_tendsto_μ, },
    rcases h_ae with ⟨Λ, hΛ, h_tendsto_ae⟩,
    use Λ,

    -- In order to apply the tendsto_Lp_of_tendsto_ae we need to show that still
    -- along the subsequence ns ∘ Λ all functions are ae_strongly_measurable.
    have hf2Λ : ∀ (n : ℕ), ae_strongly_measurable (f (ns (Λ n))) μ,
    { intro n, exact (hf (ns (Λ n))).left, },

    -- We also need to know that the new sub-family of F={fₙ | n ∈ ℕ} has
    -- uniformly absolutely continuous integrals.
    have h_unif_Λ : unif_integrable (λ n, f (ns (Λ n))) 1 μ,
    { intros ε hε,
      specialize h_unif hε,
      rcases h_unif with ⟨δ, hδ, hδ_snorm⟩,
      use δ,
      split,
      { exact hδ, },
      { intros n s hs hμs,
        exact hδ_snorm (ns (Λ n)) s hs hμs, }, },
    exact tendsto_Lp_of_tendsto_ae μ (le_refl 1) ennreal.one_ne_top hf2Λ hg h_unif_Λ h_tendsto_ae,
end

/-- This is a special case of the Vitali's theorem in L1. -/
theorem vitali_theorem {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
(f : ℕ → X → ℝ) (g : X → ℝ) (hf : ∀ (n : ℕ), (f n) ∈_L1{μ}) (hg : g ∈_L1{μ}) :
f -→ g in_measure{μ} ∧ unif_integrable f 1 μ ↔ f -→ g in_L1{μ} :=
begin
  split,
  { rintro ⟨h_tendsto_μ , h_unif_int⟩,
    exact tendsto_L1_of_unif_integr_of_tendsto_in_μ hf hg h_tendsto_μ  h_unif_int, },
  { intro h_tendsto_L1,
    split,
    { exact tendsto_in_measure_of_tendsto_L1 hf hg h_tendsto_L1 },
    { exact unif_integrable_of_tendsto_L1 hf hg h_tendsto_L1, }, },
end
