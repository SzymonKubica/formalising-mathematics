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

/-- I decided to add alias definitions for the two notions of convergence that
    we deal with in the proof. They improve readability at a cost of sometimes
    introducing an additional rewrite step. -/
def tendsto_in_L1 {m : measurable_space X}
(μ : measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
filter.tendsto (λ (n : ℕ), snorm (f n - g) 1 μ) filter.at_top (𝓝 0)

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
theorem sub_strongly_measurable {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
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
(k : ℝ≥0∞) (hk : k ≠ ⊤) (hf : f ∈_L1{μ}) (hg : g ∈_L1{μ}) :
k * snorm (f - g) 1 μ < ⊤ :=
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
    ε⁻¹  * snorm ((f n) - g) 1 μ ,
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
  let a : ℕ → ℝ≥0∞ := λ n, (ennreal{ε})⁻¹ * snorm ((f n) - g) 1 μ,
  let b : ℕ → ℝ≥0∞ := λ n, μ {x : X | ε ≤ dist (f n x) (g x)},

  -- In order to apply the squeeze_zero theorem, we need to show the below:
  have h_b_le_a : ∀ n, b n ≤ a n,
  { intro n,
    have h_set_eq : {x : X | ε ≤ dist (f n x) (g x)} =
                    {x : X | ennreal{ε} ≤ ‖f n x - g x‖₊},
    { exact set_ε_le_dist_eq_set_ε_le_nnorm (f n) g ε },

    -- Here we need to use change to unwrap the definition back and make rw work.
    change μ {x : X | ε ≤ dist (f n x) (g x)} ≤ (ennreal{ε})⁻¹ * snorm ((f n) - g) 1 μ,
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
    change (ennreal{ε})⁻¹ * snorm ((f n) - g) 1 μ < ⊤,
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
  → μ s ≤ ennreal{δ} → snorm (s.indicator (g)) 1 μ ≤ ennreal{ε} :=
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
snorm (s.indicator (f + g)) 1 μ ≤ snorm (s.indicator f) 1 μ + snorm (s.indicator g) 1 μ :=
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
      μ s ≤ ennreal{δ} → snorm (s.indicator (g)) 1 μ ≤ ennreal{ε / 2},
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
    have h_snorm_le : snorm (s.indicator (g + (f n - g))) 1 μ ≤
        snorm (s.indicator g) 1 μ  + snorm (s.indicator (f n - g)) 1 μ,
    { exact snorm_triangle_ineq hg.left (ae_strongly_measurable.sub (hf n).left hg.left) hs, },

    have h_snorm_sum_le_ε : snorm (s.indicator g) 1 μ  + snorm (s.indicator (f n - g)) 1 μ ≤ ennreal{ε},
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
      have h_indicator_n₀ : snorm (s.indicator (f n - g)) 1 μ ≤ ennreal{ε / 2},
      { exact le_trans (snorm_indicator_le (f n - g)) hn₀, },
      exact le_trans (add_le_add h_snorm1 h_indicator_n₀) hε2_sum_eq_ε, },
    exact le_trans h_snorm_le h_snorm_sum_le_ε, },
end

/-- This theorem is the forward direction of the Vitali's theorem. -/
theorem tendsto_L1_of_unif_integr_of_tendsto_in_μ
{m : measurable_space X} {μ : measure X} [is_finite_measure μ]
{ f : ℕ → X → ℝ } { g : X → ℝ } (hf : ∀ (n : ℕ), mem_ℒp (f n) (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ)
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
(f : ℕ → X → ℝ) (g : X → ℝ) (hf : ∀ (n : ℕ), mem_ℒp (f n) (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ) :
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

---------------------------- Appendix -------------------------------------------
-- Initially I tried proving the forward direction of the Vitali theorem by
-- contradiction and some form of a epsilon/3 proof. Unfortunately converting
-- from tendsto filters to ε-δ is not always possible so I had some difficulty
-- with that approac and eventually decided to rethink my approach and prove that
-- statement in a different way. However, leading up to the initial version of the
-- proof, I introduced a number of interesting lemmas and so I decided to include
-- that initial attempt here because I've learned a lot by writing it.

/-- This lemma is used in the forward direction of the theorem. It asserts that
    if fₙ doesn't converge to g in L1 then limsup of ∫|fₙ - g|dμ > 0 -/
lemma limsup_pos_of_not_tendsto_L1 {m : measurable_space X} {μ : measure X}
{f : ℕ → X → ℝ} { g : X → ℝ } (h_not_tendsto : ¬(f -→ g in_L1{μ})) :
limsup (λ n, snorm (f n - g) 1 μ) at_top > 0 :=
begin
  by_contra,
  rw [tendsto_in_L1, not_tendsto_iff_exists_frequently_nmem] at h_not_tendsto,
  have h_contra : limsup (λ n, snorm (f n - g) 1 μ) at_top = 0,
  { sorry, },
  sorry,
end

/-- This lemma allows us to extract a subsequence from a limsup such that it's
    limit is still positive. -/
lemma extract_subseq_of_limsup_pos {V : Type} [has_zero V]
[conditionally_complete_lattice V] [topological_space V]
(f : ℕ → V) {Λ : ℕ → ℕ} (hΛ : strict_mono Λ) (hf : limsup f at_top > 0) :
lim at_top (λ (i : ℕ), f (Λ i)) > 0 :=
begin
 sorry,
end

/-- This lemma allows us to get a δ := min δ₁ δ₂ such that if we get δ₁ from the
    u.a.c.i. statement for g and δ₂ from the statement for {fₙ | n ∈ ℕ} then
    both of the conclusions hold for sets of measure smaller than δ. The lemma
    is a bit specific and was extracted out only to improve the speed of computation
    when checking the main proof. If it were to be used in greater generality,
    one would have to remove the ε/3 and replace it with just ε but then in the
    main proof I would have to do some rearrangements which would slow down
    the compilation -/
lemma extract_δ_uaci {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
{ f : ℕ → X → ℝ } { g : X → ℝ }
(h_f_n_uaci : ∀ (ε : ℝ), ε > 0 →  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ (n : ℕ) s, measurable_set s →
             μ s ≤ ennreal.of_real δ → snorm (s.indicator (f n)) 1 μ ≤ ennreal.of_real (ε / 3))
(h_g_uaci : ∀ (ε : ℝ), ε > 0 →  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s →
           μ s ≤ ennreal.of_real δ → snorm (s.indicator (g)) 1 μ ≤ ennreal.of_real (ε / 3))
: ∀ (ε : ℝ), ε > 0 →  ∃ (δ : ℝ) (hδ : 0 < δ),
  ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  ∀ (n : ℕ), snorm (s.indicator (f n)) 1 μ ≤ ennreal.of_real (ε / 3) ∧
  snorm (s.indicator (g)) 1 μ ≤ ennreal.of_real (ε / 3) :=
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

/-- This lemma states that if we have a ℝ≥0∞ number a then we can find an ε > 0
    such that 0 < ε < a. -/
lemma exists_ε_between_of_pos {a : ℝ≥0∞} (ha : 0 < a) : ∃ (ε : ℝ≥0∞), 0 < ε ∧ ε < a :=
begin
  by_cases a = ⊤,
  { use 1,
    rw h,
    exact ⟨one_pos, ne.lt_top (ennreal.one_ne_top)⟩, },
  { use a / 2,
    have ha0 : a ≠ 0,
      { rw ← ne_zero_iff, exact ne_zero.of_pos ha, },
    split,
    { exact ennreal.half_pos ha0, },
    { rw ennreal.div_lt_iff,
      { nth_rewrite 0 ← mul_one a,
        rw (ennreal.mul_lt_mul_left ha0 h),
        exact ennreal.one_lt_two, },
      { right, exact ha0},
      { right, exact h}, }, },
end

/-- This lemma shows that if we have a finite measure and 0 < ε then
    0 < ε / 3μ(x). -/
lemma ε_div_3_μX_pos {m : measurable_space X} {μ : measure X} [is_finite_measure μ]
{ε : ℝ≥0∞} (hε : 0 < ε) (hε_ne_0 : ε ≠ 0) (hε_ne_top : ε ≠ ⊤) :
ennreal.to_real(ε) / (3 * ennreal.to_real(μ univ) + 1) > 0 :=
begin
    let ε₂ := ennreal.to_real(ε)/(3 * ennreal.to_real(μ univ) + 1),
    have hε2 : 0 < ε₂,
    { have hε2' : 0 < ennreal.to_real(ε),
      { exact ennreal.to_real_pos hε_ne_0 hε_ne_top },
      change 0 < ennreal.to_real(ε)/(3 * ennreal.to_real(μ univ) + 1),
      rw lt_div_iff,
      { simp,
        exact hε2', },
      { have hμ : 0 ≤ 3 * ennreal.to_real(μ univ), { simp, },
        linarith, }, },
    change ε₂ > 0,
    linarith,
end

/-- This theorem is the forward direction of the Vitali's theorem. -/
theorem tendsto_L1_of_unif_integr_of_tendsto_in_μ'
{m : measurable_space X} {μ : measure X} [is_finite_measure μ]
{ f : ℕ → X → ℝ } { g : X → ℝ } (hf : ∀ (n : ℕ), mem_ℒp (f n) (1 : ℝ≥0∞) μ) (hg : mem_ℒp g 1 μ)
(hf2 : ∀ (n : ℕ), strongly_measurable (f n)) (hg2 : strongly_measurable g)
(h_tendsto_μ : tendsto_in_measure μ f at_top g) (h_unif : unif_integrable f 1 μ) :
tendsto_in_L1 μ f g :=
begin
    by_contra,
    -- Here we assume that there is a sequence ns such that along that sequence
    -- lim ∫|fₙ - f|dμ > 0.
    by_cases h1 : ∃ (ns : ℕ → ℕ), strict_mono ns ∧ ¬ tendsto_in_L1 μ (λ i, f (ns i)) g,
    { rcases h1 with ⟨ns, hns, hns_not_tendsto⟩,
      rw tendsto_in_L1 at h,
      -- If fₙ doesn't converge to g in L1 we can deduce that limsup of snorms is > 0.
      have h_limsup : limsup (λ n, snorm (f n - g) 1 μ) at_top > 0,
      { exact limsup_pos_of_not_tendsto_L1 h, },

      -- Show that along ns we get convergence in measure!!! -> new lemma needed.
      -- Now we need to show that along ns it also converges in measure and extract
      -- the desired susequence out of that.
      have hns_tendsto_μ : tendsto_in_measure μ (λ i , f (ns i)) at_top g,
      {sorry,},

      -- Given that fₙ → g in measure, we extract the subsequence along which it
      -- converges μ-ae.
      have h_ae : ∃ (Λ : ℕ → ℕ), strict_mono Λ  ∧
                 ∀ᵐ x ∂μ, tendsto (λ (i : ℕ), f (ns (Λ i)) x) at_top (𝓝 (g x)),
      {exact tendsto_in_measure.exists_seq_tendsto_ae hns_tendsto_μ, },

      rcases h_ae with ⟨Λ, hΛ, h_tendsto_ae⟩,

      -- Then given that limsup we pass down to a subsequence along Λ.
      -- have h_lim_along_Λ : lim at_top (λ (i : ℕ), snorm(f (Λ i) - g) 1 μ) > 0,
      -- { exact extract_subseq_of_limsup_pos (λ (n : ℕ), snorm(f n - g) 1 μ) hΛ h_limsup, },

      -- Idea:
      -- Given that there exists ns such that along it we don't have convergence
      -- in L1, we pass to a subsequence Λ which converges in measure
      -- then from uaci we extract the information we need and after that
      -- we need to show convergence in L1 using a epsilon delta proof.

      -- Given that F has u.a.c.i and so does {g} we want to show that for all ε
      -- we can pick a δ such that for all measurable sets with μ(s) < δ we have
      -- the u.a.c.i condition of ∫ₛ|f|dμ < ε satisifed for all fₙ and g
      have h_uaci : ∀ (ε : ℝ), 0 < ε  →  ∃ (δ : ℝ) (hδ : 0 < δ),
                     ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
                     ∀ (n : ℕ), snorm (s.indicator (f n)) 1 μ ≤ ennreal.of_real (ε / 3) ∧
                       snorm (s.indicator (g)) 1 μ ≤ ennreal.of_real (ε / 3),
      { -- I have moved the hypotheses which the goal depends on below here so that
        -- they don't pollute the infoview.
        -- Now we extract the uniformly abs cont integrals condition from the singleton
        -- set {g} but so that for any ε it gives us the criterion with ε / 3.
        have h_g_uaci : ∀ (ε : ℝ), 0 < ε  →  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s →
                         μ s ≤ ennreal.of_real δ →
                         snorm (s.indicator (g)) 1 μ ≤ ennreal.of_real (ε / 3),
        { intros ε hε,
          have hε3 : 0 < ε / 3, { linarith, },
          exact unif_integrable_singleton hg hε3 },

        -- Now we need to extract a similar proposition from the family F = {fₙ | n ∈ ℕ}.
        have h_f_n_uaci : ∀ (ε : ℝ), 0 < ε →  ∃ (δ : ℝ) (hδ : 0 < δ),
                         ∀ (n : ℕ) s, measurable_set s → μ s ≤ ennreal.of_real δ →
                           snorm (s.indicator (f n)) 1 μ ≤ ennreal.of_real (ε / 3),
        { intros ε hε,
          have hε3 : 0 < ε / 3, { linarith, },
          exact h_unif hε3, },
        exact extract_δ_uaci h_f_n_uaci h_g_uaci, },

      -- Now we need to apply Egorov's theorem to (fₙ) along Λ.
      have h_set_from_Egorov : ∀ (δ : ℝ) , δ > 0 → ∃ s, measurable_set s ∧ μ s ≤ ennreal.of_real δ
                               ∧ tendsto_uniformly_on (λ n, f (ns (Λ n))) g filter.at_top sᶜ,
      { intros δ hδ,
        have hfΛ2 : ∀ n : ℕ, strongly_measurable (f (ns (Λ n))),
        { intro n, exact hf2 (ns (Λ n)) },
        exact tendsto_uniformly_on_of_ae_tendsto' hfΛ2 hg2 h_tendsto_ae hδ, },

      --

      have h_exists_ε : ∃ (ε : ℝ≥0∞), 0 < ε ∧ ε < lim at_top (λ (i : ℕ), snorm(f (Λ i) - g) 1 μ),
      { exact exists_ε_between_of_pos h_lim_along_Λ },

      rcases h_exists_ε with ⟨ε, ⟨hε, hεlt⟩⟩,

      have hε_ne_0 : ε ≠ 0, { rw ← ne_zero_iff, exact ne_zero.of_pos hε },
      have hε_ne_top : ε ≠ ⊤, { exact ne_top_of_lt hεlt },
      specialize h_uaci (ennreal.to_real ε) (ennreal.to_real_pos hε_ne_0 hε_ne_top),

      rcases h_uaci with ⟨δ, hδ, hδ_set⟩,

      specialize h_set_from_Egorov δ hδ,
      rcases h_set_from_Egorov with ⟨s, hs, hμs, hs_tendsto⟩,

      specialize hδ_set s hs hμs,

      rw metric.tendsto_uniformly_on_iff at hs_tendsto,
      specialize hs_tendsto (ennreal.to_real(ε)/(3 * ennreal.to_real(μ univ) + 1)),
      specialize hs_tendsto (ε_div_3_μX_pos hε hε_ne_0 hε_ne_top),

      rw eventually_at_top at hs_tendsto,
      cases hs_tendsto with n₀ hn₀,

      -- Here comes the ε/3 part of the proof.
      have h_bound : ∀ (n : ℕ), n₀ < n → (λ (i : ℕ), snorm (f (Λ i) - g) 1 μ) < ε,
      { sorry },

      have h_contradiction : lim at_top (λ (i : ℕ), snorm (f (Λ i) - g) 1 μ) < ε,
      { sorry, },
      have h_ε_lt_ε : ε < ε,
      { exact lt_trans hεlt h_contradiction },
      have h_irrefl : ¬ ε < ε,
      { exact lt_irrefl ε },
      exact h_irrefl h_ε_lt_ε, },
    { -- For the other case, If no such subsequence exists we can show convergence
      -- in L1 and arrive at a contradiciton.
      apply h,
      rw tendsto_in_L1,
      apply tendsto_of_subseq_tendsto,
      push_neg at h1,
      intros ns hns,
      have h_ns_mono : ∃ (φ : ℕ → ℕ), strict_mono φ ∧ strict_mono (ns ∘ φ),
      { exact strict_mono_subseq_of_tendsto_at_top hns, },
      rcases h_ns_mono with ⟨φ, hφ, hnsφ⟩,
      use φ,
      specialize h1 (ns ∘ φ) hnsφ,
      simp at h1,
      rw tendsto_in_L1 at h1,
      exact h1,
    },

end

end measure_theory
