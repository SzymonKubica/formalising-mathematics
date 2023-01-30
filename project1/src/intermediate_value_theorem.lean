import tactic
import data.real.basic
import data.set.intervals.basic
import data.set
import order

-- Makes the set class globally available for syntax brevity.
open set
open function
open order

def tends_to (a : ℕ → ℝ) (t : ℝ) : Prop :=
∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε


def continuous (f : ℝ → ℝ) : Prop :=
∀ (x : ℝ), ∀ ε > 0, ∃ δ > 0, ∀ (y : ℝ), |x - y| < δ → |f x - f y| < ε


lemma lemma1 (k m : ℝ) (S : set ℝ)
(h0: m ∈ upper_bounds S) (h1 : ∀ x ∈ Ioc k m, x ∉ S) : k ∈ upper_bounds S :=
begin
  rw upper_bounds,
  intros a ha,
  specialize h1 a,
  by_contra,
  rw not_le at h,
  have hlub: a ∈ Ioc k m,
  { rw <- Ioc_def,
    split,
    { exact h },
    { specialize h0 ha,
      exact h0 }, },
  specialize h1 hlub,
  apply h1,
  exact ha,
end

lemma subset_of_Icc_bdd_above (a b : ℝ) (S: set ℝ) (h0 : S ⊆ Icc a b) : bdd_above S :=
begin
 use b,
 intros y hy,
 specialize h0 hy,
 exact h0.right,
end

lemma subset_of_Icc_sup_bounds (a b x : ℝ) (S : set ℝ)
(h0: a < b) (h1: a ∈ S) (h2: bdd_above S) (h3: S ⊆ Icc a b) (h4: is_lub S x) :
a ≤ x ∧ x ≤ b :=
begin
    rw is_lub at h4,
    split,
    {
      cases h4,
      specialize h4_left h1,
      exact h4_left,
    },
    {
      apply h4.right,
      intros y hy,
      specialize h3 hy,
      exact h3.right,
    },
end

lemma add_positive_gt_self (a b : ℝ) (h : 0 < b) : a < a + b :=
begin
  simp,
  exact h,
end

lemma no_elem_gt_upper_bound (a b : ℝ) (S : set ℝ) (h0: b ∈ upper_bounds S) (h1: a ∈ S) (h2: b < a) :
false :=
begin
  specialize h0 h1,
  linarith,
end

lemma div_lt_iff_mul_pos (a b c : ℝ) (h0: 0 < c): a < c * b → a / c < b :=
begin
  intro h,
  exact (div_lt_iff' h0).mpr h,
end

#check two_pos

theorem intermediate_value_theorem (a b : ℝ) (h0: a < b) (f : ℝ  → ℝ) (hc: continuous f) :
∀ (c : ℝ), c ∈ Ioo (f a) (f b) -> ∃ (x : ℝ), (x ∈ Icc a b) ∧ (f x = c) :=
begin
  rw continuous at *,
  intros c hc,
  cases hc with hfac hcfb,

  let S: set ℝ := { y : ℝ | y ∈ Icc a b ∧ f y < c },

  have ha : a ∈ S,
  { split,
    { split; linarith, },
    { exact hfac },
  },

  have hsc: S.nonempty,
  { exact ⟨a, ha⟩ },

  have hSab: S ⊆ Icc a b,
  { intros y hy,
    exact hy.left },

  have hba: bdd_above S,
  { exact subset_of_Icc_bdd_above a b S hSab },

  have hlub: ∃ (x : ℝ), is_lub S x,
  { apply real.exists_is_lub S hsc hba, },

  cases hlub with x hxlub,
  have hx: x = Sup S,
  { exact is_lub.unique hxlub (real.is_lub_Sup S hsc hba), },

  have h4: a ≤ x ∧ x ≤ b,
  { exact subset_of_Icc_sup_bounds a b x S h0 ha hba hSab hxlub, },

  have hgt: f x ≥ c :=
  begin
    by_contra,
    specialize hc x (c - f x),
    rw not_le at h,
    have hlt: x < b,
    { rw <- not_le,
      intro hbx,
      rw antisymm hbx h4.right at hcfb,
      linarith, },

    simp at hc,
    specialize hc h,
    cases hc with δ hδ,
    cases hδ with hδ_pos hδ_imp,
    let dx := (1 / 2) * (min δ (b - x)),
    let y := x + dx,
    have hpos: 0 < dx,
    { simp,
      exacts ⟨hδ_pos, hlt⟩,},
    specialize hδ_imp y,
    have hymx: x < y,
    { exact add_positive_gt_self x dx hpos, },
    have hy: y ∈ S,
    { split,
      { simp,
        split,
        { linarith },
        { have hyle : y ≤ x + (b - x) / 2,
          { simp,
            change (1 / 2) * (min δ (b - x)) ≤ (b - x) / 2,
            simp,
            rw div_eq_inv_mul,
            simp,
          },
          linarith,
        }, },
      {
        have hxy : | x - y | < δ,
        { simp,
          rw abs_lt,
          split,
          { linarith, },
          { change (1 / 2) * (min δ (b - x)) < δ,
            simp,
            rw <- div_eq_inv_mul,
            apply div_lt_iff_mul_pos,
            { exact two_pos, },
            { rw min_lt_iff,
              left,
              linarith, }, }, },

        specialize hδ_imp hxy,
        rw abs_lt at hδ_imp,
        cases hδ_imp,
        simp at hδ_imp_left,
        exact hδ_imp_left,
      },
    },
    exact no_elem_gt_upper_bound y x S hxlub.left hy hymx,
  end,
  have hlt: f x ≤ c :=
  begin
    by_contra,
    specialize hc x (f x - c),
    rw not_le at h,
    simp at hc,
    specialize hc h,
    cases hc with δ hδ,
    cases hδ,
    have hy: ∀ (y : ℝ), | x - y | < δ -> y ∉ S,
    { intro y,
      specialize hδ_right y,
      intro hxyδ,
      specialize hδ_right hxyδ,
      rw abs_lt at hδ_right,
      cases hδ_right,
      simp at hδ_right_right,
      intro hSy,
      cases hSy,
      linarith, },
    let m := max (x-δ / 2) a,
    have hm : m < x,
    { simp,
      split,
      { exact div_pos hδ_left two_pos },
      { rw lt_iff_not_le,
        intro hxa,
        rw antisymm hxa h4.left at hgt,
        linarith, }, },

    have hmS: ∀ y ∈ Ioc m x, y ∉ S,
    { intros y hy2,
      specialize hy y,
      apply hy,
      rw abs_lt,
      split,
      { simp,
        cases hy2,
        linarith, },
      { simp,
        apply sub_lt_comm.mp,
        { cases hy2,
          have hmx: x - δ ≤ m,
          { rw le_max_iff,
            left,
            simp,
            linarith, },
          linarith,
        },
        {exact covariant_add_lt_of_contravariant_add_le ℝ,}
      },
    },
    have hmu: m ∈ upper_bounds S,
     { exact lemma1 m x S hxlub.left hmS, },

    cases hxlub,
    specialize hxlub_right hmu,
    linarith,
  end,
  use x,
  split,
  { split; linarith },
  { linarith, },
end
