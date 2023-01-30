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

lemma upper_bound_not_lt_sup (a b : ℝ) (S : set ℝ) (h0: is_lub S b) (h1: a < b) :
a ∉ upper_bounds S :=
begin
  by_contra,
  cases h0,
  specialize h0_right h,
  linarith,
end

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
    have h5: x ≠ b,
    { intro h5,
      rw <- h5 at hcfb,
      linarith, },

    have hlt: x < b,
    { rw <- not_le,
      intro hbx,
      apply h5,
      exact antisymm h4.right hbx, },

    simp at hc,
    specialize hc h,
    cases hc with δ hδ,
    cases hδ,
    let y := x + 1 / 2 * (min δ (b - x)),
    specialize hδ_right y,
    have hymx: x < y :=
    begin
      simp,
      split,
      { exact hδ_left },
      { exact hlt },
    end,
    have hy: y ∈ S :=
    begin
      split,
      {
        simp,
        split,
        { linarith },
        {
          have h6: y ≤  x + 1/2 * (b - x) :=
          begin
            simp,
          end,
          linarith,
        },
      },
      {
        have hxy : | x - y | < δ :=
        begin
          simp,
          rw abs_lt,
          split,
          {
            have hmin: 0 < 2⁻¹ * min δ (b - x), {
              rw mul_pos_iff,
              left,
              split,
              { norm_num, },
              { rw lt_min_iff,
                split,
                { exact hδ_left },
                { simp,
                  exact hlt,},
              },
            },
            have hdmin: -δ < 0, {
              simp,
                exact hδ_left,
            },
            exact lt_trans hdmin hmin,
          },
          {
            rw inv_mul_eq_div,
            rw div_lt_iff,
            rw min_lt_iff,
            left,
            linarith,
            norm_num,
          },
        end,
        specialize hδ_right hxy,
        rw abs_lt at hδ_right,
        cases hδ_right,
        simp at hδ_right_left,
        exact hδ_right_left,
      },
    end,
    rw is_lub at hxlub,
    rw upper_bounds at hxlub,
    rw is_least at hxlub,
    cases hxlub,
    specialize hxlub_left hy,
    linarith,
  end,
  have hlt: f x ≤ c :=
  begin
    by_contra,
    specialize hc x,
    specialize hc (f x - c),
    rw not_le at h,
    have h5: x ≠ a :=
    begin
      intro h5,
      rw <- h5 at hfac,
      linarith,
    end,
    simp at hc,
    specialize hc h,
    cases hc with δ hδ,
    cases hδ,
    have hy: ∀ (y : ℝ), | x - y | < δ -> y ∉ S :=
    begin
      intro y,
      specialize hδ_right y,
      intro hxyδ,
      specialize hδ_right hxyδ,
      rw abs_lt at hδ_right,
      cases hδ_right,
      simp at hδ_right_right,
      intro hSy,
      cases hSy,
      linarith,
    end,
    let m := max (x-δ / 2) a,
    have hm : m < x :=
    begin
      simp,
      split,
      { exact div_pos hδ_left two_pos },
      {
        rw lt_iff_not_le,
        intro hxa,
        apply h5,
        exact antisymm hxa h4.left,
      },
    end,
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
    have hmu: m ∈ upper_bounds S :=
    begin
      exact lemma1 m x S hm hxlub.left hmS,
    end,
    rw is_lub at hxlub,
    rw is_least at hxlub,
    rw lower_bounds at hxlub,
    cases hxlub,
    specialize hxlub_right hmu,
    linarith,
  end,
  use x,
  split,
  { split; linarith },
  { linarith, },
end

#lint
