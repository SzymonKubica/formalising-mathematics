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
(h0: k < m) (h1: m ∈ upper_bounds S) (h2 : ∀ x ∈ Ioc k m, x ∉ S) : k ∈ upper_bounds S :=
begin
  rw upper_bounds,
  intros a ha,
  specialize h2 a,
  by_contra,
  rw not_le at h,
  have h3: a ∈ Ioc k m,
  { rw <- Ioc_def,
    split,
    { exact h },
    { specialize h1 ha,
      exact h1 }, },
  specialize h2 h3,
  apply h2,
  exact ha,
end


theorem intermediate_value_theorem (a b : ℝ ) (h0: a < b) (f : ℝ  → ℝ) (hc: continuous f) :
∀ (c : ℝ), c ∈ Ioo (f a) (f b) -> ∃ (x : ℝ), (x ∈ Icc a b) ∧ (f x = c) :=
begin
  rw continuous at *,
  intro c,
  intro hc,
  rw <- Ioo_def at hc,
  rw mem_def at hc,
  rw set_of_app_iff at hc,
  cases hc with hfa hfb,
  let S: set ℝ := { y : ℝ | y ∈ Icc a b ∧ f y < c },
  have hsc: S.nonempty :=
  begin
   use a,
   rw mem_def,
   split,
   {
     rw <- Icc_def,
     rw mem_def,
     rw set_of_app_iff,
     split;
     linarith,
   },
   { exact hfa },
  end,
  have hba: bdd_above S:=
  begin
    use b,
    intro x,
    intro hx,
    rw mem_def at hx,
    cases hx,
    rw <- Icc_def at hx_left,
    rw mem_def at hx_left,
    rw set_of_app_iff at hx_left,
    exact hx_left.right,
  end,
  have h3: ∃ (x : ℝ), is_lub S x :=
  begin
    apply real.exists_is_lub S hsc hba,
  end,
  cases h3 with x h3h,
  have hx: x = Sup S :=
  begin
    have hSup : is_lub S (Sup S),
    apply real.is_lub_Sup S hsc hba,
    exact is_lub.unique h3h hSup,
  end,

  have h4: a ≤ x ∧ x ≤ b :=
  begin
    split,
    {
      rw hx,
      rw real.le_Sup_iff,
      intros ε hε,
      use a,
      split,
      {
        split,
        { rw <- Icc_def,
          split;
          linarith, },
        { exact hfa },
      },
      { linarith },
      exacts [hba, hsc],
    },
    {
      rw is_lub at h3h,
      have h5: b ∈ upper_bounds S :=
      begin
        rw upper_bounds,
        intros k hk,
        cases hk,
        rw <- Icc_def at hk_left,
        exact hk_left.right,
      end,
      rw is_least at h3h,
      cases h3h,
      rw lower_bounds at h3h_right,
      rw mem_def at h3h_right,
      rw set_of_app_iff at h3h_right,
      specialize h3h_right h5,
      exact h3h_right,
    },
  end,
  have hgt: f x ≥ c :=
  begin
    by_contra,
    specialize hc x,
    specialize hc (c - f x),
    rw not_le at h,
    have h5: x ≠ b :=
    begin
      intro h5,
      rw <- h5 at hfb,
      linarith,
    end,
    have hlt: x < b :=
    begin
      rw <- not_le,
      intro hbx,
      apply h5,
      exact antisymm h4.right hbx,
    end,
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
    rw is_lub at h3h,
    rw upper_bounds at h3h,
    rw is_least at h3h,
    cases h3h,
    specialize h3h_left hy,
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
      rw <- h5 at hfa,
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
    have hmu: m ∈ upper_bounds S :=
    begin
      rw upper_bounds,
      intros k hk,
      by_contra h2,
      rw <- lt_iff_not_le at h2,
      specialize hy k,
      have hxk: | x - k | < δ,
      { rw abs_lt,
        split,
        {
          simp,
          rw is_lub at h3h,
          rw is_least at h3h,
          rw upper_bounds at h3h,
          cases h3h,
          specialize h3h_left hk,
          linarith,
        },
        {
          apply sub_left_lt_of_lt_add,
          rw add_comm,
          apply lt_add_of_sub_left_lt,
          have hmxδ : x - δ < m,
          {
            simp,
            left,
            linarith,
          },
          exact lt_trans hmxδ h2,
        },
      },
      specialize hy hxk,
      apply hy,
      exact hk,
    end,
    rw is_lub at h3h,
    rw is_least at h3h,
    rw lower_bounds at h3h,
    cases h3h,
    specialize h3h_right hmu,
    linarith,
  end,
  use x,
  split,
  {
    split;
    linarith
  },
  {
    linarith,
  },
end

