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
∀ ε > 0, ∃ δ > 0, ∀ (x y : ℝ), |x - y| < δ → |f x - f y| < ε


theorem intermediate_value_theorem (a b : ℝ ) (h0: a < b) (f : ℝ  → ℝ) (h: continuous f) :
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
        {
          rw <- Icc_def,
          split;
          linarith,
        },
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
    sorry,
  end,
  have hlt: f x ≤ c :=
  begin
    sorry,
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


