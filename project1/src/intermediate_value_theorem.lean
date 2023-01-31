import tactic
import data.real.basic
import data.set.intervals.basic
import data.set
import order
import logic.basic

-- Makes the set, function, order classes globally available for syntax brevity.
open set
open function
open order

def continuous (f : ℝ → ℝ) : Prop :=
∀ (x : ℝ), ∀ ε > 0, ∃ δ > 0, ∀ (y : ℝ), |x - y| < δ → |f x - f y| < ε

-- The following theorem proves that if a function f is continuous then its
-- reflection along x-axis is also continuous. It will be used int the last part
-- of the proof to achieve the full generality of the statement of IVT.
theorem negation_is_continuous (f : ℝ → ℝ) (h: continuous f) : continuous (-f) :=
begin
 intros x ε hε,
 -- Unwrapping the definition of continuity of f to get the required δ.
 specialize h x ε hε,
 rcases h with ⟨δ, ⟨hδ, hy⟩⟩,
 use δ,
 split,
 { exact hδ },
 { simp,
   intros y hxyδ,
   specialize hy y hxyδ,
   rw abs_sub_comm,
   exact hy },
end

-- The following section contains lemmas which prove useful fundamental operations
-- on sets and interfals and their respective upper bounds. Those lemmas are used
-- in the main proof to make the arguments more concise and speed up the compilation
-- of the body of the main proof.

-- This lemma proves that if we have some upper bound m for the set S, and
-- in the interval (k,m] there are no elements of S, then we can improve the
-- bound for S. It will be used in the proof of the special case of IVT.
lemma no_elems_lt_upper_bound_imp_better_bound (k m : ℝ) (S : set ℝ)
(h0: m ∈ upper_bounds S) (h1 : ∀ x ∈ Ioc k m, x ∉ S) : k ∈ upper_bounds S :=
begin
  intros a ha,
  specialize h1 a,
  by_contra,
  rw not_le at h,
  have hlub: a ∈ Ioc k m,
  { rw <- Ioc_def,       -- Here the left part of the conjunction follows immediately
    exact ⟨h, h0 ha⟩, }, -- whereas the right follows because m is an upper bound for S.
  apply h1,
  exacts [hlub, ha],
end

-- This lemma asserts that any subset of a closed interval [a,b] is bounded above,
-- it is used later to simplify some of the arguments in the special case of the proof.
lemma subset_of_Icc_bdd_above (a b : ℝ) (S: set ℝ) (h0 : S ⊆ Icc a b) : bdd_above S :=
begin
 use b,
 intros y hy,
 specialize h0 hy,
 exact h0.right,
end

-- The following lemma shows that if a set S is a subset of the closed interval
-- [a,b] then its supremum must belong to that interval.
lemma subset_of_Icc_sup_bounds (a b x : ℝ) (S : set ℝ)
(h0: a < b) (h1: a ∈ S) (h2: bdd_above S) (h3: S ⊆ Icc a b) (h4: is_lub S x) :
a ≤ x ∧ x ≤ b :=
begin
    rw is_lub at h4,
    split,
    { cases h4,
      specialize h4_left h1,
      exact h4_left, },
    { apply h4.right,
      intros y hy,
      specialize h3 hy,
      exact h3.right, },
end

-- This lemma is used later to derive a contradition given an element of a set
-- which is greater than an upper bound of that set.
lemma no_elem_gt_upper_bound (a b : ℝ) (S : set ℝ) (h0: b ∈ upper_bounds S) (h1: a ∈ S) (h2: b < a) :
false :=
begin
  specialize h0 h1,
  linarith,
end

-- This lemma proves that if we are given a closed interval [a,b] and a point
-- inside that interval which doesn't lie on either of the endpoints, then in fact
-- the point belongs to the open interval (a,b)
lemma elem_in_Icc_not_at_endpoints_in_Ioo (a b c : ℝ) (h0 : a ≠ c) (h1 : b ≠ c)
(hIcc: c ∈ Icc a b) :  c ∈ Ioo a b :=
begin
  cases hIcc with hac hcb,
  rw <- Ioo_def,
  split,
  { rw lt_iff_le_and_ne,
    exact ⟨hac, h0⟩ },
  { rw lt_iff_le_and_ne,
    rw ne_comm at h1,
    exact ⟨hcb, h1⟩ },
end

lemma neg_elem_reflection_Ioo (a b c: ℝ) (h : c ∈ Ioo a b): (-c) ∈ Ioo (-b) (-a) :=
begin
  split,
    { simp, exact h.right, },
    { simp, exact h.left, },
end



-- The following section contains lemmas involving some elementary arithmetic
-- operations which are a bit difficult to show once the terms in the expressions
-- of the main proof get more complex.

-- Adding a positive constant makes a number bigger.
lemma add_positive_gt_self (a b : ℝ) (h : 0 < b) : a < a + b :=
begin
  simp,
  exact h,
end

-- One can divide both sides of an inequality by a positive constant.
lemma div_lt_iff_mul_pos (a b c : ℝ) (h0: 0 < c): a < c * b → a / c < b :=
begin
  intro h,
  exact (div_lt_iff' h0).mpr h,
end

-- Given two numbers, their minimum is equal to the smaller one.
lemma min_eq_smaller_number (a b : ℝ) (h: a < b): a = min a b :=
begin
  apply eq.symm,
  rw min_eq_iff,
  left,
  split,
  { refl, },
  { linarith, },
end

-- Given two numbers, their maximum is equal to the larger one.
lemma max_eq_larger_number (a b : ℝ) (h: a < b): b = max a b :=
begin
  apply eq.symm,
  rw max_eq_iff,
  right,
  split,
  { refl, },
  { linarith, },
end

-- The following two lemmas deal with the fact that if we are given two numbers
-- a and b, then if c is not equal to either of them, then it won't be equal to
-- neither their min nor their max. It seems obvious, but I've decided to introduce
-- an additional lemma because writing the proofs inline was a bit difficult when
-- operating on more complicated terms such as a, b, and c.

lemma not_eq_min (a b c : ℝ) (h0 : c ≠ a) (h1 : c ≠ b) : min a b ≠ c :=
begin
  by_contra,
  rw min_eq_iff at h,
  cases h,
  { apply h0,
    apply eq.symm,
    exact h.left, },
  { apply h1,
    apply eq.symm,
    exact h.left, },
end

lemma not_eq_max (a b c : ℝ) (h0 : c ≠ a) (h1 : c ≠ b) : max a b ≠ c :=
begin
  by_contra,
  rw max_eq_iff at h,
  cases h,
  { apply h0,
    apply eq.symm,
    exact h.left, },
  { apply h1,
    apply eq.symm,
    exact h.left, },
end

-- One can multiply both sides of an equation by (-1).
lemma neg_one_mul2 (a b : ℝ) (h : a = -b) : (-a) = b :=
begin
  exact neg_eq_iff_neg_eq.mp (eq.symm h),
end

theorem intermediate_value_theorem_special (a b : ℝ) (h0: a < b) (f : ℝ  → ℝ) (hc: continuous f) :
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
     { exact no_elems_lt_upper_bound_imp_better_bound m x S hxlub.left hmS, },

    cases hxlub,
    specialize hxlub_right hmu,
    linarith,
  end,
  use x,
  split,
  { split; linarith },
  { linarith, },
end

theorem intermediate_value_theorem_general (a b : ℝ) (h0: a < b) (f : ℝ  → ℝ) (hc: continuous f) :
∀ (c : ℝ), c ∈ Icc (min (f a) (f b)) (max (f a) (f b)) -> ∃ (x : ℝ), (x ∈ Icc a b) ∧ (f x = c) :=
begin
  intro c,
  by_cases (c = f a ∨ c = f b),
    { cases h,
      repeat { intro hIcc,
        use a,
        split,
        { simp, linarith, },
        { rw h, }, },
      { intro hIcc,
        use b,
        split,
        { simp, linarith, },
        { rw h, }, }, },
    { rw not_or_distrib at h,
      intro hIcc,
      have himp: c ∈ Ioo (min (f a) (f b)) (max (f a) (f b)),
      { have hMin: (min (f a) (f b)) ≠ c,
          { exact not_eq_min (f a) (f b) c h.left h.right, },
        have hMax: (max (f a) (f b)) ≠ c,
          { exact not_eq_max (f a) (f b) c h.left h.right, },
        exact elem_in_Icc_not_at_endpoints_in_Ioo (min (f a) (f b)) (max (f a) (f b)) c hMin hMax hIcc},
      by_cases (f a) < (f b),
      { dedup,
        have hMin: f a = min (f a) (f b),
          { exact min_eq_smaller_number (f a) (f b) h_1 },
        have hMax: f b = max (f a) (f b),
          { exact max_eq_larger_number (f a) (f b) h_1 },
        rw <- hMin at himp,
        rw <- hMax at himp,
        apply intermediate_value_theorem_special a b h0 f hc,
        exact himp,
        },
      { let g := -f,

        have hg : continuous g,
          { exact negation_is_continuous f hc, },

        have hfba : f b < f a,
          { rw not_lt at h,
            by_contra,
            dedup,
            rw not_lt at h_2,
            have h_3: f a = f b,
              { linarith },
            rw h_3 at himp,
            simp at himp,
            exact himp, },

        have hgab : g a < g b,
          { change - (f a) < - (f b),
            simp,
            exact hfba, },

        have hcf: c ∈ Ioo (f b) (f a),
          { have hMin: f b = min (f b) (f a),
              { exact min_eq_smaller_number (f b) (f a) hfba },
            have hMax: f a = max (f b) (f a),
              { exact max_eq_larger_number (f b) (f a) hfba },
            rw min_comm at himp,
            rw max_comm at himp,
            rw <- hMin at himp,
            rw <- hMax at himp,
            exact himp,
          },

        have hcm: -c ∈ Ioo (g a) (g b),
          { exact neg_elem_reflection_Ioo (f b) (f a) c hcf, },
        have hx: ∃ (x : ℝ), x ∈ Icc a b ∧ g x = - c,
          { exact intermediate_value_theorem_special a b h0 g hg (-c) hcm,},

        rcases hx with ⟨x , ⟨ hIcc, hgx ⟩⟩,
        use x,
        split,
        { exact hIcc },
        { have hfx: -(f x) = -c,
            { rw <- hgx, refl, },
          simp at hfx,
          exact hfx,
        },
      },
    },
end
