/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet5 -- import a bunch of previous stuff

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in a solutions video,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/


/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tends_to_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : tends_to a t) :
  tends_to (λ n, 37 * a n) (37 * t) :=
begin
  rw tends_to at *,
  have h2: ∀ (n : ℕ), | 37 * a n - 37 * t | = 37 * | a n - t | :=
  begin
    intro n,
    rw <- mul_sub 37 (a n) t,
    rw abs_mul,
    have h1: (0: ℝ) ≤ 37,
    linarith,
    simp,
    left,
    exact h1,
  end,
  intros ε hε,
  specialize h (ε / 37),
  have h3: (ε / 37) > 0 :=
  begin
    linarith,
  end,
  specialize h h3,
  cases h,
  use h_w,
  intro n,
  specialize h_h n,
  specialize h2 n,
  intro h4,
  rw h2,
  specialize h_h h4,
  rw lt_div_iff at h_h,
  rw mul_comm at h_h,
  exact h_h,
  linarith,
end


/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tends_to_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tends_to a t)
  {c : ℝ} (hc : 0 < c) : tends_to (λ n, c * a n) (c * t) :=
begin
  rw tends_to at *,
  have h3: ∀ (n : ℕ), | c * a n - c * t | = c * | a n - t | :=
  begin
    intro n,
    rw <- mul_sub c (a n) t,
    rw abs_mul,
    simp,
    left,
    linarith,
  end,
  intros ε hε,
  specialize h (ε / c),
  have h2: ε / c > 0,
  rw gt_iff_lt at *,
  apply div_pos,
  exact hε,
  exact hc,
  specialize h h2,
  have h4: ∀ (n : ℕ), c * | a n - t | < ε ↔  | a n - t | < ε / c:=
  begin
    intro n,
    rw lt_div_iff,
    rw mul_comm,
    exact hc,
  end,
  cases h,
  use h_w,
  intro n,
  intro hN,
  specialize h3 n,
  specialize h4 n,
  specialize h_h n,
  rw h3,
  rw h4,
  apply h_h,
  exact hN,
end

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tends_to_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tends_to a t)
  {c : ℝ} (hc : c < 0) : tends_to (λ n, c * a n) (c * t) :=
begin
  rw tends_to at *,
  have h3: ∀ (n : ℕ), | c * a n - c * t | = (- c) * | a n - t | :=
  begin
    intro n,
    rw <- mul_sub c (a n) t,
    rw abs_mul,
    have h4: |c| = -c :=
    begin
      rw abs_eq_neg_self,
      linarith,
    end,
    rw h4,
  end,
  intros ε hε,
  specialize h (ε / (- c)),
  have h2: ε / (- c) > 0,
  rw gt_iff_lt at *,
  apply div_pos,
  exact hε,
  simp,
  exact hc,
  specialize h h2,
  have h4: ∀ (n : ℕ), (-c) * | a n - t | < ε ↔  | a n - t | < ε / (-c):=
  begin
    intro n,
    rw lt_div_iff,
    rw mul_comm,
    simp,
    exact hc,
  end,
  cases h,
  use h_w,
  intro n,
  intro hN,
  specialize h3 n,
  specialize h4 n,
  specialize h_h n,
  rw h3,
  rw h4,
  apply h_h,
  exact hN,
end

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/

lemma deMorgan (P : Prop) (Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,
  { intro h,
    split,
    { intro hP,
      apply h,
      left,
      exact hP },
    { intro hQ,
      apply h,
      right,
      exact hQ } },
  { rintro ⟨hnP, hnQ⟩ (hP | hQ),
    { apply hnP, exact hP },
    { exact hnQ hQ } }
end


theorem tends_to_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tends_to a t) :
  tends_to (λ n, c * a n) (c * t) :=
begin
  have h1: (c < 0) ∨ (c ≥ 0) :=
  begin
    by_contra,
    rw deMorgan at h,
    cases h,
    linarith,
  end,
  cases h1,
  {
    apply tends_to_neg_const_mul,
    exact h,
    exact h1
  },
  {
    have h1: c = 0 ∨ c > 0 :=
    begin
      by_contra,
      rw deMorgan at h,
      cases h,
      change c = 0 → false at h_left,
      apply h_left,
      linarith,
    end,
    cases h1,
    {
      rw h1_1,
      simp,
      rw tends_to,
      simp,
      intros ε hε,
      use 1,
      intro n,
      intro h5,
      exact hε
    },
    {
      apply tends_to_pos_const_mul,
      exact h,
      linarith,
    },
  },
end

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/


theorem tends_to_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tends_to a t) :
  tends_to (λ n, a n * c) (t * c) :=
begin
  have h1: (λ n, a n * c) = (λ n, c * a n) :=
  begin
  ext,
  rw mul_comm,
  end,
  rw mul_comm,
  rw h1,
  apply tends_to_const_mul,
  exact h,
end

-- another proof of this result, showcasing some tactics
-- which I've not covered yet.
theorem tends_to_neg' {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n, - a n) (-t) :=
begin
  convert tends_to_const_mul (-1) ha, -- read about the `convert` tactic in the course notes!
  { ext, simp }, -- ext is a generic extensionality tactic. Here it's being
                 -- used to deduce that two functions are the same if they take
                 -- the same values everywhere
  { simp },
end

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tends_to_of_tends_to_sub {a b : ℕ → ℝ} {t u : ℝ}
  (h1 : tends_to (λ n, a n - b n) t) (h2 : tends_to b u) :
  tends_to a (t+u) :=
begin
end

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tends_to_sub_lim {a : ℕ → ℝ} {t : ℝ}
  (h : tends_to a t) : tends_to (λ n, a n - t) 0 :=
begin
  sorry,
end

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tends_to_zero_mul_tends_to_zero
  {a b : ℕ → ℝ} (ha : tends_to a 0) (hb : tends_to b 0) :
  tends_to (λ n, a n * b n) 0 :=
begin
  sorry,
end

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tends_to_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : tends_to a t)
  (hb : tends_to b u) : tends_to (λ n, a n * b n) (t * u) :=
begin
  sorry,
end

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tends_to_unique (a : ℕ → ℝ) (s t : ℝ)
  (hs : tends_to a s) (ht : tends_to a t) : s = t :=
begin
  sorry,
end
