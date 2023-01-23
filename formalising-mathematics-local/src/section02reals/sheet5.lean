/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet3 -- import the definition of `tends_to` from a previous sheet

-- you can maybe do this one now
theorem tends_to_neg {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n, - a n) (-t) :=
begin
  rw tends_to at *,
  have h : ∀ n, |a n - t| = | -a n - -t|,
  intro,
  ring,
  rw abs_sub_comm,
  rw add_comm,
  ring,
  simpa [h] using ha,
end

/-
`tends_to_add` is quite a challenge. In a few weeks' time I'll
show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/

-- Solution from the lectures
theorem tends_to_add_lectures {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n + b n) (t + u) :=
begin
  -- We can abuse definitional equality,
  intros ε hε,
  specialize ha (ε/2) (half_pos hε),
  specialize hb (ε/2) (half_pos hε),
  cases ha with  A hA,
  cases hb with  B hB,
  use (max A B),
  intros n hn,
  rw max_le_iff at hn,
  specialize hA n,
  specialize hB n,
  specialize hA hn.1,
  specialize hB hn.2,
  simp,
  rw abs_lt at *,
  split;
  linarith,
  -- You lose marks if you have two goals and don't indicate it with {} {}
end

theorem tends_to_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n + b n) (t + u) :=
begin
  rw tends_to at *,
  have h1 : ∀ n, |a n + b n - (t + u)| = |(a n - t) + (b n - u) | :=
  begin
    intro,
    ring_nf,
  end,
  simp [h1],
  have h2 : ∀ n, |(a n - t) + (b n - u) | ≤ |a n - t| + |b n - u| :=
  begin
    intro,
    exact abs_add (a n - t) (b n - u),
  end,
  intros ε hε,
  have h3 : ∃ (B : ℕ), ∀ (n : ℕ), B ≤ n → |a n - t| < ε / 2 :=
  begin
    apply ha,
    exact half_pos hε,
  end,
  have h4 : ∃ (B : ℕ), ∀ (n : ℕ), B ≤ n → |b n - u| < ε / 2 :=
  begin
    apply hb,
    exact half_pos hε,
  end,
  have h5 : ∀ (n : ℕ), |b n - u| < ε / 2 ∧ |a n - t| < ε / 2 → |a n - t| + |b n - u| < ε :=
  begin
    intro,
    intro h5,
    cases h5,
    linarith,
  end,
  cases h3,
  cases h4,
  use max h3_w h4_w,
  intro,
  intro h7,
  have h8: h3_w ≤ n ∧ h4_w ≤ n,
  rw max_le_iff at h7,
  exact h7,
  have h10 : ∀ (n : ℕ), |a n - t| + |b n - u| < ε -> |a n - t + (b n - u)| < ε  :=
  begin
    intro,
    intro h9,
    specialize h2 n_1,
    linarith,
  end,
  specialize h10 n,
  apply h10,
  specialize h5 n,
  apply h5,
  split,
  {
    specialize h4_h n,
    apply h4_h,
    cases h8,
    exact h8_right,
  },
  {
    specialize h3_h n,
    apply h3_h,
    cases h8,
    exact h8_left,
  },
end

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tends_to_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n - b n) (t - u) :=
begin
  -- this one follows without too much trouble from earlier results.
  apply tends_to_add,
  { exact ha, },
  {
    apply tends_to_neg,
    exact hb,
  },

end

theorem tends_to_sub_short {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n - b n) (t - u) :=
tends_to_add ha (tends_to_neg hb)
