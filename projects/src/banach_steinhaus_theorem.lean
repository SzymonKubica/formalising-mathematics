import analysis.normed.group.basic
import analysis.normed_space.operator_norm
import topology.metric_space.baire
import tactic


open normed_space
open set

/- In order to formulate the Banach-Steinhaus theorem, we need two normed spaces
   X and Y. In my implementation I decided to assume that those vector spaces
   are over ℝ. That was because a part of the proof involves complex manipulation
   on x ∈ X : x = 2/r *(x₀ + r/2 * x/‖x‖ - x₀) and for that to work I needed to
   ensure that the scalars that I have in my vector spaces are in ℝ, otherwise
   I wasn't able to multiply x ∈ X by r ∈ R using scalar multiplication. -/
variables {X Y : Type*}
[normed_add_comm_group X] [normed_add_comm_group Y]
[normed_space ℝ X] [normed_space ℝ Y]

/- The following lemma needs to be proven first and then Banach-Steinhaus follows
   from it as a corollary. Given a family of continuous functions from a complete
   space X to ℝ which are bounded pointwise, we can find a ball Bᵣ(x₀) such that
   the family is uniformly bounded on that ball. -/
theorem uniform_bounded_of_cont_of_bounded_pointwise {l : Type*} [complete_space X]
{f : l → (X → ℝ)} (h_cont : ∀ (i : l), continuous (f i)) (h: ∀ x, ∃ K, ∀ (i : l), ‖f i x‖ ≤ K) :
∃ (x₀ : X) (r : ℝ), 0 < r ∧  ∃ K', ∀ (i : l) x ∈ metric.ball x₀ r, ‖f i x‖ ≤ K' :=
begin
  /- We define a sequence of sets (Aₖ) such that on the k-th set for all i ∈ l
     the norm of fᵢ is bounded by k on that set. -/
  set A : ℕ → set X := λ n, (⋂ i : l, { x : X | ‖(f i) x‖ ≤ n }) with hA,
  /- In order to apply the Baire category theorem, we need two things:
     →  ∀ k ∈ ℕ, Aₖ is closed
     →  the infinite union of Aₖ covers the whole space X -/
  have hA_closed : ∀ n : ℕ, is_closed (A n),
  { intro n,
    -- A set which is an intersection is closed if all intersected sets are closed.
    -- And the set defined as a set of points satisfying f x ≤ g x is closed if
    -- both f and g are continuous.
    exact is_closed_Inter (λ i, is_closed_le (continuous.norm (h_cont i)) continuous_const), },
  have hA_union : (⋃ n : ℕ, (A n)) = univ,
  { ext, -- Proving equality by set extensionality.
    refine ⟨λ hx, mem_univ x, _⟩,        -- First deal with the trivial forward inclusion.
    cases h x with k hk,                 -- Find the bound which works for x,
    obtain ⟨k', hk'⟩ := exists_nat_ge k, -- Find a natural number greater than the bound k.
    -- Conclude that x is a member of the union because there exists a set which
    -- is a part of that union such that x belongs to it.
    exact λ hx, mem_Union.mpr ⟨k', mem_Inter.mpr (λ i, le_trans (hk i)  hk')⟩, },
  /- Now we can apply the Baire Category theorem -/
  rcases nonempty_interior_of_Union_of_closed hA_closed hA_union with ⟨k₀, x₀, hx₀⟩,
  /- Now that we have found a k such that the interior of Aₖ is nonempty, we can
     pick a point inside of it and get the ball around it. -/
  have hBall: ∃ δ > 0, metric.ball x₀ δ ⊆ interior (A k₀),
    from (metric.is_open_iff.mp is_open_interior) x₀ hx₀,
  rcases hBall with ⟨r, hr, hball⟩, -- Extract the radius r and hypothesis 0 < r from hBall

  -- Avoids having to repeatedly invoke 'use' tactic, it fills in x₀, r, k₀ into
  -- their corresponding ∃ statements.
  refine ⟨x₀, r, ⟨gt.lt hr, ⟨k₀, _⟩⟩⟩,

  intros i x hx, -- We take arbitrary fᵢ and x inside of the ball
  have hxAk : x ∈ (A k₀), from interior_subset (hball hx),
  rw mem_Inter at hxAk, -- We unwrap what it means to belong to an intersection of set.
  exact hxAk i, -- We obtain the bound precisely from the definition of Aₖ₀.
end

lemma point_in_ball {r : ℝ} {x₀ x : X} (hr: (0 : ℝ) < r) (hx: x ≠ 0) : (x₀ + (r / ((2 : ℝ) * ‖x‖)) • x) ∈ metric.ball x₀ r
:=
begin
  rw metric.mem_ball,
  simp,
  rw norm_smul,
  rw div_eq_mul_inv,
  simp,
  rw mul_comm (‖x‖⁻¹) (2⁻¹),
  rw ← mul_assoc (|r|) (2⁻¹) (‖x‖⁻¹),
  rw mul_assoc,
  rw inv_mul_cancel (norm_ne_zero_iff.mpr hx),
  simp,
  rw abs_eq_self.mpr (le_of_lt hr),
  rw ← div_eq_mul_inv,
  rw div_lt_iff,
  { linarith, },
  { exact two_pos, },
end


#check continuous_linear_map.op_norm_le_bound

theorem banach_steinhaus_theorem {l : Type*} [complete_space X] {f : l → (X →SL[ring_hom.id ℝ] Y)}
  (h: ∀ x, ∃ K, ∀ (i : l), ‖f i x‖ ≤ K): ∃ K', ∀ i, ‖f i‖ ≤ K' :=
begin
  /- Define a family of functions to which we'll apply the uniform boundedness principle. -/
  set F : l → X → ℝ := λ i, (λ x, ‖f i x‖) with hF,
  have h_cont: ∀ (i : l), continuous (F i),
  { intro i,
    rw hF,
    simp,
    apply continuous.norm,
    exact continuous_linear_map.continuous (f i),
  },
  have hF: ∀ x, ∃ K, ∀ (i : l), ‖F i x‖ ≤ K,
  { intro x,
    specialize h x,
    rcases h with ⟨K, hK⟩,
    use K,
    intro i,
    specialize hK i,
    rw hF,
    simp,
    exact hK, },
  /- We get a ball B(x₀, r) from uniform boundedness_principle. -/
  obtain ⟨x₀, ⟨r, hr, ⟨K', hK'⟩⟩⟩ := uniform_bounded_of_cont_of_bounded_pointwise h_cont hF,
  use 2 * 2 * K' / r, -- we probably need to use some better bound.
  intro i,
  specialize hK' i,
  apply continuous_linear_map.op_norm_le_bound,
  { specialize hK' x₀,
    apply div_nonneg,
    { have h4pos: (0 : ℝ) < 2 * 2, { simp, },
      exact mul_nonneg (le_of_lt h4pos) (le_trans (norm_nonneg (F i x₀)) (hK' (metric.mem_ball_self hr))), },
    { exact le_of_lt hr, }, },
  { intro x,
    by_cases x ≠ 0,
    {
      have hx: x = ((2 * ‖x‖) / r) • (x₀ + ((r / (2 * ‖x‖)) • x) - x₀),
      { simp,
        rw smul_smul,
        rw div_eq_mul_inv,
        rw div_eq_mul_inv,
        rw mul_assoc,
        rw ← mul_assoc r⁻¹ r,
        rw inv_mul_cancel,
        { simp,
        rw mul_assoc,
        rw ← mul_assoc (‖x‖) (‖x‖⁻¹) (2⁻¹),
        rw mul_inv_cancel,
        simp,
        exact norm_ne_zero_iff.mpr h},
        { exact ne_of_gt hr, }, },
      nth_rewrite 0 hx,
      rw continuous_linear_map.map_smulₛₗ (f i) (2 * ‖x‖ / r),
      rw norm_smul,
      rw ring_hom.id_apply,
      rw real.norm_eq_abs,
      have hpos : 0 ≤  (2 * ‖x‖) / r,
      { apply div_nonneg,
        { exact mul_nonneg (le_of_lt two_pos) (norm_nonneg x), },
        { exact le_of_lt hr, }, },
      rw abs_of_nonneg hpos,
      rw continuous_linear_map.map_sub,
      rw div_eq_inv_mul,
      rw mul_assoc,
      rw div_eq_inv_mul (2 * 2 * K') r,
      rw mul_assoc (r⁻¹) (2 * 2 * K'),
      rw mul_le_mul_left (inv_pos_of_pos hr),
      rw mul_assoc,
      rw mul_assoc 2 2 K',
      rw mul_assoc 2 (2 * K'),
      rw mul_le_mul_left,
      { rw mul_comm 2 K',
        rw mul_assoc,
        rw mul_comm K' (2 * ‖x‖),
        rw mul_comm 2 (‖x‖),
        rw mul_assoc (‖x‖) 2 K',
        rw mul_le_mul_left,
        { { have h1: ‖ (f i) (x₀ + (r / (2 * ‖x‖)) • x) ‖ ≤ K',
          { specialize hK' (x₀ + (r / (2 * ‖x‖)) • x),
            have hinBall: (x₀ + (r / (2 * ‖x‖)) • x) ∈ metric.ball x₀ r,
            { exact point_in_ball hr h},
            specialize hK' hinBall,
            change (F i) (x₀ + (r / (2 * ‖x‖)) • x) ≤ K',
            change ‖‖(f i) (x₀ + (r / (2 * ‖x‖)) • x) ‖ ‖ ≤ K' at hK',
            rw norm_norm at hK',
            change (F i) (x₀ + (r / (2 * ‖x‖)) • x) ≤ K' at hK',
            exact hK', },
          have h2: ‖ (f i) x₀ ‖ ≤ K',
          { specialize hK' x₀ (metric.mem_ball_self hr),
            change ‖ ‖ (f i) x₀ ‖‖ ≤ K' at hK',
            rw norm_norm at hK',
            exact hK', },
          have h3: ‖ (f i) (x₀ + (r / (‖x‖ * 2)) • x) - (f i) x₀ ‖ ≤ ‖ (f i) (x₀ + (r / (2 * ‖x‖)) • x) ‖ + ‖ (f i) x₀ ‖,
          { rw mul_comm (‖x‖) 2, exact norm_sub_le ((f i) (x₀ + (r / (2 * ‖x‖)) • x)) ((f i) x₀), },
          have h4: K' + K'  ≤  2 * K',
          { rw ← mul_two,
            rw mul_comm,},
          exact le_trans h3 (le_trans (add_le_add h1 h2) h4),},},
        { exact norm_pos_iff.mpr h, }, },
      { exact two_pos }, },
    { push_neg at h,
      have hf0 : (f i) x = 0,
      {
      rw h,
      exact continuous_linear_map.map_zero (f i), },
      rw hf0,
      rw h,
      simp, }, },
end

