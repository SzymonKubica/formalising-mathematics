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
∃ (x₀ : X) (r : ℝ), 0 < r ∧  ∃ K' ≥ 0, ∀ (i : l) x ∈ metric.ball x₀ r, ‖f i x‖ ≤ K' :=
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
  { ext,                                 -- Proving equality by set extensionality.
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
  refine ⟨x₀, ⟨r, ⟨gt.lt hr, ⟨k₀, ⟨nat.cast_nonneg k₀, _⟩⟩⟩⟩⟩,

  intros i x hx, -- We take arbitrary fᵢ and x inside of the ball
  have hxAk : x ∈ (A k₀), from interior_subset (hball hx),
  rw mem_Inter at hxAk, -- We unwrap what it means to belong to an intersection of set.
  exact hxAk i, -- We obtain the bound precisely from the definition of Aₖ₀.
end

-- The following lemma is used in the main body of the proof, it shows that if we
-- have a ball Bᵣ(x₀) and we consider a point which is moved r/2 away from the centre
-- x₀ in the direction x, then the point still lies inside of the ball. It looks
-- trivial, however dealing with those kinds of arithmetic manipulations is a bit
-- tricky in Lean.
lemma point_in_ball {r : ℝ} {x₀ x : X} (hr: (0 : ℝ) < r) (hx: x ≠ 0) :
(x₀ + (r / ((2 : ℝ) * ‖x‖)) • x) ∈ metric.ball x₀ r
:=
begin
  rw [metric.mem_ball,    -- Unwrap the definition of being contained in a ball,
      dist_self_add_left, -- simplify dist(a + b, a) = ‖b‖,
      norm_smul,          -- use absolute homogeneity of the norm,
      div_eq_mul_inv,     -- replace division by (2*‖x‖) with multiplication by its inverse,
      mul_inv_rev,        -- arithmetic manipulation: inverse of a product is a product of inverses,
      real.norm_eq_abs,   -- replace the norm on real numbers by the absolute value,
      abs_mul,            -- use |a * b| = |a| * |b|
      -- The following line lets us drop the absolute value around ‖x‖⁻¹ * 2⁻¹ given
      -- that the product is non-negative.
      abs_eq_self.mpr (mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (inv_nonneg.mpr (le_of_lt two_pos)))],

  -- Now we need to simplify the complicated expression:
  -- |r| * (‖x‖⁻¹ * 2⁻¹) * ‖x‖ < r
  conv {
    to_lhs,                                            -- |r| * (‖x‖⁻¹ * 2⁻¹) * ‖x‖ =
    conv { find (‖x‖⁻¹ * _) {rw mul_comm, }},          -- |r| * (2⁻¹ * ‖x‖⁻¹) * ‖x‖ =
    conv { rw mul_assoc, congr,                        -- |r| * (2⁻¹ * ‖x‖⁻¹ * ‖x‖) =
           rw abs_eq_self.mpr (le_of_lt hr), skip,     --   r * (2⁻¹ * ‖x‖⁻¹ * ‖x‖) =
           rw mul_assoc,                               --   r * 2⁻¹ * (‖x‖⁻¹ * ‖x‖) =
           rw inv_mul_cancel (norm_ne_zero_iff.mpr hx),--              r * 2⁻¹ * 1  =
           rw mul_one, skip, },                        --                   r * 2⁻¹ =
    rw ← div_eq_mul_inv, },                            --                       r / 2

  -- We are left with r / 2 < r which linarith can solve given hr : 0 < r.
  linarith,
end

/-
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
        { exact ne_of_gt hr,
-/

lemma scale_add_zero_rescale {x : X } (x₀ : X) {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) :
x = ((2 * ‖x‖) / r) • (x₀ + ((r / (2 * ‖x‖)) • x) - x₀) :=
by conv begin
  to_rhs,
  find (x₀ + _ - x₀) { -- RHS = (2 * ‖x‖) / r) • (x₀ + ((r / (2 * ‖x‖)) • x) - x₀)
    rw [add_comm,      --     = (2 * ‖x‖) / r) • (((r / (2 * ‖x‖)) • x) + x₀ - x₀)
        add_sub_assoc, --     = (2 * ‖x‖) / r) • (((r / (2 * ‖x‖)) • x) + (x₀ - x₀))
        sub_self,      --     = (2 * ‖x‖) / r) • (((r / (2 * ‖x‖)) • x) + 0)
        add_zero], },  --     = (2 * ‖x‖) / r) • (((r / (2 * ‖x‖)) • x))
  rw [smul_smul,       --     = ((2 * ‖x‖) / r) * (r / (2 * ‖x‖))) • x
      div_eq_mul_inv,
      div_eq_mul_inv,
      mul_assoc],

  conv { congr, congr, skip,
         rw [← mul_assoc,
             inv_mul_cancel (ne_of_gt (gt.lt hr)),
             one_mul] },

  conv { congr,
         rw mul_inv_cancel (mul_ne_zero two_ne_zero (norm_ne_zero_iff.mpr hx)), },
  rw one_smul,
end


theorem banach_steinhaus_theorem {l : Type*} [complete_space X] {f : l → (X →SL[ring_hom.id ℝ] Y)}
  (h: ∀ x, ∃ K, ∀ (i : l), ‖f i x‖ ≤ K): ∃ K', ∀ i, ‖f i‖ ≤ K' :=
begin
  /- Define a family of functions to which we'll apply the lemma. -/
  set F : l → X → ℝ := λ i, (λ x, ‖f i x‖) with hF,
  have h_cont: ∀ (i : l), continuous (F i),
    -- For each i the composition of the norm and the continuous (f i) is continuous.
    from λ i, continuous.norm (continuous_linear_map.continuous (f i)),

  have hF: ∀ x, ∃ K, ∀ (i : l), ‖F i x‖ ≤ K,
  { intro x, -- let x be arbitrary
    rcases (h x) with ⟨K, hK⟩, -- get K such that ∀ i ‖(f i) x‖ ≤ K
    -- now use that K and the fact that ‖F i x‖ = ‖ ‖(f i) x‖ ‖ =  ‖(f i) x‖ ≤ K
    exact ⟨K, λ i, le_trans (le_of_eq (norm_norm ((f i) x))) (hK i)⟩, },

  /- We get a ball B(x₀, r) from the lemma. -/
  obtain ⟨x₀, ⟨r, hr, ⟨K', hK', hBound⟩⟩⟩ := uniform_bounded_of_cont_of_bounded_pointwise h_cont hF,
  -- The bounding constant that we'll use is: K'' := 4K'/r.
  use 2 * 2 * K' / r,
  intro i,
  specialize hBound i,
  -- Here we use the proposition that if we control the norm ‖(f i) x‖ for all
  -- x then we control the operator norm of (f i). Before we can apply it however,
  -- we need to ensure that our bound is non-negative.
  have hBoundNonneg : 0 ≤ 2 * 2 * K' / r,
  from div_nonneg (mul_nonneg (le_of_lt (mul_pos two_pos two_pos)) (ge.le hK')) (le_of_lt hr),

  -- Once that precondition is satisfied we can apply the proposition.
  apply continuous_linear_map.op_norm_le_bound (f i) hBoundNonneg,
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
          { specialize hBound (x₀ + (r / (2 * ‖x‖)) • x),
            have hinBall: (x₀ + (r / (2 * ‖x‖)) • x) ∈ metric.ball x₀ r,
            { exact point_in_ball hr h},
            specialize hBound hinBall,
            change (F i) (x₀ + (r / (2 * ‖x‖)) • x) ≤ K',
            change ‖‖(f i) (x₀ + (r / (2 * ‖x‖)) • x) ‖ ‖ ≤ K' at hBound,
            rw norm_norm at hBound,
            change (F i) (x₀ + (r / (2 * ‖x‖)) • x) ≤ K' at hBound,
            exact hBound, },
          have h2: ‖ (f i) x₀ ‖ ≤ K',
          { specialize hBound x₀ (metric.mem_ball_self hr),
            change ‖ ‖ (f i) x₀ ‖‖ ≤ K' at hBound,
            rw norm_norm at hBound,
            exact hBound, },
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

