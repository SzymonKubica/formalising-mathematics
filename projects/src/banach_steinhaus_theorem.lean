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
theorem uniform_bounded_of_cont_of_bounded_pointwise {ι : Type*} [complete_space X]
{f : ι → (X → ℝ)} (h_cont : ∀ (i : ι), continuous (f i)) (h : ∀ x, ∃ K, ∀ (i : ι), ‖f i x‖ ≤ K) :
∃ (x₀ : X) (r : ℝ), 0 < r ∧  ∃ K' ≥ 0, ∀ (i : ι) x ∈ metric.ball x₀ r, ‖f i x‖ ≤ K' :=
begin
  /- We define a sequence of sets (Aₖ) such that on the k-th set for all i ∈ l
     the norm of fᵢ is bounded by k on that set. -/
  set A : ℕ → set X := λ n, (⋂ i : ι, { x : X | ‖(f i) x‖ ≤ n }) with hA,
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
  have hBall : ∃ δ > 0, metric.ball x₀ δ ⊆ interior (A k₀),
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
lemma point_in_ball {r : ℝ} {x₀ x : X} (hr : (0 : ℝ) < r) (hx : x ≠ 0) :
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


/- This lemma is allows us to perform a very specific manipulation on x ∈ X.
   If we scale x by r/(2 * ‖x‖) then add and subtract x₀ and then rescale,
   we still get x. -/
lemma scale_add_zero_rescale {x : X } (x₀ : X) {r : ℝ} (hx : x ≠ 0) (hr : r ≠ 0) :
x = ((2 * ‖x‖) / r) • (x₀ + ((r / (2 * ‖x‖)) • x) - x₀) :=
by conv begin
  to_rhs,
  find (x₀ + _ - x₀) { -- RHS =   (2 * ‖x‖) / r) • (x₀ + ((r / (2 * ‖x‖)) • x) - x₀) =
    rw [add_comm,      --         (2 * ‖x‖) / r) • (((r / (2 * ‖x‖)) • x) + x₀ - x₀) =
        add_sub_assoc, --       (2 * ‖x‖) / r) • (((r / (2 * ‖x‖)) • x) + (x₀ - x₀)) =
        sub_self,      --               (2 * ‖x‖) / r) • (((r / (2 * ‖x‖)) • x) + 0) =
        add_zero], },  --                   (2 * ‖x‖) / r) • (((r / (2 * ‖x‖)) • x)) =
  rw [smul_smul,       --                   (((2 * ‖x‖) / r) * (r / (2 * ‖x‖))) • x  =
      div_eq_mul_inv,  --                (((2 * ‖x‖) * r⁻¹) * (r * (2 * ‖x‖)⁻¹)) • x =
      div_eq_mul_inv,  --                (((2 * ‖x‖) * r⁻¹) * (r * (2 * ‖x‖)⁻¹)) • x =
      mul_assoc],      --                ((2 * ‖x‖) * (r⁻¹ * (r * (2 * ‖x‖)⁻¹))) • x =
  conv { congr, congr, skip,    --                                                   =
         rw [← mul_assoc,       --       ((2 * ‖x‖) * ((r⁻¹ * r) * (2 * ‖x‖)⁻¹)) • x =
             inv_mul_cancel hr, --               ((2 * ‖x‖) * (1 * (2 * ‖x‖)⁻¹)) • x =
             one_mul] },        --                     ((2 * ‖x‖) * (2 * ‖x‖)⁻¹) • x =
  conv { congr,                 --                                             1 • x =
         rw mul_inv_cancel (mul_ne_zero two_ne_zero (norm_ne_zero_iff.mpr hx)), },
  rw one_smul,                  --                                                 = x
end

lemma linear_manipulation (f : X→SL[ring_hom.id ℝ] Y) (x₀ x : X) {β : ℝ} (hβ : β ≠ 0) :
‖ f (β • (x₀ + (β⁻¹ • x) - x₀)) ‖ ≤ |β| * (‖ f (x₀ + β⁻¹ • x) ‖ + ‖ f x₀ ‖) :=
begin
  rw [continuous_linear_map.map_smulₛₗ f  β,
      norm_smul,
      ring_hom.id_apply,
      real.norm_eq_abs,
      continuous_linear_map.map_sub,
      mul_le_mul_left (abs_pos.mpr hβ)],
  exact norm_sub_le (f(x₀ + (β⁻¹ • x))) (f x₀),
end


theorem banach_steinhaus_theorem {ι : Type*} [complete_space X] {f : ι → (X →SL[ring_hom.id ℝ] Y)}
  (h : ∀ x, ∃ K, ∀ (i : ι), ‖f i x‖ ≤ K) : ∃ K', ∀ i, ‖f i‖ ≤ K' :=
begin
  /- Define a family of functions to which we'll apply the lemma. -/
  set F : ι → X → ℝ := λ i, (λ x, ‖f i x‖) with hF,
  have h_cont : ∀ (i : ι), continuous (F i),
    -- For each i the composition of the norm and the continuous (f i) is continuous.
    from λ i, continuous.norm (continuous_linear_map.continuous (f i)),

  have hF : ∀ x, ∃ K, ∀ (i : ι), ‖F i x‖ ≤ K,
  { intro x, -- let x be arbitrary
    rcases (h x) with ⟨K, hK⟩, -- get K such that ∀ i ‖(f i) x‖ ≤ K
    -- now use that K and the fact that ‖F i x‖ = ‖ ‖(f i) x‖ ‖ =  ‖(f i) x‖ ≤ K
    exact ⟨K, λ i, le_of_eq_of_le (norm_norm ((f i) x)) (hK i)⟩, },

  /- We get a ball B(x₀, r) from the lemma. -/
  obtain ⟨x₀, ⟨r, hr, ⟨K', hK', h_bound⟩⟩⟩ := uniform_bounded_of_cont_of_bounded_pointwise h_cont hF,
  -- The bounding constant that we'll use is: K'' := 4K'/r.
  use 2 * 2 * K' / r,
  intro i,
  specialize h_bound i,
  -- Here we use the proposition that if we control the norm ‖(f i) x‖ for all
  -- x then we control the operator norm of (f i). Before we can apply it however,
  -- we need to ensure that our bound is non-negative.
  have h_bound_nonneg : 0 ≤ 2 * 2 * K' / r,
    from div_nonneg
      (mul_nonneg (le_of_lt (mul_pos two_pos two_pos)) (ge.le hK'))
      (le_of_lt hr),

  -- Once that precondition is satisfied we can apply the proposition.
  apply continuous_linear_map.op_norm_le_bound (f i) h_bound_nonneg,
  intro x,
  -- We need to consider cases when x=0 and x≠0 separately because if x is zero
  -- then our manipulation doesn't work as we can't divide by ‖x‖ which is 0.
  by_cases x = 0,
  { -- The case when x = 0 is trivial because by linearity we get 0 ≤ 0 in the end.
    rw [h, continuous_linear_map.map_zero (f i), norm_zero, norm_zero, mul_zero], },
  { -- Here we assume x ≠ 0.
    have hx : x = ((2 * ‖x‖) / r) • (x₀ + ((r / (2 * ‖x‖)) • x) - x₀),
      from scale_add_zero_rescale x₀ h (ne_of_gt (gt.lt hr)),

    /- The idea of the proof is to show that
       ‖fᵢ(x)‖ ≤  (2‖x‖/r)(‖fᵢ(x₀ + (r / (2‖x‖)) • x)‖ + ‖f(x₀)‖) and then we
       bound both of the norms above by K' to deduce that
       ‖fᵢ(x)‖ ≤ (2‖x‖/r)(K' + K') = K''‖x‖ -/

    -- ‖(f i) (x₀ + (r / (2 * ‖x‖)) • x)‖ = ‖‖(f i) (x₀ + (r / (2 * ‖x‖)) • x)‖‖
    -- = ‖(F i) (x₀ + (r / (2 * ‖x‖)) • x)‖ ≤ K' <- as the point is in the ball.
    have h1 : ‖ (f i) (x₀ + (r / (2 * ‖x‖)) • x) ‖ ≤ K',
      from le_of_eq_of_le
        (eq.symm (norm_norm ((f i) (x₀ + (r / (2 * ‖ x ‖)) • x))))
        (h_bound (x₀ + (r / (2 * ‖x‖)) • x) (point_in_ball hr h)),

    -- Again : ‖ (f i) x₀ ‖ = ‖‖ (f i) x₀ ‖‖ = ‖ (F i) x₀ ‖ ≤ K' as x₀ ∈ B.
    have h2 : ‖ (f i) x₀ ‖ ≤ K',
      from le_of_eq_of_le
        (eq.symm (norm_norm ((f i) x₀)))
        (h_bound x₀ (metric.mem_ball_self hr)),

    -- The linear manipulation lemma requires that the constant that we use
    -- for multiplying is not equal to zero, thus we need to first establish
    -- that (2 * ‖x‖) / r ≠ 0.
    have h_ne_zero : (2 * ‖x‖) / r ≠ 0,
      from div_ne_zero
        (mul_ne_zero (two_ne_zero) (norm_ne_zero_iff.mpr h))
        (ne.symm (ne_of_lt hr)),

    -- We also need to know that the constant is non-negative to be able to
    -- drop the absolute value around it.
    have h_nonneg : 0 ≤ (2 * ‖x‖) / r,
      from div_nonneg (mul_nonneg (le_of_lt two_pos) (norm_nonneg x)) (le_of_lt hr),

    -- This hypothesis uses the linear_manipulation lemma and non-negativity of
    -- the (2 * ‖x‖) / r to get the bound on ‖ (f i) x ‖.
    have h5 : ‖ (f i) x ‖ ≤ ((2 * ‖x‖)/r) * (‖ (f i) (x₀ + ((2 * ‖x‖)/r)⁻¹ • x) ‖ + ‖ (f i) x₀ ‖),
    { nth_rewrite 0 hx,
      nth_rewrite 1 ← abs_eq_self.mpr h_nonneg,
      conv { to_lhs, find (r / _) { rw ← inv_div, }},
      exact linear_manipulation (f i) x₀ x (h_ne_zero), },

    -- Use h5 to turn the goal into:
    -- ((2 * ‖x‖)/r) * (‖ (f i) (x₀ + ((2 * ‖x‖)/r)⁻¹ • x) ‖ + ‖ (f i) x₀ ‖) ≤
    -- 2 * 2 * K' / r * ‖ x ‖.
    apply le_trans h5,

    -- Now we need to convert to rearrange multiplications of terms so that
    -- they are on the left side of each side of the inequality. That
    -- way we can later use mul_le_mul_left to strip them off.
    conv
    { conv
      { to_rhs,                          -- Convert RHS:  2 * 2 * K' / r * ‖x‖ =
        rw [mul_assoc, div_eq_mul_inv],        --     2 * (2 * K') * r⁻¹ * ‖x‖ =
        rw [mul_comm, ← mul_assoc, mul_comm],  -- r⁻¹ * (‖x‖ * (2 * (2 * K'))) =
        rw [← mul_assoc, ← mul_assoc],         --     r⁻¹ * ‖x‖ * 2 * (2 * K') =
        find (r⁻¹ * _) { rw mul_comm, },       --     ‖x‖ * r⁻¹ * 2 * (2 * K') =
        find (‖x‖ * r⁻¹ * _) { rw mul_comm, }, --   2 * (‖x‖ * r⁻¹) * (2 * K') =
        rw ← div_eq_mul_inv, },                --       2 * (‖x‖ / r) * (2 * K')
      conv
      { to_lhs, congr,
        rw mul_div_assoc, }, -- Obtains: 2 * (‖x‖ / r) * (‖(f i) ...) on the LHS.

      -- By associativity we get to the final shape 2 * (_) ≤ 2 * (_) and replace
      -- the multiplication by inverse with division as other hypotheses require
      -- that form.
      rw [mul_assoc, mul_assoc, inv_div], },

    -- For some reason I wasn't able to feed two_pos directly into the lemma
    -- mul_le_mul_left to be able to cancel 2 * _ ≤ 2 * _. I think it failed
    -- to fill in the instance variables and writing : 'rw mul_le_mul_left two_pos'
    -- resulted in 5 new goals appearing which required to prove the instance
    -- properties for ℝ which whould have been filled in automatically.
    -- I decided to use work_on_goal 2 to switch the order of goals and supply
    -- the positivity hypotheses straight away. This way the instance variables
    -- are filled in properly.
    rw mul_le_mul_left, work_on_goal 2 { exact two_pos },
    rw mul_le_mul_left, work_on_goal 2 { exact div_pos (norm_pos_iff.mpr h) (hr), },
    exact le_of_le_of_eq (add_le_add h1 h2) (eq.symm (two_mul K')), },
end

-- Now having proven the Banach-Steinhaus theorem in terms of bounding constants,
-- we can state it using suprema and prove it using the previous version.

-- Since we are now dealing with suprema of norms, we need extended non-negative
-- real numbers to be able to describe them.
open ennreal
open_locale ennreal

#check le_supr

theorem banach_steinhaus_supremum {ι : Type*} [complete_space X] {f : ι → (X →SL[ring_hom.id ℝ] Y)}
(h : ∀ x, (⨆ i, ↑‖f i x‖₊) < ∞) : (⨆ i, ↑‖f i‖₊) < ∞ :=
begin
  have h_bound : ∀ (x : X), ∃ (Kₓ : ℝ), ∀ (i : ι), ‖(f i) x‖ ≤ Kₓ,
  { intro x,
    specialize h x,
    rw ennreal.lt_iff_exists_coe at h,
    rcases h with ⟨Kₓ, hKₓ_bound, hKₓ_lt_top⟩,
    refine ⟨Kₓ, (λ i, _)⟩,
    have h_supr: ∀ i : ι, ‖(f i) x‖ ≤  (⨆ i, ‖f i x‖₊),
    { sorry, },
    apply le_trans (h_supr i),
    apply le_of_eq,
    norm_cast,
    rw ← ennreal.coe_eq_coe,
    rw ← hKₓ_bound,
    rw with_top.coe_supr,
    rw bdd_above_def,
    use Kₓ,
    intro c,
    rw mem_range,
    intro h_index,
    cases h_index with j hj,
    rw ← hj,
    apply le_trans (h_supr j),
    rw ← hKₓ_bound,





















  },

  -- We apply the previous version of the theorem to get the bounding constant.
  obtain ⟨K', hK'⟩ := banach_steinhaus_theorem h_bound,

  -- Here the idea of the proof is to show that sup{‖(f i) x‖ | i ∈ ι} ≤ K' < ∞
  -- it is achieved by showing that for all i ∈ ι, ‖(f i) x‖ is bounded by K'
  -- The statement below is complicated because I needed to handle coercions between
  -- K' which is real and the contexts which expect it to be nnreal or ennreal.
  exact lt_of_le_of_lt
    (supr_le (λ i, le_of_eq_of_le'
        (eq.symm (ennreal.of_real_eq_coe_nnreal (le_trans (norm_nonneg (f i)) (hK' i))))
        (coe_le_coe.mpr (hK' i))))
    (ennreal.coe_lt_top),
end
