import analysis.normed.group.basic
import analysis.normed_space.operator_norm
import tactic


open normed_space

/- In order to formulate the Banach-Steinhaus theorem, we need two normed spaces
   X and Y, we assume they are over two fields 𝔽₁, 𝔽₂ respectively. We also need
   a ring homomorphism between 𝔽₁ and 𝔽₂ and the fact that it is an isometric
   homomorphism to be able to talk about linear operators from X to Y-/
variables {X Y 𝔽₁ 𝔽₂ : Type*}
[seminormed_add_comm_group X] [seminormed_add_comm_group Y]
[nontrivially_normed_field 𝔽₁] [nontrivially_normed_field 𝔽₂]
[normed_space 𝔽₁ X] [normed_space 𝔽₂ Y]
{σ : 𝔽₁ →+* 𝔽₂} [ring_hom_isometric σ]

/- The following theorem needs to be proven first and then Banach-Steinhaus follows
   from it as a corollary. -/
theorem uniform_boundedness_principle {l : Type*}  (f : l → (X → ℝ))
(h: ∀ x, ∃ K, ∀ (i : l), ‖f i x‖ ≤ K) (h_cont : ∀ (i : l), continuous (f i)) :
∃ (x₀ : X) r, 0 < r ∧  ∃ K', ∀ (i : l) x ∈ metric.ball x₀ r, ‖f i x‖ ≤ K' :=
begin
 sorry,
end


#check continuous_linear_map.op_norm_le_bound

theorem banach_steinhaus_theorem {l : Type*} [complete_space X] {f : l → (X →SL[σ] Y)}
  (h: ∀ x, ∃ K, ∀ (i : l), ‖f i x‖ ≤ K): ∃ K', ∀ i, ‖f i‖ ≤ K' :=
begin
  /- Define a family of functions to which we'll apply the uniform boundedness principle. -/
  let F : l → X → ℝ := λ i, (λ x, ‖f i x‖),
  have h_cont: ∀ (i : l), continuous (F i),
  { sorry },
  have hF: ∀ x, ∃ K, ∀ (i : l), ‖F i x‖ ≤ K,
  { sorry },
  /- We get a ball B(x₀, r) from uniform boundedness_principle. -/
  obtain ⟨x₀, ⟨r, hr, ⟨K', hK'⟩⟩⟩ := uniform_boundedness_principle F hF h_cont,
  use K', -- we probably need to use some better bound.
  intro i,
  specialize hK' i,
  apply continuous_linear_map.op_norm_le_bound,
  { specialize hK' x₀,
    exact le_trans (norm_nonneg (F i x₀)) (hK' (metric.mem_ball_self hr)), },
  { intro x,
    have hx : x = (‖x‖ / r) • (x₀ + ((r / ‖x‖) • x)- x₀),
    },
end

