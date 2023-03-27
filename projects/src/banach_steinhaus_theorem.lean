import analysis.normed.group.basic
import analysis.normed_space.operator_norm
import tactic



/- In order to formulate the Banach-Steinhaus theorem, we need two normed spaces
   X and Y, we assume they are over two fields 𝔽₁, 𝔽₂ respectively. We also need
   a ring homomorphism between 𝔽₁ and 𝔽₂ and the fact that it is an isometric
   homomorphism to be able to talk about linear operators from X to Y-/
variables {X Y 𝔽₁ 𝔽₂ : Type*}
[seminormed_add_comm_group X] [seminormed_add_comm_group Y]
[nontrivially_normed_field 𝔽₁] [nontrivially_normed_field 𝔽₂]
[normed_space 𝔽₁ X] [normed_space 𝔽₂ Y]
{σ : 𝔽₁ →+* 𝔽₂} [ring_hom_isometric σ]


theorem banach_steinhaus_theorem {l : Type*} [complete_space X] {f : l → (X →SL[σ] Y)}
  (h: ∀ x, ∃ K, ∀ (i : l), ‖f i x‖ ≤ K): ∃ K', ∀ i, ‖f i‖ ≤ K' :=
begin
  sorry,
end

