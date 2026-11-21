import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolution

namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

section WeakAdjLemmas

variable {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem weakAdj_zero (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) : WeakAdj ι t 0 0 := by
  intro g
  simp

theorem WeakAdj.add {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f + f') (w + w') := by
  intro g
  rw [inner_add_right, inner_add_right, h g, h' g]

theorem WeakAdj.smul {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f : H₂} {w : H₁}
    (h : WeakAdj ι t f w) (a : ℂ) : WeakAdj ι t (a • f) (a • w) := by
  intro g
  rw [inner_smul_right, inner_smul_right, h g]

theorem WeakAdj.sub {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f - f') (w - w') := by
  intro g
  rw [inner_sub_right, inner_sub_right, h g, h' g]

def weakAdjGraph (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) : Submodule ℂ (H₂ × H₁) where
  carrier := {p | WeakAdj ι t p.1 p.2}
  add_mem' := fun ha hb => WeakAdj.add ha hb
  zero_mem' := weakAdj_zero ι t
  smul_mem' := fun a _ hp => WeakAdj.smul hp a

end WeakAdjLemmas

theorem split (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    SplitStatement E H₁ H₂ := by
  intro ι t K hK hrange f w hfw
  haveI : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := K.exists_add_mem_mem_orthogonal f
  have h2 : WeakAdj ι t f₂ 0 := by
    intro g
    rw [inner_zero_right]
    exact Submodule.inner_right_of_mem_orthogonal (hrange (LinearMap.mem_range_self t g)) hf₂
  refine ⟨f₁, f₂, rfl, hf₁, hf₂, ?_, h2⟩
  have h1 := hfw.sub h2
  simpa using h1


end ReciprocityTheory.L2DbarEstimates
