import Mathlib
import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open NumberField IsDedekindDomain MeasureTheory

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace Parabolic

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  {π : Representation ℂ (GL (Fin n) F) V} {π' : Representation ℂ (GL (Fin n) F) V'}

theorem IsSupercuspidal.of_equiv (h : IsSupercuspidal π) (e : π.Equiv π') : IsSupercuspidal π' := by
  intro γ hγ
  haveI := h γ hγ
  have hsurj : Function.Surjective (jacquetMap F n γ e.toIntertwiningMap) := by
    intro x
    obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    refine ⟨Representation.Coinvariants.mk _ (e.toLinearEquiv.symm a), ?_⟩
    rw [jacquetMap_mk]
    congr 1
    exact e.toLinearEquiv.apply_symm_apply a
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  rw [Subsingleton.elim a b]


end Parabolic

namespace AutomorphicForm

open CuspidalSpectrum Parabolic

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

namespace CuspidalAutomorphicRepresentation

variable (π : CuspidalAutomorphicRepresentation K n)

def IsSupercuspidalAt (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ D : AdelicDecomposition π.toModule, IsSupercuspidal (D.finite.π v)


variable {μ : Measure (Reduction.normOneGL K n)} [μ.IsHaarMeasure]


end CuspidalAutomorphicRepresentation

end AutomorphicForm

end

end GroundTheory.Automorphic
