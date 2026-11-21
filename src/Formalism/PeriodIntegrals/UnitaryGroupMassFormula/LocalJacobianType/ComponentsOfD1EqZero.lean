import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ChiZeroRight

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

theorem piu_inv_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (piu v)⁻¹ ∉ v.adicCompletionIntegers F := by
  intro h
  have hU : {x : Fv F v | x ≠ 1} ∈ 𝓝 (0 : Fv F v) := isOpen_ne.mem_nhds zero_ne_one
  obtain ⟨k, hk⟩ := (tube v (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v) hU).exists
  have hm : (piu v)⁻¹ ^ k ∈ v.adicCompletionIntegers F := pow_mem h k
  apply hk _ hm
  simp [smul_eq_mul, mul_inv_cancel₀ (pow_ne_zero k (piu_ne v))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem finrank_pos' : 0 < Module.finrank F E := Module.finrank_pos

theorem exists_not_mem_oev : ∃ t0 : Fv F v ⊗[F] E, t0 ∉ OEv (E := E) v := by
  classical
  set i0 : Fin (Module.finrank F E) := ⟨0, finrank_pos'⟩
  set P : Set (Fv F v) := (fun y => trE (E := E) v y i0) '' OEv (E := E) v
  have hP : IsCompact P :=
    (isCompact_oev v).image ((continuous_apply i0).comp (continuous_trE v))
  have hU : (v.adicCompletionIntegers F : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) :=
    (Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _)
  obtain ⟨k, hk⟩ := (tube v hP hU).exists
  refine ⟨(trE (E := E) v).symm (Pi.single i0 (piu v ^ (k + 1))⁻¹), fun h => ?_⟩
  have hp : (piu v ^ (k + 1))⁻¹ ∈ P :=
    ⟨_, h, by simp⟩
  have h2 := hk _ hp
  have e : piu v ^ k • (piu v ^ (k + 1))⁻¹ = (piu v)⁻¹ := by
    have := piu_ne v
    rw [smul_eq_mul, pow_succ]
    field_simp
  rw [e] at h2
  exact piu_inv_not_mem v h2

variable [SecondCountableTopology (Fv F v ⊗[F] E)]


theorem components_of_D1_eq_zero (h : ¬ OpenKer v ψ) : D1 (E := E) v ψ = {0} := by
  ext y
  constructor
  · intro hy
    by_contra hne
    have h1 : trE (E := E) v y ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact hne
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
    apply h (openKer_of v ψ (trE (E := E) v y j) hj fun c hc => ?_)
    have e : c * trE (E := E) v y j =
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c • bas (E := E) v j) * y) := by
      rw [trE_apply, trC_apply, smul_mul_assoc, map_smul, smul_eq_mul]
    rw [e]
    exact hy _ (smul_bas_mem v hc j)
  · intro hy
    rw [Set.mem_singleton_iff.1 hy]
    intro x _
    simp [psiV_zero]


end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
