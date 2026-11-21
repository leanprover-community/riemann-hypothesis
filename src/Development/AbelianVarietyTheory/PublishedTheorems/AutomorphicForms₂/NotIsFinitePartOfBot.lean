import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2AutomorphicCharacter

noncomputable section

open NumberField MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IdeleCovolume
open scoped InnerProductSpace

namespace GlobalTheory.CuspRep.CuspidalL2GL.SpecModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exists_scalar {G K : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {ρ : G →* (K →L[ℂ] K)} (hu : GlobalTheory.OpTrace.IsUnitaryRep ρ) (hc : ∀ g h : G, g * h = h * g)
    {H : Submodule ℂ K} (hi : IsIrredSubrep ρ H) (g : G) : ∃ c : ℂ, ∀ F ∈ H, ρ g F = c • F := by
  have hπ := isIrrUnitary_rep hu hi
  have := hπ.complete
  have h1 : ContinuousLinearMap.id ℂ H ∈ homIn hi.1.rep hi.1.rep ⊤ := mem_homIn_top.2 fun _ _ => rfl
  have hT : hi.1.rep g ∈ homIn hi.1.rep hi.1.rep ⊤ := mem_homIn_top.2 fun k x =>
    DFunLike.congr_fun ((map_mul hi.1.rep g k).symm.trans ((congrArg _ (hc g k)).trans (map_mul hi.1.rep k g))) x
  refine ⟨be (hi.1.rep g) (.id ℂ H), fun F hF => congrArg Subtype.val
    (show hi.1.rep g ⟨F, hF⟩ = be (hi.1.rep g) (.id ℂ H) • ⟨F, hF⟩ from ext_inner_left ℂ fun y => ?_)⟩
  exact (inner_eq_be hπ hπ.unitary hT h1 _ y).trans (inner_smul_right _ _ _).symm


theorem finiteDimensional_zero (μ : Measure (GA E 0)) [μ.IsHaarMeasure] :
    FiniteDimensional ℂ (L2 (latticeGL E 0) μ) := by
  have : Subsingleton (Quot (latticeGL E 0)) := ⟨fun p q => Quotient.inductionOn₂ p q fun x y => by
    rw [Subsingleton.elim x y]⟩
  refine FiniteDimensional.of_injective (V₂ := ℂ) (K := ℂ)
    { toFun := fun F : L2 (latticeGL E 0) μ => lift (latticeGL E 0) F 1
      map_add' := fun F F' => ?_
      map_smul' := fun c F => ?_ } fun F F' e => l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (.of_forall fun x => by rw [Subsingleton.elim x 1]; exact e)
  · obtain ⟨x, hx⟩ := (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')).exists
    rw [Subsingleton.elim x 1] at hx
    exact hx
  · obtain ⟨x, hx⟩ := (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)).exists
    rw [Subsingleton.elim x 1] at hx
    exact hx







end GlobalTheory.CuspRep.CuspidalL2GL.SpecModel

end
