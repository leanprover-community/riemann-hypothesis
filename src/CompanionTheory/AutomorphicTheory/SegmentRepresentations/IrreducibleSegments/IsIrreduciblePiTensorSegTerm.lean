import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetMultiplicityPosOfSocle

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published

namespace CompanionTheory.Lit1.SegRep

set_option synthInstance.maxHeartbeats 400000 in

def SegmentRepresentationLit : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d l : ℕ), 0 < d → 0 < l → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ Z : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        Z.toSubmodule = ⨆ (S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
            (_ : S.toRepresentation.IsIrreducible), S.toSubmodule ∧
        Z.toRepresentation.IsIrreducible ∧
        HasFiniteLength (jac (consecBlocks l d) Z.toRepresentation) ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
          (τ : Representation ℂ (Levi k (fun _ : Fin l => Fin d)) W), τ.IsIrreducible →
          jhMult τ (jac (consecBlocks l d) Z.toRepresentation) = jhMult τ (piTensor (segTerm σ.ρ l))

end CompanionTheory.Lit1.SegRep

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published

namespace CompanionTheory.Lit1.SegRep.PIrr

theorem isIrreducible_piTensor_segTerm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) :
    (piTensor (segTerm σ.ρ l)).IsIrreducible := by
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _
    (fun a => GlobalTheory.LocGL.isIrreducible_twist σ.irr _) fun a φ hφ => ?_
  refine GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id σ.ρ σ.smooth σ.irr φ fun g x => ?_
  have h := hφ g x
  simp only [segTerm, twist_apply, map_smul] at h
  exact (smul_right_injective _ (Units.ne_zero _)) h

end CompanionTheory.Lit1.SegRep.PIrr

end
end
