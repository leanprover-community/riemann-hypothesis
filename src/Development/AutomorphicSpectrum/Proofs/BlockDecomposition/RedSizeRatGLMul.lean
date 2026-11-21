import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCoordinatesBoundedRise
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.Desc
open GroundTheory.Automorphic.Reduction (adelicBorel maxCompact posIdele diagUnits)
open scoped ENNReal
attribute [local instance] borelH

noncomputable section
namespace GlobalTheory.CompanionTheory.PiVec

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem logSize_nonneg_cm {n : ℕ} (g : GA E n) : 0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)


theorem bddBelow_sizes {n : ℕ} (g : GA E n) :
    BddBelow (Set.range fun γ : GL (Fin n) E => logSize (ratGL E n γ * g)) :=
  ⟨0, by rintro _ ⟨γ, rfl⟩; exact logSize_nonneg_cm _⟩

theorem redSize_nonneg {n : ℕ} (g : GA E n) : 0 ≤ redSize g :=
  le_ciInf fun _ => logSize_nonneg_cm _

theorem redSize_le {n : ℕ} (g : GA E n) : redSize g ≤ logSize g := by
  have h := ciInf_le (bddBelow_sizes g) (1 : GL (Fin n) E)
  simp only [map_one, one_mul] at h
  exact h



end GlobalTheory.CompanionTheory.PiVec
end
