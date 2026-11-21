import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCoordinatesBoundedRise

section
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
end

section
noncomputable section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E
open scoped ENNReal Pointwise
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace GlobalTheory.CompanionTheory.Growth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem size_facts (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (∀ C : Set (GA E n), IsCompact C → ∃ r, ∀ g ∈ C, logSize g ≤ r) ∧ (∀ g : GA E n, 0 ≤ logSize g) ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∀ g h : GA E n, logSize (g * h) ≤ logSize g + logSize h + c := by
  obtain ⟨h1, h2, -, c, hc⟩ := GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin
    GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E n
  exact ⟨h1, h2, max c 0, le_max_right _ _, fun g h =>
    (hc g h).trans (add_le_add le_rfl (le_max_left _ _))⟩

def ratP (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) :
    GL (Fin a) E × GL (Fin b) E →* ratH E a b := ((ratGL E a).prodMap (ratGL E b)).rangeRestrict

theorem toRationalSubgroup_surjective : Function.Surjective (ratP E a b) := MonoidHom.rangeRestrict_surjective _

instance countable_ratH : Countable (ratH E a b) := by
  have : Countable E := by
    exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ E |>.trans (by simp)) |> Cardinal.mk_le_aleph0_iff.1
  have h : Countable (GL (Fin a) E × GL (Fin b) E) := by
    have hh : ∀ n : ℕ, Countable (GL (Fin n) E) := fun n =>
      haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
      Function.Injective.countable (f := fun g : GL (Fin n) E => (g.val : Matrix (Fin n) (Fin n) E))
        Units.val_injective
    exact @instCountableProd _ _ (hh a) (hh b)
  exact (toRationalSubgroup_surjective (E := E) (a := a) (b := b)).countable

end GlobalTheory.CompanionTheory.Growth
end
end
