import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.WeilBound.CoreStatements.IdealCycleValues.CycNumRenameVariables
import BuildAid.ForwardExisting

section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_rename : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) :=
  BaseChangeColon.cycNum_rename_variables

end GlobalTheory.CompanionTheory.Ar.Num
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cycle_number_rename : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.numbers_rename
