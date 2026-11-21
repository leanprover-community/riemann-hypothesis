import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes

section
noncomputable section

namespace GlobalTheory.LowTypeRestriction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DeterminedByLowTypes : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ →
    (∀ τ, lowT M τ ≠ ⊥) → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ,
      (∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) → T = 0

theorem resInj_of_determined (h : DeterminedByLowTypes) : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj :=
  fun D _ _ _ _ _ _ _ _ _ _ R hθ i U hU hv =>
    h D _ _ (R.MW i _) R.θ hθ (lowT_ne_bot _) _ _ U hU hv

end GlobalTheory.LowTypeRestriction

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → (∀ τ, lowT M τ ≠ ⊥) → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, (∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) → T = 0 := by
  first | exact @GlobalTheory.LowTypeDetermined.eq_zero_of_lowT | exact GlobalTheory.LowTypeDetermined.eq_zero_of_lowT | (intros; apply GlobalTheory.LowTypeDetermined.eq_zero_of_lowT <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.LowTypeRestriction

theorem determinedByLowTypes : DeterminedByLowTypes := GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes

theorem resInj : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj := resInj_of_determined determinedByLowTypes

end GlobalTheory.LowTypeRestriction

end
end
