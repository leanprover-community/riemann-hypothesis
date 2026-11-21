import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSym

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem psi_real (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) :
    ∃ Λ : Ainf D.host.F →+ ℂ, Continuous Λ ∧ ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1) := by
  obtain ⟨⟨θ, hθ⟩, hall⟩ := hψ.2
  have hf := hall θ hθ
  let Λ : Ainf D.host.F →+ ℂ :=
    { toFun := fun y => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := fun y y' => by simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]; ring }
  refine ⟨Λ, ?_, fun z hz => ?_⟩
  · show Continuous fun y => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E))
    exact continuous_const.mul (continuous_finset_sum _ fun ρ _ => (hθ ρ).2)
  · have hz' : z = pairA D.host.F z.1 0 := Prod.ext rfl hz
    rw [hz']
    exact hf z.1


end Formalism.IndefR.Eqv

end
