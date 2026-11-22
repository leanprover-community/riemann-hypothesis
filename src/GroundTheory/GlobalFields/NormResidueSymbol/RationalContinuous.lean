module

public import Mathlib
public import GroundTheory.GlobalFields.NormResidueSymbol.Rational

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField Topology
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

def unitsPadicHomeomorph : (Π q : Nat.Primes, ℤ_[q])ˣ ≃ₜ* ℤ̂ˣ :=
  unitsContinuousMulEquiv padicEquiv.symm.toMulEquiv continuous_ofPadics continuous_toPadics

theorem unitPart_eq (x : IdeleClassGroup ℚ) :
    unitPart x = unitsPadicHomeomorph (RationalIdeles.ideleClassGroupEquiv x).2 :=
  Units.ext rfl

theorem continuous_unitPart : Continuous unitPart := by
  have h : (unitPart : IdeleClassGroup ℚ → ℤ̂ˣ) =
      unitsPadicHomeomorph ∘ Prod.snd ∘ RationalIdeles.ideleClassGroupEquiv :=
    funext unitPart_eq
  rw [h]
  exact unitsPadicHomeomorph.continuous.comp
    (continuous_snd.comp RationalIdeles.ideleClassGroupEquiv.continuous)

end RationalSymbol

end

end GroundTheory.Global
