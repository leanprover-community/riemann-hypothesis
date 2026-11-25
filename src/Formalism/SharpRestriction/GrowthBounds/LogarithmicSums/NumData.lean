module

public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

theorem ev_const (c α : ℝ) (hα : 0 < α) : ∀ᶠ x : ℝ in atTop, c ≤ Real.exp (x ^ α) := by
  filter_upwards [(tendsto_rpow_atTop hα).eventually_ge_atTop c] with x hx
  linarith [Real.add_one_le_exp (x ^ α)]

def rE (eps : ℝ) : ℕ := ⌈8 * (2 + 8 * eps + 2) / eps⌉₊ + 1

end Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

end
