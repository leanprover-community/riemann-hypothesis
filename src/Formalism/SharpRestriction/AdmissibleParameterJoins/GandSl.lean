import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
import Formalism.SharpRestriction.GlobalTheoremInputs

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}






def ExcSplit (L : SizeData₂ D) : Prop :=
  ∀ u p, p.Prime → Formalism.MainNotions.LocalQuadraticParts.Exc L u p → p = D.host.d ∨ ¬ InertK D p


theorem sc_a_pos (s : Scale) : 1 < s.a := by
  have hx := s.one_lt_alt
  have hb : 1 ≤ s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  unfold Scale.a
  nlinarith




end Formalism.MainNotions.J

end
