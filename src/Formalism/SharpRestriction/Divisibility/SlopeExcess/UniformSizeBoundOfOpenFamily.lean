import Mathlib
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.NormDecompositionCondOfJetConsequence
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLbud
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.BasicNotions Formalism.MainNotions


theorem top2c2_dlSize (eps : ℝ) (Fm : FamP eps) : J.DlSize Fm := by
  unfold J.DlSize
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx1 i
  obtain ⟨-, -, -, -, -, h, -⟩ := hQD
  exact h


end Formalism.MainNotions.DIV.Proofs
