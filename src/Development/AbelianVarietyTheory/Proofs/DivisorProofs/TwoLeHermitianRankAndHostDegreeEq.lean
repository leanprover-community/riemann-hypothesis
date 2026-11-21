import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.RankHostFacts

theorem two_le_r_and_fdeg (D : D7) : 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  refine ⟨Formalism.L2.Geo.two_le_r D, ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg
  rw [Formalism.L2.Pj.hostSize_finrank D]
  omega

theorem main : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f :=
  two_le_r_and_fdeg

end GlobalTheory.RankHostFacts
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  atlas_forward_decl GlobalTheory.RankHostFacts.main
