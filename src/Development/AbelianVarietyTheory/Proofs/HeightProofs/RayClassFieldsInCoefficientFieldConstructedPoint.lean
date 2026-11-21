import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem rayClassFields_in_coefficients : ∀ (K : Ctx) (β : BPt K), β.Is RayPosition → RayRec β.D β.O.ex.nch := by
  intro K β h
  obtain ⟨X, f, T, c, Y, hY, p, _, _, _, _, _, _, _, _, _⟩ := β
  change RayRec X.toD7 c.O.nch at h
  rw [← hY] at h
  exact h

end GlobalTheory.PlugPt
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint : ∀ (K : Ctx) (β : BPt K), β.Is RayPosition → RayRec β.D β.O.ex.nch := by
  atlas_forward_decl GlobalTheory.PlugPt.rayClassFields_in_coefficients
