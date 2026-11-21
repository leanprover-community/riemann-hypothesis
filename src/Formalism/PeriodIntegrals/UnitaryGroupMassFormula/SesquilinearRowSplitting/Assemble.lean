import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.FrameReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SecondDualReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction

section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitRow_of (hc : CoreStep) (ha : AaStep) (ht : TrStep) : PI.SplitRow.SplitRow := by
  intro D u F0 Λ hΛ
  obtain ⟨hg, hF, hX⟩ := hΛ
  exact hc _ _ _ _ _ F0 Λ ⟨hg.1, hF.2.1, hF.2.2.1.1, hF.2.2.2.2,
    hX.trans (Formalism.L2.SG.Saturated.latSpan_aaS D F0).symm,
    fun a => (ha D a).1, fun a => (ha D a).2, ht D⟩

end PI.SRW
end

section
namespace PI.SRW

theorem splitRow_of_iso (hi : IsoStep) : PI.SplitRow.SplitRow :=
  splitRow_of (coreStep_of frame_reduction hi assembly_reduction) adjoint_action_reduction trace_reduction

end PI.SRW
end
