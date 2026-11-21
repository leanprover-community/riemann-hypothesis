import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVolMt
import BuildAid.ForwardExisting

section
noncomputable section

namespace GlobalTheory.GaugeKExists

theorem gaugeK : PI.RhsWLim.W.GaugeK := by
  intro k r _
  exact ⟨Formalism.L2.SG.Pf.GV.nu0 k r, Formalism.L2.SG.Pf.GV.gauge_measure_is_gauge⟩

end GlobalTheory.GaugeKExists
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure : PI.RhsWLim.W.GaugeK := by
  atlas_forward_decl GlobalTheory.GaugeKExists.gaugeK
