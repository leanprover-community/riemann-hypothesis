module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.GaugeExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryGroupWbDensityChartStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarFormStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasureStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptoticStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupGaugeVolumeInHermitianUnitaryStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ChartJac
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PhiDiff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWLimOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.RankOneChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI

theorem rhsWLim_of_leaves (hD : HaarDens) (hQ : HypQ) (hC : HypChart) (hK : GaugeK) (hV : GaugeVolUk)
    (hT : TubeLimK) (hR : OrbRepY) : Formalism.L2.SG.Pf.WB.RhsWLim := by
  have hL : PI.RhsWLim.RhsWLim :=
    rhsWLim_of mBaseMem tBallMeas (gaugeExists_of_dens hD) (rhsHaar_of (rhsWInv_of_hypQ hQ)) haarUniq
      (constVal_of_orbit (orbitPush_of hV hK hT (hypInv_of lebInvB (coneForm_of hypTh coneVol)) hR
        (hypLocal_of chartJac hC hermitianDefectAdd) opEMeas hypLF))
  exact fun k r z z' μW μW' a a' μsec hW => hL k r z z' μW μW' a a' μsec
    ⟨hW.k_pos, hW.z_mem, hW.z'_mem, hW.T_pos, hW.T'_pos, hW.haarW, hW.haarW', hW.a_pos, hW.a'_pos, hW.massW,
      hW.massW', hW.sec⟩

theorem rhsWLim : Formalism.L2.SG.Pf.WB.RhsWLim :=
  rhsWLim_of_leaves GlobalTheory.T.haar_unitaryGroupWb_density_chart GlobalTheory.T.hyperboloid_invariant_measure_polar_form GlobalTheory.T.hyperboloid_chart_measure_formula GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure GlobalTheory.T.unitaryGroup_gaugeVolume_in_hermitianUnitary GlobalTheory.T.stabilizerTube_gaugeMass_asymptotic GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation

instance : Fact (Formalism.L2.SG.Pf.WB.RhsWLim) := ⟨rhsWLim⟩

end GlobalTheory.RankOneChart
