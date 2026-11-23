module

public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformRestrictionOfEnergy
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.ThmBFinal
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.StepThmBPinnedCOfN
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformRestrictionOfFiniteEnergy
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChain
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.Pf

namespace Formalism.MainStatements.RowRest

theorem energyFin : EnergyFin := by
  intro D hG X u u' h
  have h1 := (EnergyConvJ.BM.realObj_inInfinityX_jsz CompanionTheory.Lime.BM.uniqGap_holds hG X u u' 1 one_pos).2.2
  rw [realObj_inNuX X u u' 1, h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (MassDataPos.cooOf_pos X u u')).ne'] at h1
  exact ENNReal.ofReal_ne_top (top_le_iff.1 h1)

theorem uniform_restriction_bound : ThmBChain6.AmplitudeBoundsAllChoicesUniform := uniform_restriction_of_finite_energy energyFin

theorem analytic_pinnedTheoremB_uniform : NGAnalytic.StepThmBPinnedC :=
  stepThmBPinnedC_ofN (ThmBChain.theoremB_uniform_rotated CompanionTheory.WaveGrid.weighted_bound_rotated_uniform) CompanionTheory.Lime.BM.ampUnif_holds
    PointUniformity.ptUnif' (rowDataUnifN_of_6 Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds uniform_restriction_bound)

theorem bDat_theoremB_global : BDat.StepThmBG :=
  stepThmBG_ofN (ThmBChain.theoremB_uniform_rotated CompanionTheory.WaveGrid.weighted_bound_rotated_uniform) CompanionTheory.Lime.BM.ampUnif_holds
    PointUniformity.ptUnifG (rowDataUnifN_of_6 Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds uniform_restriction_bound)

end Formalism.MainStatements.RowRest
