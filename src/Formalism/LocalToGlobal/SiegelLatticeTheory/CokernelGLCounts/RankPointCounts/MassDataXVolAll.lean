module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXColumns
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXMasses
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataLevelS
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.SG.Pf.MassDataX

theorem massDataVolAll_of (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.MassDataVolAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  refine ⟨PI.VolStabS.MassDataS.inVolumesAt_of_SWS hSW _ _ _ _ _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · first
      | apply level_s_at_instance
  · apply inMassesAt_holds
  · apply inColumnsAt_holds
  · apply _root_.local_indices_at_instance

end Formalism.L2.SG.Pf.MassDataX
