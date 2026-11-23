module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ChangeDifferentiableOn
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetMulStrictLowerEqOne
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetOfBlockTriangularInjective
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableAtAdjugate
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralImageLeConst
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeOfSection
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetBorSat
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeasureClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kapGG_holds : KapGGStatement (E := E) :=
  GlobalTheory.UnitriJac.kapGG_of_det GlobalTheory.det_conj_strictLower GlobalTheory.det_mul_strictLower_eq_one

theorem measInv_holds : MeasInvStatement (E := E) :=
  GlobalTheory.measInv_of_jacobian kapGG_holds GlobalTheory.NormFactor.nfac_transform

theorem frameMeas_holds : FrameMeasStatement (E := E) :=
  GlobalTheory.FrameMeas.frameMeas_of_local measInv_holds
    (GlobalTheory.frame_measure_local GlobalTheory.FrameSplit.frameSplit)

theorem extF_holds : ExtFStatement (E := E) :=
  extF_of lu_holds frameMeas_holds

theorem measure_statements :
    (KapGGStatement (E := E)) ∧ (MeasInvStatement (E := E)) ∧ (FrameMeasStatement (E := E)) ∧
      (ExtFStatement (E := E)) :=
  ⟨kapGG_holds, measInv_holds, frameMeas_holds, extF_holds⟩

end GlobalTheory.FrameMeasureClosed
