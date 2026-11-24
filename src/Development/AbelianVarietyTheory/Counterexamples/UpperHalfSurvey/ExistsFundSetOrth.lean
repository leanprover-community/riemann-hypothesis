module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC

@[expose] public section

namespace GlobalTheory.MetricWeightTest

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem exists_fundSet_orth {x0 : Frame X.Ψ r} (ho : IsOrth X x0) : ∃ FF, IsFundSet X x0 FF :=
  fundSet_holds r X x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X)

theorem muF_ne_zero {x0 : Frame X.Ψ r} (ho : IsOrth X x0) : muF X x0 Set.univ ≠ 0 := by
  intro h
  have hae : ∀ᵐ z ∂muF X x0, False := by
    rw [ae_iff]; simpa using h
  unfold muF at hae
  rw [ae_withDensity_iff (OntoC.measurable_densF X x0),
    ae_restrict_iff' (OntoB.isOpen_OmF X x0).measurableSet] at hae
  have h0 : (volume : Measure (V (nd X))) (OmF X x0) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with z hz hzO
    exact hz hzO (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact OntoB.densF_pos hzO)
  exact ((OntoB.isOpen_OmF X x0).measure_pos volume ⟨0, IW.zero_mem_OmF X x0 ho⟩).ne' h0

theorem fundSet_pos {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hF : IsFundSet X x0 FF) : muF X x0 FF ≠ 0 := by
  intro h
  have e := GlobalTheory.Unfold.lintegral_unfold GlobalTheory.FrameMeasureClosed.measInv_holds r X x0 ho FF hF
    (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)
  rw [setLIntegral_measure_zero _ _ h, lintegral_one] at e
  exact muF_ne_zero X ho e

end GlobalTheory.MetricWeightTest
