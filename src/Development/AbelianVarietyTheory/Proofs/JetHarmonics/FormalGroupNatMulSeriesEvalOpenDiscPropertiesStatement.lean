module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (F : FormalGroup K), Intg F.toPowerSeries → (∀ n, Intg (nMul F n)) ∧ ∀ x : K, ‖x‖ < 1 → ev1 (nMul F 0) x = 0 ∧ ev1 (nMul F 1) x = x ∧ (∀ j, ‖ev1 (nMul F j) x‖ ≤ ‖x‖ ∧ (‖(j : K)‖ = 1 → ‖ev1 (nMul F j) x‖ = ‖x‖)) ∧ (∀ i j, ev F.toPowerSeries ![ev1 (nMul F i) x, ev1 (nMul F j) x] = ev1 (nMul F (i + j)) x) ∧ (∀ i j, ev1 (nMul F i) (ev1 (nMul F j) x) = ev1 (nMul F (i * j)) x) ∧ (∀ y : K, ‖y‖ < 1 → ev F.toPowerSeries ![0, y] = y ∧ ev F.toPowerSeries ![y, 0] = y) := by
  first | exact @GlobalTheory.ConvSer.nMul_point | exact GlobalTheory.ConvSer.nMul_point | (intros; apply GlobalTheory.ConvSer.nMul_point <;> assumption)
