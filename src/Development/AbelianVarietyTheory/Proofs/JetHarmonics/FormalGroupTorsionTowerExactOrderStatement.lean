module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupTorsionTowerExactOrder
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

theorem _root_.GlobalTheory.T.formalGroup_torsionTower_exact_order : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → (∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n)) ∧ (∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n)) ∧ ∀ n i j, ev1 (nMul F i) (t n) = ev1 (nMul F j) (t n) ↔ i ≡ j [MOD p ^ n] := by
  first | exact @GlobalTheory.ConvSer.tower_exact_order | exact GlobalTheory.ConvSer.tower_exact_order | (intros; apply GlobalTheory.ConvSer.tower_exact_order <;> assumption)
