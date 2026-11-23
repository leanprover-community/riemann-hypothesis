module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProductExpChartAllRealPlacesLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.lintegral_productExpChart_allRealPlaces_le : ∀ (I : AutInst) (c : InfinitePlace I.F → ℝ) (s : ℝ) (E : InfinitePlace I.F → Fin (I.n ^ 2) → Matrix (Fin I.n) (Fin I.n) ℂ) (Θ : (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ) → I.Ginf), (∀ v, IsGauge (I.ε v) (c v)) → (∀ v i, inG (I.ε v) (E v i)) → (∀ v i j, ((E v i * (E v j)ᴴ).trace).re = if i = j then 1 else 0) → 0 < s → 12 * (I.n : ℝ) ^ 3 * s ≤ 1 → 8 * (I.n : ℝ) ^ 5 * s ≤ 1 → (∀ t v, uMat (Θ t v) = (List.ofFn fun i => NormedSpace.exp ((t v i : ℂ) • E v i)).prod) → ∃ S : Set I.Ginf, MeasurableSet S ∧ (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) ∧ ∀ Φ : I.Ginf → ENNReal, Measurable Φ → ∫⁻ t in Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s), Φ (Θ t) ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) * ∫⁻ y in S, Φ y ∂(muInf I) := by
  first | exact @GlobalTheory.ProductChartAll.lintegral_chart_all_le | exact GlobalTheory.ProductChartAll.lintegral_chart_all_le | (intros; apply GlobalTheory.ProductChartAll.lintegral_chart_all_le <;> assumption)
