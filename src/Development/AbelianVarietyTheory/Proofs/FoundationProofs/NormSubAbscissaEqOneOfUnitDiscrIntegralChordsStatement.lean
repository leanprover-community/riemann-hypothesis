module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubAbscissaEqOneOfUnitDiscrIntegralChords
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.norm_sub_abscissa_eq_one_of_unitDiscr_integral_chords : ∀ {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x₁ y₁ x₂ y₂ m m' : ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.Δ‖ = 1 → W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ → ‖x₁‖ ≤ 1 → ‖x₂‖ ≤ 1 → x₁ ≠ x₂ → m * (x₁ - x₂) = y₁ - y₂ → m' * (x₁ - x₂) = y₁ - W.toAffine.negY x₂ y₂ → ‖m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖x₁ - x₂‖ = 1 := by
  first | exact @GlobalTheory.ThetaPar.norm_sub_x_eq_one | exact GlobalTheory.ThetaPar.norm_sub_x_eq_one | (intros; apply GlobalTheory.ThetaPar.norm_sub_x_eq_one <;> assumption)
