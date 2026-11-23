module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffNormLeOneOfIsogenySeriesIdentities
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.coeffNormLeOne_of_isogeny_series_identities : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (e h S f : PowerSeries ℂ_[p]) (x₀ x₁ : ℂ_[p]) (y : Fin k → ℂ_[p]) (y' : Fin (2 * k) → ℂ_[p]), IntSer e → PowerSeries.constantCoeff e = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖((2 * k : ℕ) : ℂ_[p])‖ < 1 → PowerSeries.constantCoeff S = 1 → PowerSeries.constantCoeff f = 1 → f ^ 2 = S * lineSer e x₀ → (PowerSeries.subst h f : PowerSeries ℂ_[p]) = S ^ k * ∏ i, lineSer e (y i) → (PowerSeries.subst h (S * lineSer e x₁) : PowerSeries ℂ_[p]) = S ^ (2 * k) * ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → (∃ j, y' j = x₀) → (∃ j, y' j = x₁) → x₀ ≠ x₁ → IntSer f ∧ ‖x₀‖ ≤ 1 := by
  first | exact @GlobalTheory.EvenTheta.intSer_of_isogeny_identities | exact GlobalTheory.EvenTheta.intSer_of_isogeny_identities | (intros; apply GlobalTheory.EvenTheta.intSer_of_isogeny_identities <;> assumption)
