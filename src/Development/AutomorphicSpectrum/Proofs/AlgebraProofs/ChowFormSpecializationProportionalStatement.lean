module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChowFormSpecializationProportional
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.chow_form_specialization_proportional : ∀ (n e δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
  (v : Fin e × Fin n → ℂ) (P : Finset (Fin n → ℂ)) (u₀ : Fin n → ℂ),
  IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (∀ x ∈ P, x ≠ 0 ∧ (∀ q ∈ W, eval x q = 0) ∧ ∀ i, ∑ j, v (i, j) * x j = 0) →
  (∀ x ∈ P, ∀ x' ∈ P, ∀ t : ℂ, x' = t • x → x' = x) →
  P.card = δ → eval (consGroup u₀ v) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u v) g = c * ∏ x ∈ P, ∑ j, u j * x j := by
  exact @GlobalTheory.CompanionTheory.Relay.chow_form_specialization_proportional
