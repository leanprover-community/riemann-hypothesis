module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaCharHalfPeriodEqZeroIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke


theorem _root_.GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add : ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  first | exact @GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff | exact GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff | (intros; apply GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff <;> assumption)
