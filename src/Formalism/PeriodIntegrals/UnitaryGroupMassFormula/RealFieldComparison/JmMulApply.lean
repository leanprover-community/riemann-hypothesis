module

public import Formalism.PeriodIntegrals.AdBridgeSteps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace PI.UnitaryGroupMassFormula.BridgeRealK

open Matrix

lemma jm_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl

lemma sgn_mul_self {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (if ε a then (1 : ℂ) else -1) * (if ε a then (1 : ℂ) else -1) = 1 := by
  cases ε a <;> simp

lemma jm_mul_jm {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 :=
  Formalism.REAL.Jm_mul_self ε

lemma jm_mul_apply {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Formalism.REAL.Jm ε * k) a b = (if ε a then (1 : ℂ) else -1) * k a b := by
  rw [jm_eq, Matrix.diagonal_mul]

lemma mul_jm_apply {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (k * Formalism.REAL.Jm ε) a b = k a b * (if ε b then (1 : ℂ) else -1) := by
  rw [jm_eq, Matrix.mul_diagonal]

lemma comm_iff {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * k = k * Formalism.REAL.Jm ε ↔ ∀ a b, ε a ≠ ε b → k a b = 0 := by
  constructor
  · intro h a b hab
    have e := congrFun (congrFun h a) b
    rw [jm_mul_apply, mul_jm_apply] at e
    cases ha : ε a <;> cases hb : ε b
    · exact absurd (ha.trans hb.symm) hab
    · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at e
      have h2 : (2 : ℂ) * k a b = 0 := by linear_combination -e
      simpa using h2
    · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at e
      have h2 : (2 : ℂ) * k a b = 0 := by linear_combination e
      simpa using h2
    · exact absurd (ha.trans hb.symm) hab
  · intro h
    ext a b
    rw [jm_mul_apply, mul_jm_apply]
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab]; simp

theorem realK : PI.AdBridgeSteps.RealK := by
  intro n ε k hk
  unfold Formalism.REAL.inUJ at hk
  rw [← comm_iff]
  constructor
  · intro hu
    have hu' : k * kᴴ = 1 := mul_eq_one_comm.mp hu
    calc Formalism.REAL.Jm ε * k = (k * kᴴ) * Formalism.REAL.Jm ε * k := by rw [hu', Matrix.one_mul]
      _ = k * (kᴴ * Formalism.REAL.Jm ε * k) := by simp only [Matrix.mul_assoc]
      _ = k * Formalism.REAL.Jm ε := by rw [hk]
  · intro hc
    calc kᴴ * k = kᴴ * k * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) := by rw [jm_mul_jm, Matrix.mul_one]
      _ = kᴴ * (k * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc]
      _ = kᴴ * (Formalism.REAL.Jm ε * k) * Formalism.REAL.Jm ε := by rw [hc]
      _ = (kᴴ * Formalism.REAL.Jm ε * k) * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk, jm_mul_jm]

end PI.UnitaryGroupMassFormula.BridgeRealK
