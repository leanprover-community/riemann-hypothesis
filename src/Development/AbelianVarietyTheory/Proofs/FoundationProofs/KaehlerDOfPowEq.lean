module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kaehler_D_of_pow_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (a b : S) (m : ℕ) (h : a ^ m = b) :
    a • KaehlerDifferential.D R S b = ((m : S) * b) • KaehlerDifferential.D R S a := by
  subst h
  rw [Derivation.leibniz_pow]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [smul_comm a, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]
    congr 1
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_pow (T : Tower p Ω) (n k : ℕ) : zS T (n + k) ^ (p ^ k) = zS T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply Subtype.ext
    have h1 : (zS T (n + (k + 1)) : Ω) ^ p = (zS T (n + k) : Ω) := T.ζpow (n + k)
    have h2 : (zS T (n + k) : Ω) ^ (p ^ k) = (zS T n : Ω) := congrArg Subtype.val ih
    simp only [SubmonoidClass.coe_pow]
    rw [pow_succ', pow_mul, h1, h2]

theorem qS_pow (T : Tower p Ω) (n k : ℕ) : qS T (n + k) ^ (p ^ k) = qS T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply Subtype.ext
    have h1 : (qS T (n + (k + 1)) : Ω) ^ p = (qS T (n + k) : Ω) := T.qpow (n + k)
    have h2 : (qS T (n + k) : Ω) ^ (p ^ k) = (qS T n : Ω) := congrArg Subtype.val ih
    simp only [SubmonoidClass.coe_pow]
    rw [pow_succ', pow_mul, h1, h2]

theorem dlog_transition : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (n k : ℕ), zS T (n + k) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T n) = ((p : (integralClosure (O0 p) Ω)) ^ k * zS T n) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T (n + k)) ∧ qS T (n + k) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T n) = ((p : (integralClosure (O0 p) Ω)) ^ k * qS T n) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T (n + k)) := by
  intro p _ Ω _ _ T n k
  constructor
  · have := kaehler_D_of_pow_eq (R := O0 p) _ _ _ (zS_pow T n k)
    simpa [Nat.cast_pow] using this
  · have := kaehler_D_of_pow_eq (R := O0 p) _ _ _ (qS_pow T n k)
    simpa [Nat.cast_pow] using this

end GlobalTheory.AlmostEt
