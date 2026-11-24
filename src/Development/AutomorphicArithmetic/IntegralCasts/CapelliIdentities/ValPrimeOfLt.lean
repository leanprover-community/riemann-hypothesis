module

public import Mathlib.RingTheory.Valuation.ValuationSubring
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
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

theorem UpperTheory.Reformulated.B.Qi55.val_prime_of_lt :
    ∀ {Ω : Type} [inst : Field Ω]
    (A : ValuationSubring Ω) (n : ℕ),
    n ≠ (0 : ℕ) →
      (A.valuation : Ω → A.ValueGroup) (↑n : Ω) < (1 : A.ValueGroup) →
        ∃ (t : ℕ), Nat.Prime t ∧ t ∣ n ∧ (A.valuation : Ω → A.ValueGroup) (↑t : Ω) < (1 : A.ValueGroup) := by
  intro Ω _ A n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ h; simp at h
  | prime_mul p a hp ih =>
    intro hne h
    have ha : a ≠ 0 := right_ne_zero_of_mul hne
    by_cases hpv : A.valuation (p : Ω) < 1
    · exact ⟨p, hp, dvd_mul_right p a, hpv⟩
    · have hav : A.valuation (a : Ω) < 1 := by
        by_contra hc
        rw [Nat.cast_mul, map_mul] at h
        exact absurd h (not_lt.mpr (one_le_mul (not_lt.mp hpv) (not_lt.mp hc)))
      obtain ⟨t, ht, hd, hv⟩ := ih ha hav
      exact ⟨t, ht, hd.mul_left p, hv⟩
