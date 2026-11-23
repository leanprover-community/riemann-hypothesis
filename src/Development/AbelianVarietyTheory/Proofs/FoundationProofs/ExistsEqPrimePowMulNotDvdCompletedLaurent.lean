module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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

@[expose] public section

open GlobalTheory.K5

namespace GlobalTheory.K5.Basic

theorem exists_not_prime_pow_dvd_completedLaurent (p : ℕ) [Fact p.Prime] (x : O0 p) (hx : x ≠ 0) :
    ∃ a : ℕ, ¬ (p : O0 p) ^ a ∣ x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) x
  obtain ⟨a, ha⟩ := exists_not_dvd p s hx
  refine ⟨a, ?_⟩
  rintro ⟨z, hz⟩
  apply ha a le_rfl
  have h1 := congrArg (AdicCompletion.evalₐ (pI p) a) hz
  rw [AdicCompletion.evalₐ_mk, map_mul, map_pow, map_natCast,
    ← map_natCast (Ideal.Quotient.mk (pI p ^ a)), ← map_pow] at h1
  have h2 : Ideal.Quotient.mk (pI p ^ a) ((p : Lau p) ^ a) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow]
  rw [h2, zero_mul, Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow] at h1
  exact h1

theorem exists_eq_prime_pow_mul_not_dvd_completedLaurent : ∀ (p : ℕ) [Fact p.Prime], ∀ x : O0 p, x ≠ 0 →
    ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := by
  intro p _ x hx
  obtain ⟨a, ha⟩ := exists_not_prime_pow_dvd_completedLaurent p x hx
  have hfin : FiniteMultiplicity (p : O0 p) x :=
    ⟨a, fun h => ha ((pow_dvd_pow _ (Nat.le_succ a)).trans h)⟩
  obtain ⟨y, hy, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, y, hy, hnd⟩

end GlobalTheory.K5.Basic
