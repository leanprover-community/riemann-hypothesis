module

public import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open PowerSeries

theorem coeff_relation {O : Type*} [CommRing O] [IsDomain O] {d₁ d : ℕ} (p : O) (hp : p ≠ 0)
    (F : Fin d₁ → O⟦X⟧) (μ : Fin d₁ → Fin d → O) (k₀ : Fin d) (K s S h k : ℕ) (Q : O⟦X⟧)
    (hk : k < h) (hkS : S ≤ k)
    (heq : ∀ j : Fin d, ∃ R : O⟦X⟧,
      C p ^ K * (∑ m, F m * C (μ m j) - (if j = k₀ then C p ^ s * X ^ S * Q else 0)) = X ^ h * R) :
    ∀ j, ∑ m, coeff k (F m) * μ m j = if j = k₀ then p ^ s * coeff (k - S) Q else 0 := by
  intro j
  obtain ⟨R, hR⟩ := heq j
  have h1 : coeff k (C p ^ K * (∑ m, F m * C (μ m j) -
      (if j = k₀ then C p ^ s * X ^ S * Q else 0))) = 0 := by
    rw [hR, coeff_X_pow_mul', if_neg (by omega)]

  simp only [← map_pow, coeff_C_mul, map_sub, map_sum, coeff_mul_C] at h1
  have h2 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hp))
  rw [h2]
  split_ifs with hj
  · simp [← map_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul', hkS]
  · exact map_zero _

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
