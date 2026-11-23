module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem coboundaryOne_additiveFormalGroupLaw_X_pow (R : Type) [CommRing R] (d N : ℕ) (m : Fin d) (hN : 1 ≤ N) :
    cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N,
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
  have h1 : HasSubst (addLaw R d) := hasSubst_of_constantCoeff_zero fun i => by simp [addLaw]
  have h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold cob1 inL inR
  rw [subst_pow h1, subst_pow h2, subst_pow h3, subst_X h1, subst_X h2, subst_X h3]
  simp only [addLaw]
  have hr : Finset.range (N + 1) = insert 0 (insert N (Finset.Ioo 0 N)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [add_pow, hr, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
  simp only [pow_zero, Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, mul_one, one_mul]
  have key : ∀ i ∈ Finset.Ioo 0 N,
      (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R) ^ i * X (Sum.inr m) ^ (N - i) *
        (N.choose i : MvPowerSeries (Fin d ⊕ Fin d) R) =
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
    intro i _
    rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, ← nsmul_eq_mul', ← map_nsmul,
      nsmul_one]
  rw [Finset.sum_congr rfl key]
  abel

end GlobalTheory
