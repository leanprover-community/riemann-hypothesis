module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
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

namespace GlobalTheory.NewPrime

theorem aeval_eq_zero_of_low_coeff_of_pow_eq_zero :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t : B) (K : ℕ) (ξ : ι → B)
      (F : MvPolynomial ι O), t ^ K = 0 → (∀ q, t ∣ ξ q) →
      (∀ u : ι →₀ ℕ, u.degree < K → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t K ξ F htK hdvd hlow
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : u.degree < K
  · rw [hlow u hu, zero_mul]
  ·
    have hmon : t ^ u.degree ∣ ∏ i ∈ u.support, ξ i ^ u i := by
      rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow_of_dvd (hdvd i) _
    have hK : t ^ K ∣ ∏ i ∈ u.support, ξ i ^ u i :=
      (pow_dvd_pow t (not_lt.mp hu)).trans hmon
    rw [htK, zero_dvd_iff] at hK
    rw [hK, mul_zero]

end GlobalTheory.NewPrime
