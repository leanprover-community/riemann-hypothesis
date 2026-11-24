module

public import Formalism.ConjugateSelfDual.Statement
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.PadicIntegralNorm

theorem norm_le_one_of_isIntegral {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [Algebra R K]
    (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (x : K) (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  obtain ⟨p, hpm, hpx⟩ := hx
  by_contra hlt
  rw [not_le] at hlt
  have h0 : (0 : ℝ) < ‖x‖ := zero_lt_one.trans hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hpx

  have hxn : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * x ^ i := by
    linear_combination hpx

  have hterm : ∀ i ∈ Finset.range p.natDegree,
      ‖algebraMap R K (p.coeff i) * x ^ i‖ < ‖x‖ ^ p.natDegree := by
    intro i hi
    rw [norm_mul, norm_pow]
    calc ‖algebraMap R K (p.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by gcongr; exact hR _
      _ = ‖x‖ ^ i := one_mul _
      _ < ‖x‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rcases (Finset.range p.natDegree).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, neg_zero] at hxn
    have h1 : ‖x ^ p.natDegree‖ = 0 := by rw [hxn, norm_zero]
    rw [norm_pow] at h1
    exact (pow_pos h0 _).ne' h1
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun i => algebraMap R K (p.coeff i) * x ^ i)
    have h2 := congrArg norm hxn
    rw [norm_neg, norm_pow] at h2
    linarith [hterm i hi]

theorem norm_le_one_of_isIntegral_padicInt {l : ℕ} [inst : Fact (Nat.Prime l)] (x : Formalism.ConjugateSelfDual.Qbar l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  refine norm_le_one_of_isIntegral (R := ℤ_[l]) (fun r => ?_) x hx
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Formalism.ConjugateSelfDual.Qbar l), norm_algebraMap']
  exact PadicInt.norm_le_one r

end GlobalTheory.PadicIntegralNorm
