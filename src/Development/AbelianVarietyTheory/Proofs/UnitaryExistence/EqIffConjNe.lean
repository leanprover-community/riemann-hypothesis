module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory.ConjugateMembership

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_neg_of_sq {x : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) x = -x := by
  have hre : x.re * x.re - x.im * x.im = -d := by
    have := congrArg Complex.re hx
    simpa [sq] using this
  have him : x.re * x.im + x.im * x.re = 0 := by
    have := congrArg Complex.im hx
    simpa [sq] using this
  have h0 : x.re = 0 := by
    by_contra h
    have hi : x.im = 0 := by
      have h2 : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left h
    rw [hi] at hre
    nlinarith [mul_self_nonneg x.re]
  apply Complex.ext <;> simp [h0]

theorem eq_iff_conj_ne {x r : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) (hr : r ^ 2 = -(d : ℂ)) :
    x = r ↔ ¬ (starRingEnd ℂ) x = r := by
  rw [conj_eq_neg_of_sq hd hx]
  constructor
  · rintro rfl h
    have h0 : x = 0 := by linear_combination (-1 / 2 : ℂ) * h
    rw [h0] at hx
    have : (d : ℂ) = 0 := by linear_combination hx
    exact hd.ne' (by exact_mod_cast this)
  · intro h
    have : (x - r) * (-x - r) = 0 := by linear_combination hr - hx
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd (sub_eq_zero.1 h1) h

theorem mem_iff_conjugate_notMem {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hx : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [← map_pow, hE]; simp
  have hr : H.rt0 ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [H.sqrt_neg_disc_sq]; simp
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  exact eq_iff_conj_ne hd hx hr

end GlobalTheory.ConjugateMembership
