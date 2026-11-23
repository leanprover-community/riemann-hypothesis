module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem ringOfIntegers_trace_mulLeft_nondegenerate :
    ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K),
      (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro K _ _ x hx
  by_contra hne
  have hxK : (x : K) ≠ 0 := by
    intro h; exact hne (RingOfIntegers.coe_eq_zero_iff.mp h)
  have halg : IsAlgebraic ℤ ((x : K)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨d, hd0, hdi⟩ := halg.exists_integral_multiple
  let y : 𝓞 K := ⟨d • (x : K)⁻¹, hdi⟩
  have hxy : x * y = algebraMap ℤ (𝓞 K) d := by
    apply RingOfIntegers.coe_injective
    show (x : K) * (d • (x : K)⁻¹) = ((algebraMap ℤ (𝓞 K) d : 𝓞 K) : K)
    rw [eq_intCast, zsmul_eq_mul]
    push_cast
    field_simp
    first | exact (map_intCast (algebraMap (𝓞 K) K) d).symm | norm_cast | simp
  have h := hx y
  rw [hxy] at h
  have h2 : LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (algebraMap ℤ (𝓞 K) d))
      = Algebra.trace ℤ (𝓞 K) (algebraMap ℤ (𝓞 K) d) := by
    rw [Algebra.trace_apply]; rfl
  rw [h2, Algebra.trace_algebraMap] at h
  have hpos : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (by exact_mod_cast h) hpos.ne'
  · exact hd0 h

end GlobalTheory
