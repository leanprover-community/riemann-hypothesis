module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

@[expose] public section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_of_unity_eq_one_of_dvd_sub_one :
    ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E) (n M : ℕ),
      0 < n → u ^ n = 1 → 3 ≤ M → (M : 𝓞 E) ∣ u - 1 → u = 1 := by
  intro E _ _ u n M hn hu hM ⟨x, hx⟩
  have hlt : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ < 1 := by
    intro φ
    have h1 : (φ (u : E)) ^ n = 1 := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hu
      simpa using this
    have h2 : ‖φ (u : E)‖ = 1 := by
      have := congrArg norm h1
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h3 : φ (u : E) - 1 = (M : ℂ) * φ (x : E) := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hx
      simpa using this
    have h4 : (M : ℝ) * ‖φ (x : E)‖ ≤ 2 := by
      have h5 := norm_sub_le (φ (u : E)) 1
      rw [h3, norm_mul, h2, norm_one, Complex.norm_natCast] at h5
      linarith
    have h6 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [norm_nonneg (φ (x : E))]
  by_contra hne
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    have : x = 0 := by exact_mod_cast h0
    rw [this, mul_zero, sub_eq_zero] at hx
    exact hne hx
  obtain ⟨k, hk, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx0
    (RingOfIntegers.isIntegral_coe x) (fun φ => (hlt φ).le)
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h7 := congrArg (fun y : E => ‖φ y‖) hpow
  simp only [map_pow, norm_pow, map_one, norm_one] at h7
  have h8 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h7
  exact (hlt φ).ne h8

end GlobalTheory.CompanionTheory.Ar.Flat
