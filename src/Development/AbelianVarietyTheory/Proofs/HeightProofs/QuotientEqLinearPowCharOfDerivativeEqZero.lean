module

public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory

theorem quotient_eq_linear_pow_char_of_derivative_eq_zero
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (A D : k[X]) (hD : D ≠ 0)
    (hA : A.natDegree ≤ p) (hDp : D.natDegree < p)
    (hder : derivative A * D = A * derivative D) (hnc : ¬ ∃ c : k, A = C c * D) :
    ∃ a b c : k, a ≠ 0 ∧ c ≠ 0 ∧ D = C c ∧ A = C c * (C a * X ^ p + C b) := by
  classical
  have hp : p.Prime := Fact.out
  have hA0 : A ≠ 0 := fun h => hnc ⟨0, by simp [h]⟩
  obtain ⟨A₁, D₁, hA₁, hD₁, hu⟩ := extract_gcd A D
  have hcop : IsCoprime A₁ D₁ := (gcd_isUnit_iff A₁ D₁).1 hu
  generalize gcd A D = g at hA₁ hD₁
  subst hA₁ hD₁
  have hg : g ≠ 0 := left_ne_zero_of_mul hD
  have hD1 : D₁ ≠ 0 := right_ne_zero_of_mul hD
  have hA1 : A₁ ≠ 0 := right_ne_zero_of_mul hA0
  have h1 : derivative A₁ * D₁ = A₁ * derivative D₁ := by
    have h2 : g ^ 2 * (derivative A₁ * D₁) = g ^ 2 * (A₁ * derivative D₁) := by
      simp only [derivative_mul] at hder
      linear_combination hder
    exact mul_left_cancel₀ (pow_ne_zero 2 hg) h2
  have hdvd : D₁ ∣ derivative D₁ :=
    hcop.symm.dvd_of_dvd_mul_left ⟨derivative A₁, by rw [← h1, mul_comm]⟩
  have hD' : derivative D₁ = 0 := by
    by_contra hne
    exact absurd (degree_le_of_dvd hdvd hne) (not_le.2 (degree_derivative_lt hD1))
  have hA' : derivative A₁ = 0 := by
    rw [hD', mul_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_right hD1
  rw [natDegree_mul hg hA1] at hA
  rw [natDegree_mul hg hD1] at hDp
  have eD := expand_contract p hD' hp.ne_zero
  have eA := expand_contract p hA' hp.ne_zero
  have nD := natDegree_expand p (contract p D₁)
  have nA := natDegree_expand p (contract p A₁)
  rw [eD] at nD
  rw [eA] at nA
  have hD0 : D₁.natDegree = 0 := by
    rcases Nat.eq_zero_or_pos (contract p D₁).natDegree with h | h
    · rw [nD, h, zero_mul]
    · have := Nat.le_mul_of_pos_left p h
      omega
  obtain ⟨d, rfl⟩ := natDegree_eq_zero.1 hD0
  have hd : d ≠ 0 := by
    rintro rfl
    exact hD1 (map_zero _)
  have hm : (contract p A₁).natDegree = 1 := by
    rcases Nat.lt_trichotomy (contract p A₁).natDegree 1 with h | h | h
    · exfalso
      have h0 : (contract p A₁).natDegree = 0 := by omega
      rw [h0, zero_mul] at nA
      obtain ⟨a, rfl⟩ := natDegree_eq_zero.1 nA
      refine hnc ⟨a * d⁻¹, ?_⟩
      have : (C a : k[X]) = C (a * d⁻¹) * C d := by
        rw [← map_mul, inv_mul_cancel_right₀ hd]
      rw [this]
      simp only [map_mul]
      ring
    · exact h
    · exfalso
      have h2 : 2 * p ≤ (contract p A₁).natDegree * p := Nat.mul_le_mul_right p h
      have := hp.pos
      omega
  rw [hm, one_mul] at nA
  have hg0 : g.natDegree = 0 := by omega
  obtain ⟨γ, rfl⟩ := natDegree_eq_zero.1 hg0
  have hγ : γ ≠ 0 := by
    rintro rfl
    exact hg (map_zero _)
  obtain ⟨a, ha, b, hab⟩ := natDegree_eq_one.1 hm
  refine ⟨a * d⁻¹, b * d⁻¹, γ * d, mul_ne_zero ha (inv_ne_zero hd), mul_ne_zero hγ hd,
    (map_mul _ _ _).symm, ?_⟩
  have hdd : (C d : k[X]) * C d⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  rw [← eA, ← hab]
  simp only [map_add (f := _), map_mul, expand_C, expand_X]
  linear_combination (-(C γ * (C a * X ^ p + C b))) * hdd

end GlobalTheory
