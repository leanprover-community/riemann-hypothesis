module

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.AlgebraMapNeZeroOfMemHcompl
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace BE

theorem exists_gen {R : Type*} [CommRing R] [IsDedekindDomain R] {I P Q : Ideal R} (hI : I ≠ ⊥)
    (hP : P.IsPrime) (hQ : Q.IsPrime) :
    ∃ r ∈ I, r ≠ 0 ∧ ∃ s : R, s ∉ P ∧ s ∉ Q ∧ ∀ x ∈ I, ∃ y : R, s * x = r * y := by
  have key : ∀ P : Ideal R, P.IsPrime → ¬ I ≤ I * P := by
    intro P hP hle
    have h1 : I * P = I * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left hle
    exact hP.ne_top (mul_left_cancel₀ hI h1)
  have h1 : ¬ ((I : Set R) ⊆ (I * P : Ideal R) ∪ (I * Q : Ideal R)) := by
    intro h
    rcases Ideal.subset_union.1 h with h | h
    · exact key P hP h
    · exact key Q hQ h
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.1 h1
  have hrP : r ∉ I * P := fun h => hr (Or.inl h)
  have hrQ : r ∉ I * Q := fun h => hr (Or.inr h)
  have hr0 : r ≠ 0 := fun h => hrP (h ▸ Ideal.zero_mem _)
  have hle : Ideal.span {r} ≤ I := (Ideal.span_singleton_le_iff_mem I).2 hrI
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hmem : r ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self r
  have h2 : ¬ ((J : Set R) ⊆ (P : Ideal R) ∪ (Q : Ideal R)) := by
    intro h
    rcases Ideal.subset_union.1 h with h | h
    · exact hrP (Ideal.mul_mono_right h hmem)
    · exact hrQ (Ideal.mul_mono_right h hmem)
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.1 h2
  refine ⟨r, hrI, hr0, s, fun h => hs (Or.inl h), fun h => hs (Or.inr h), fun x hx => ?_⟩
  have h3 : x * s ∈ Ideal.span {r} := hJ ▸ Ideal.mul_mem_mul hx hsJ
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h3
  exact ⟨y, by rw [mul_comm s x, ← hy, mul_comm]⟩

theorem avoid_two {R : Type*} [CommRing R] {P Q : Ideal R} (hQ : Q.IsPrime) {a s m : R} (k : R)
    (ha : a ∈ P) (hsP : s ∉ P) (hsQ : s ∉ Q) (hm : m ∉ Q) :
    (s - k * a ∉ P ∧ s - k * a ∉ Q) ∨ (s - (k + m) * a ∉ P ∧ s - (k + m) * a ∉ Q) := by
  have hP : ∀ c : R, s - c * a ∉ P := by
    intro c h
    apply hsP
    have := P.add_mem h (P.mul_mem_left c ha)
    simpa using this
  by_cases h1 : s - k * a ∈ Q
  · right
    refine ⟨hP _, fun h2 => ?_⟩
    have h3 : m * a ∈ Q := by
      have := Q.sub_mem h1 h2
      have e : s - k * a - (s - (k + m) * a) = m * a := by ring
      rwa [e] at this
    rcases hQ.mem_or_mem h3 with h | h
    · exact hm h
    · apply hsQ
      have := Q.add_mem h1 (Q.mul_mem_left k h)
      simpa using this
  · exact Or.inl ⟨hP _, h1⟩

end BE

theorem principal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal)
    (A : AddSubgroup K) (hA : ∀ s ∈ locRing p, ∀ a ∈ A, s * a ∈ A) (h0 : ∃ a ∈ A, a ≠ 0)
    (ht : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ locRing p) :
    ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ locRing p := by
  apply Formalism.HermitianLattices.Ext.L3.WA.principal_locRing <;> assumption

theorem unit_or_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) (ha : a ∈ locRing p)
    (κ : K) (hκ : κ ∈ locRing p) (μ : K) (hna : a⁻¹ ∉ locRing p) (hμ : IsUnitIn (locRing p) μ) :
    IsUnitIn (locRing p) (1 - κ * a) ∨ IsUnitIn (locRing p) (1 - (κ + μ) * a) := by
  apply Formalism.HermitianLattices.Ext.L3.WA.unit_or_locRing <;> assumption

theorem isHermSemilocal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) :=
  ⟨fun _ ha => star_mem_locRing hp.isPrime ha, frac_locRing p, unram_locRing hK hp,
    principal_locRing hK hp, unit_or_locRing hp.isPrime⟩

end ReciprocityTheory.ChartRestriction.L3.WA
