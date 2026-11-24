module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}

open NumberField IsDedekindDomain in
open scoped WithZero in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} in
theorem _root_.GlobalTheory.QNorm.IsQuad.coord_indep
    (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (a b : F)
    (hab : algebraMap F E a + algebraMap F E b * θ = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply h.nonsq
    refine ⟨-a / b, (algebraMap F E).injective ?_⟩
    have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
    have hθ : θ = -algebraMap F E a / algebraMap F E b := by
      field_simp
      linear_combination hab
    rw [← h.sq, hθ]
    simp [map_div₀, map_neg]
    ring
  subst hb
  refine ⟨(algebraMap F E).injective ?_, rfl⟩
  simpa using hab

open NumberField IsDedekindDomain in
open scoped WithZero in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} in
theorem _root_.GlobalTheory.QNorm.IsQuad.root_ne_zero (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) :
    θ ≠ 0 := by
  intro hθ
  apply h.nonsq
  refine ⟨0, (algebraMap F E).injective ?_⟩
  rw [← h.sq, hθ]
  simp

end


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.isQuad_basic : ∀ (F E : Type) [Field F] [CharZero F] [Field E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ a : F, x = algebraMap F E a) ∧
    (∀ a b : F, algebraMap F E a + algebraMap F E b * θ = 0 → a = 0 ∧ b = 0) ∧
    (∀ x : E, ∃ a b : F, x * σ x = algebraMap F E (a ^ 2 - δ * b ^ 2)) ∧
    (∀ x : E, x * σ x = 1 → ∃ y : E, y ≠ 0 ∧ x = y / σ y) ∧
    (∀ u : F, IsSquare (algebraMap F E u) → IsSquare u ∨ IsSquare (u * δ)) ∧
    Module.finrank F E = 2 := by
  intro F E _ _ _ _ δ θ σ h
  have t1 := h.coord_indep
  have hθ := h.root_ne_zero
  have hc := h.conj
  have hs := h.sq
  refine ⟨?_, ?_, t1, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    simp [AlgEquiv.commutes, hc]
  · intro x hx
    obtain ⟨a, b, rfl⟩ := h.span x
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc] at hx
    have := t1 0 (2 * b) (by simp only [map_zero, map_mul, map_ofNat]; linear_combination -hx)
    have hb : b = 0 := by simpa using this.2
    exact ⟨a, by simp [hb]⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    refine ⟨a, b, ?_⟩
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc, map_sub, map_pow]
    linear_combination (-(algebraMap F E b) ^ 2) * hs
  · intro x hx
    by_cases h1 : x = -1
    · refine ⟨θ, hθ, ?_⟩
      rw [hc, h1, div_neg, div_self hθ]
    · have hy : (1 + x) ≠ 0 := fun h0 => h1 (by linear_combination h0)
      have hσy : σ (1 + x) ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ σ.injective]
      refine ⟨1 + x, hy, ?_⟩
      rw [eq_div_iff hσy, map_add (f := _), map_one]
      linear_combination hx
  · rintro u ⟨y, hy⟩
    obtain ⟨a, b, rfl⟩ := h.span y
    have := t1 (u - a ^ 2 - b ^ 2 * δ) (-(2 * a * b)) (by
      simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat]
      linear_combination hy + (algebraMap F E b) ^ 2 * hs)
    have h2 : a * b = 0 := by
      have h3 := this.2
      have h4 : (2 : F) * (a * b) = 0 := by linear_combination -h3
      simpa using h4
    have hu : u = a ^ 2 + b ^ 2 * δ := by linear_combination this.1
    rcases mul_eq_zero.1 h2 with ha | hb
    · right; exact ⟨b * δ, by rw [hu, ha]; ring⟩
    · left; exact ⟨a, by rw [hu, hb]; ring⟩
  · have hli : LinearIndependent F ![(1 : E), θ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply t1
      simpa [Algebra.smul_def] using hst
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ]) := by
      intro x _
      obtain ⟨a, b, rfl⟩ := h.span x
      rw [Matrix.range_cons_cons_empty]
      refine Submodule.mem_span_pair.2 ⟨a, b, ?_⟩
      simp [Algebra.smul_def]
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)

end GlobalTheory.QNorm
