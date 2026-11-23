module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfLTensorSubtypeEqZero
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

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_mem_range_lTensor_of_lTensor_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R)
      (N : Type) [AddCommGroup N] [Module R N] (K₀ : Type) [AddCommGroup K₀] [Module R K₀]
      (K₁ : Type) [AddCommGroup K₁] [Module R K₁] (K₂ : Type) [AddCommGroup K₂] [Module R K₂]
      (K₃ : Type) [AddCommGroup K₃] [Module R K₃] (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂)
      (d₂ : K₂ →ₗ[R] K₃), IsRt p r → (∀ z, d₂ (d₁ z) = 0) →
      (∀ z, d₁ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₀) →
      (∀ z, d₂ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₁) →
      (∀ (a : R) (x : K₃), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0) →
      ∀ w : N ⊗[R] K₁, d₁.lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (d₀.lTensor N) := by
  intro p _ R _ _ _ r N _ _ K₀ _ _ K₁ _ _ K₂ _ _ K₃ _ _ d₀ d₁ d₂ hr hdd h1 h2 h3 w hw k
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : ∀ k, r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    intro k
    rw [← pow_two, ← pow_add, Nat.sub_add_cancel hp]
    exact (hr k).symm
  have hsat : ∀ (a : R) (x : K₂), a ≠ 0 → a • x ∈ LinearMap.range d₁ →
      ∀ k, r k • x ∈ LinearMap.range d₁ := by
    rintro a x ha ⟨y, hy⟩ k
    have hax : a • d₂ x = 0 := by
      rw [← map_smul, ← hy, hdd]
    have h0 : d₂ (r (k + 1) • x) = 0 := by
      rw [map_smul]
      exact h3 a _ ha hax (k + 1)
    have h4 := h2 _ h0 (k + 1)
    rw [hrk k, mul_smul, mul_smul]
    exact Submodule.smul_mem _ _ h4
  have hsub : (LinearMap.range d₁).subtype ∘ₗ d₁.rangeRestrict = d₁ := by
    ext x
    rfl
  have hw' : (LinearMap.range d₁).subtype.lTensor N (d₁.rangeRestrict.lTensor N w) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsub]
    exact hw
  have h5 := smul_eq_zero_of_lTensor_subtype_eq_zero R r N K₂ (LinearMap.range d₁) hsat _ hw' (k + 1)
  have h6 : d₁.rangeRestrict.lTensor N (r (k + 1) • w) = 0 := by
    rw [map_smul]
    exact h5
  have hex : Function.Exact (LinearMap.ker d₁).subtype d₁.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hx' : d₁ x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact Subtype.ext z.2
  obtain ⟨u, hu⟩ := (lTensor_exact N hex d₁.surjective_rangeRestrict _).1 h6
  have h7 : ∀ u : N ⊗[R] LinearMap.ker d₁,
      r (k + 1) • (LinearMap.ker d₁).subtype.lTensor N u ∈ LinearMap.range (d₀.lTensor N) := by
    intro u
    induction u with
    | tmul n z =>
      obtain ⟨y, hy⟩ := h1 z z.2 (k + 1)
      exact ⟨n ⊗ₜ y, by simp [hy, TensorProduct.tmul_smul]⟩
    | add a b ha hb =>
      rw [map_add (f := _), smul_add]
      exact Submodule.add_mem _ ha hb
  rw [hrk k, mul_smul, mul_smul, ← hu]
  exact Submodule.smul_mem _ _ (h7 u)

end GlobalTheory.CompanionTheory.Dblock
