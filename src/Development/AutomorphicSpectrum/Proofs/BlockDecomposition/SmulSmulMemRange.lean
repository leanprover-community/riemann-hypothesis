module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Data.Nat.Prime.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SnakeCov

theorem smul_smul_mem_range {A B D K₁ K₀ : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup D] [Module A D] [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (ρ : B →ₗ[A] D) (hρ : Function.Surjective ρ) (h1 : ρ 1 = 0) (d : K₁ →ₗ[A] K₀) (s : A)
    (hGood : ∀ x : D ⊗[A] K₁, d.lTensor D x = 0 →
      ∃ v : D ⊗[A] LinearMap.ker d, (LinearMap.ker d).subtype.lTensor D v = s • x)
    (hK₁ : ∀ w : B ⊗[A] K₁, ρ.rTensor K₁ w = 0 → ∃ a : K₁, w = (1 : B) ⊗ₜ[A] a)
    (hK₀ : ∀ a : K₀, (1 : B) ⊗ₜ[A] a = 0 → s • a = 0)
    (z : K₀) (w : B ⊗[A] K₁) (hw : (1 : B) ⊗ₜ[A] z = d.lTensor B w) :
    s • s • z ∈ LinearMap.range d := by
  have comm₁ : ∀ t : B ⊗[A] K₁, d.lTensor D (ρ.rTensor K₁ t) = ρ.rTensor K₀ (d.lTensor B t) := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have comm₂ : ∀ t : B ⊗[A] LinearMap.ker d,
      (LinearMap.ker d).subtype.lTensor D (ρ.rTensor _ t)
        = ρ.rTensor K₁ ((LinearMap.ker d).subtype.lTensor B t) := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have dker : ∀ t : B ⊗[A] LinearMap.ker d,
      d.lTensor B ((LinearMap.ker d).subtype.lTensor B t) = 0 := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  have hw' : d.lTensor D (ρ.rTensor K₁ w) = 0 := by
    rw [comm₁, ← hw]; simp [h1]
  obtain ⟨v', hv'⟩ := hGood _ hw'
  obtain ⟨v, rfl⟩ := LinearMap.rTensor_surjective (LinearMap.ker d) hρ v'
  obtain ⟨u, hu⟩ := hK₁ (s • w - (LinearMap.ker d).subtype.lTensor B v) (by
    rw [map_sub, map_smul, ← comm₂, hv', sub_self])
  have key : (1 : B) ⊗ₜ[A] (d u - s • z) = 0 := by
    have := congrArg (d.lTensor B) hu
    rw [map_sub, map_smul, dker, sub_zero, ← hw, LinearMap.lTensor_tmul] at this
    rw [TensorProduct.tmul_sub, ← this, TensorProduct.tmul_smul, sub_self]
  have h := hK₀ _ key
  refine ⟨s • u, ?_⟩
  rw [map_smul]
  rw [smul_sub, sub_eq_zero] at h
  exact h

theorem pow_smul_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    {p : ℕ} (hp : 2 ≤ p) (s : A) (z : M) (h : s • s • z ∈ N) : s ^ p • z ∈ N := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have : s ^ (2 + q) • z = s ^ q • s • s • z := by
    simp only [smul_smul]; congr 1; ring
  rw [this]
  exact N.smul_mem _ h

theorem mv_cov : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ : B →ₗ[A] D), IsRt p r → Pf p D → Function.Surjective ρ → ρ 1 = 0 → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ w : B ⊗[A] K, ρ.rTensor K w = 0 → ∃ a : K, w = (1 : B) ⊗ₜ[A] a) → Cov p r B := by
  intro p _ A _ B _ _ D _ _ r ρ hr hD hρ h1 hK K₁ K₀ _ _ _ _ hp₁ hp₀ d hG z hz k
  obtain ⟨w, hw⟩ := hz
  have hmem : r (k + 1) • r (k + 1) • z ∈ LinearMap.range d :=
    smul_smul_mem_range ρ hρ h1 d (r (k + 1))
      (fun x hx => by
        obtain ⟨v, hv⟩ := hG D hD x hx (k + 1)
        exact ⟨v, hv⟩)
      (hK K₁ hp₁).2
      (fun a ha => (hK K₀ hp₀).1 a ha (k + 1))
      z w hw.symm
  rw [← hr k]
  exact pow_smul_mem _ (Fact.out : p.Prime).two_le _ _ hmem

end GlobalTheory.CompanionTheory.SnakeCov
