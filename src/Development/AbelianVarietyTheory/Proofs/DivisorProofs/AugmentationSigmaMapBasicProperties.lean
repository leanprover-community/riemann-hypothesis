module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory

theorem Obs.sig_basic : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker σ hσ
  have h2 : ∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← map_mul, hσ, hσ, mul_smul_comm]
    | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  refine ⟨?_, h2, ?_, ?_⟩
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [hσ, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem y'))
    | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
  · intro b₀
    obtain ⟨b', rfl⟩ := hp b₀
    rw [hσ, α.one, zero_smul]
  · intro x hx
    rw [Ideal.map, Ideal.span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨y, hy0, hyk⟩ := α.surj i hi
      refine ⟨y ⊗ₜ 1, ?_, ?_⟩
      · simp [Obs.Aug.KerQ, hy0]
      · rw [← map_one p, hσ, hyk, Algebra.smul_def, _root_.mul_one]
    | zero => exact ⟨0, by simp [Obs.Aug.KerQ], by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      refine ⟨y + y', ?_, by rw [map_add (f := _)]⟩
      simp only [Obs.Aug.KerQ, map_add (f := _)] at *; rw [hy, hy', add_zero]
    | smul b x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨(1 ⊗ₜ p b) * y, ?_, by rw [h2, smul_eq_mul]⟩
      simp only [Obs.Aug.KerQ, map_mul] at *; rw [hy, mul_zero]

end GlobalTheory
