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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.Associator

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovMono

theorem cov_self (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A) : Cov p r A := by
  intro K₁ K₀ _ _ _ _ _ _ d _ z hz k
  obtain ⟨w, hw⟩ := hz
  have key : z = d (TensorProduct.lid A K₁ w) := by
    have h1 : TensorProduct.lid A K₀ (d.lTensor A w) = d (TensorProduct.lid A K₁ w) :=
      LinearMap.congr_fun (show (TensorProduct.lid A K₀).toLinearMap ∘ₗ d.lTensor A =
        d ∘ₗ (TensorProduct.lid A K₁).toLinearMap from TensorProduct.ext' fun _ _ => by simp) w
    rw [hw] at h1
    simpa using h1
  rw [key, ← map_smul]
  exact ⟨_, rfl⟩

theorem cov_of_algHom (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A)
    (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁]
    (φ : B →ₐ[A] B₁) (h : Cov p r B₁) : Cov p r B := by
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  obtain ⟨w, hw⟩ := hz
  refine h K₁ K₀ hK₁ hK₀ d hd z ⟨φ.toLinearMap.rTensor K₁ w, ?_⟩ k
  have h1 :
      φ.toLinearMap.rTensor K₀ (d.lTensor B w) = d.lTensor B₁ (φ.toLinearMap.rTensor K₁ w) :=
    LinearMap.congr_fun ((LinearMap.rTensor_comp_lTensor (f := φ.toLinearMap) (g := d)).trans
      (LinearMap.lTensor_comp_rTensor (f := φ.toLinearMap) (g := d)).symm) w
  rw [← h1, hw]
  simp

theorem cov_mono : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Cov p r A ∧ ∀ (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁] (φ : B →ₐ[A] B₁), Cov p r B₁ → Cov p r B := by
  intro p _ A _ r
  exact ⟨cov_self p A r, fun B _ _ B₁ _ _ φ h => cov_of_algHom p A r B B₁ φ h⟩

end GlobalTheory.CompanionTheory.CovMono
