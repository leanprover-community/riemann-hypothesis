module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LimV

theorem finiteDimensional_prodSpan_of_fd : ∀ {A B : Type} (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)),
    FiniteDimensional ℂ U₁ → FiniteDimensional ℂ U₂ → FiniteDimensional ℂ (prodSpan U₁ U₂) := by
  intro A B U₁ U₂ h₁ h₂
  let φ : U₁ →ₗ[ℂ] U₂ →ₗ[ℂ] (A × B → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b x => a.1 x.1 * b.1 x.2)
      (fun a a' b => by ext x; simp [add_mul])
      (fun c a b => by ext x; simp [mul_assoc])
      (fun a b b' => by ext x; simp [mul_add])
      (fun c a b => by ext x; simp [mul_left_comm])
  let T : U₁ ⊗[ℂ] U₂ →ₗ[ℂ] (A × B → ℂ) := TensorProduct.lift φ
  have hle : prodSpan U₁ U₂ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro F ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩ : U₁) ⊗ₜ[ℂ] (⟨b, hb⟩ : U₂), by simp [T, φ]⟩
  haveI : FiniteDimensional ℂ (LinearMap.range T) := LinearMap.finiteDimensional_range T
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.LimV

end
