module

public import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory

theorem intertwiner_dOp_of_stabiliser {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁]
    [FiniteDimensional ℂ V₁] {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂]
    [FiniteDimensional ℂ V₂] {k r : ℕ} {z e : Fin (2 * r + k + 1) → ℂ}
    {π₁ : Mx k r → (V₁ →L[ℂ] V₁)} {π₂ : Mx k r → (V₂ →L[ℂ] V₂)} (T : V₁ →L[ℂ] V₂)
    (h₁ : IsRepW k r z π₁) (h₂ : IsRepW k r z π₂)
    (hT : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, T (π₁ h v) = π₂ h (T v))
    {X : Mx k r} (hX : InLieW k r z X) (he : X *ᵥ e = 0) (v : V₁) :
    T (dOp π₁ X v) = dOp π₂ X (T v) := by
  have d₁ := dOp_hasDeriv h₁.1 h₁.2 hX
  have d₂ := dOp_hasDeriv h₂.1 h₂.2 hX
  have e₁ := ((T.comp (ContinuousLinearMap.apply ℂ V₁ v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) d₁
  have e₂ := ((ContinuousLinearMap.apply ℂ V₂ (T v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) d₂
  have hf : (((T.comp (ContinuousLinearMap.apply ℂ V₁ v)).restrictScalars ℝ) ∘
      fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • X))) =
      (((ContinuousLinearMap.apply ℂ V₂ (T v)).restrictScalars ℝ) ∘
      fun t : ℝ => π₂ (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact hT _ (exp_uw hX t) (Qx8.exp_fix he t) v
  rw [hf] at e₁
  exact e₁.unique e₂

theorem intertwiner_EB_of_stabiliser : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] (k r m : ℕ) (z e : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (T : V₁ →L[ℂ] V₂) (B : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsRepW k r z π₁ → IsRepW k r z π₂ → IsFrameOf k r [z, e] B → (∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, T (π₁ h v) = π₂ h (T v)) → ∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v) := by
  intro V₁ _ _ _ V₂ _ _ _ k r m z e π₁ π₂ T B h₁ h₂ hB hT a b v
  have hz : IsFrameOf k r [z] B := ⟨hB.1, hB.2.1, fun c y hy => hB.2.2 c y (by simp at hy; simp [hy])⟩
  have he : IsFrameOf k r [e] B := ⟨hB.1, hB.2.1, fun c y hy => hB.2.2 c y (by simp at hy; simp [hy])⟩
  have lz := frame_lie hz a b
  have le := frame_lie he a b
  have p1 := intertwiner_dOp_of_stabiliser T h₁ h₂ hT lz.1 le.1.2 v
  have p2 := intertwiner_dOp_of_stabiliser T h₁ h₂ hT lz.2 le.2.2 v
  show T (ecOp π₁ (unitB (Hpk k r) B a b) v) = ecOp π₂ (unitB (Hpk k r) B a b) (T v)
  unfold ecOp
  simp only [_root_.add_apply, _root_.smul_apply, map_add (f := _), map_smul, p1, p2]

end GlobalTheory
