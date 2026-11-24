module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm

@[expose] public section

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.BasicNotions NumberField GlobalTheory.ThStr GlobalTheory.ThBe0 Classical

namespace GlobalTheory.ClassSumEquiv

open MvPolynomial

theorem polD_subst (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ)
    (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ τ, (γ' τ).det ≠ 0) :
    aeval (fun l : Idx D N N' => ∑ k, C ((γ' l.1)⁻¹ k l.2.1) * (X (l.1, k, l.2.2) : MvPolynomial (Idx D N N') ℂ))
      (aeval (fun l : Idx D N N' => ∑ k, C (γ l.1 l.2.2 k) * (X (l.1, l.2.1, k) : MvPolynomial (Idx D N N') ℂ))
        (polD D s Q (fun τ => γ' τ * y' τ))) =
      polD D s (aeval (fun k : FrV D N => ∑ a : Fin N, C (γ k.1 k.2.1 a) *
        (X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y' := by
  unfold polD
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun ⟨τ, a, k⟩ => ?_

  simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  split_ifs with hk
  · have e : y' τ b' ⟨k, hk⟩ = ∑ b, (γ' τ)⁻¹ b' b * (γ' τ * y' τ) b ⟨k, hk⟩ := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul_cancel_left _ _ (h τ).isUnit]

    rw [e, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  · simp

theorem applyAt0_polD_equivariant : ∀ (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ) (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (G : VC D N N' → ℂ), (∀ τ, (γ' τ).det ≠ 0) → Differentiable ℂ G → applyAt0 D (polD D s Q (fun τ => γ' τ * y' τ)) (fun z => G (fun τ => ((γ' τ)⁻¹ * Matrix.of (z τ) * γ τ : Matrix (Fin N') (Fin N) ℂ))) = applyAt0 D (polD D s (MvPolynomial.aeval (fun k : FrV D N => ∑ a : Fin N, MvPolynomial.C (γ k.1 k.2.1 a) * (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y') G := by
  intro D N N' s Q y' γ' γ G h hG
  have hd : Differentiable ℂ (fun z => G (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹) z)) :=
    hG.comp (LinearMap.toContinuousLinearMap (GlobalTheory.NormSum.Minor.mulL (a := N) (fun τ => (γ' τ)⁻¹))).differentiable
  have h1 := GlobalTheory.NormSum.Minor.applyAt0_comp hd (GlobalTheory.NormSum.Minor.mulR γ) (fun l k => γ l.1 l.2.2 k)
    (fun l k => (l.1, l.2.1, k)) (GlobalTheory.NormSum.Minor.mulR_coordV γ) (polD D s Q (fun τ => γ' τ * y' τ))
  rw [GlobalTheory.NormSum.Minor.applyAt0_comp hG (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹))
    (fun l k => (γ' l.1)⁻¹ k l.2.1) (fun l k => (l.1, k, l.2.2)) (GlobalTheory.NormSum.Minor.mulL_coordV _),
    polD_subst D N N' s Q y' γ' γ h] at h1
  rw [← h1]
  simp only [Matrix.mul_assoc]
  rfl

end GlobalTheory.ClassSumEquiv
