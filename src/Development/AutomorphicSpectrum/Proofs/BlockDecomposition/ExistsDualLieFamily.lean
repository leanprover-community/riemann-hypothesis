module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieActionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModelStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem dualFam_exists : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  intro n E
  obtain ⟨e, ρ', hc, hiso, hint⟩ := GlobalTheory.T.unitary_euclidean_model E
  obtain ⟨F, hgl, -, hder⟩ := GlobalTheory.T.exists_compact_lie_action _ ρ' hc hiso
  refine ⟨fun a b => e.symm.toLinearMap ∘ₗ F a b ∘ₗ e.toLinearMap, ?_, ?_⟩
  · intro a b c d
    ext1 ξ
    have h := LinearMap.congr_fun (hgl a b c d) (e ξ)
    apply e.injective
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_sub] at h ⊢
    rw [h]
    split_ifs <;> simp
  · intro X γ hX hγ ξ
    let eL : EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] (E.V →L[ℂ] ℂ) :=
      LinearMap.toContinuousLinearMap e.symm.toLinearMap
    have heL : ∀ w, eL w = e.symm w := fun _ => rfl
    have h := (eL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder X γ hX hγ (e ξ))
    have hf : (fun t : ℝ => ξ ∘L E.ρ (γ t)⁻¹) = (eL.restrictScalars ℝ) ∘ fun t : ℝ => ρ' (γ t) (e ξ) := by
      funext t
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', heL, ← hint,
        LinearEquiv.symm_apply_apply]
    rw [hf]
    refine h.congr_deriv ?_

    simp only [ContinuousLinearMap.coe_restrictScalars', map_sum, map_smul, heL, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

end GlobalTheory.CompanionTheory.RealCountG
