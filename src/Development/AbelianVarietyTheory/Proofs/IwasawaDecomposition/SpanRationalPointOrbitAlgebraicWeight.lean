module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem span_ratPt_orbit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  intro L _ _ _ n a ι _ _ b P hA v hv w
  classical
  set x : a.W := b.equivFun.symm v with hx
  have hxv : b.repr x = v := by
    rw [← Module.Basis.equivFun_apply, hx, LinearEquiv.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    intro h
    apply hv
    rw [← hxv, h, map_zero]
    rfl
  let S0 : Submodule ℂ a.W := Submodule.span ℂ (Set.range fun γ : GQ L n => a.ρ γ x)
  have hinv : ∀ (g : GQ L n) (y : a.W), y ∈ S0 → a.ρ g y ∈ S0 := by
    intro g y hy
    have hle : S0 ≤ S0.comap (a.ρ g) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      show a.ρ g (a.ρ γ x) ∈ S0
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * γ, rfl⟩
    exact hle hy
  let S : Subrepresentation a.ρ := ⟨S0, hinv⟩
  have hxS : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hS0 : S0 = ⊤ := by
    haveI := a.irr
    rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hx0
      have h2 : S.toSubmodule = (⊥ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      have h3 : x ∈ (⊥ : Subrepresentation a.ρ).toSubmodule := h2 ▸ hxS
      change x ∈ (⊥ : Submodule ℂ a.W) at h3
      exact (Submodule.mem_bot ℂ).1 h3
    · have h2 : S.toSubmodule = (⊤ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      exact h2
  have hw : w = b.equivFun.toLinearMap (b.equivFun.symm w) := (b.equivFun.apply_symm_apply w).symm
  have hmem : b.equivFun.symm w ∈ S0 := by rw [hS0]; trivial
  rw [hw]
  have hmap : Submodule.map b.equivFun.toLinearMap S0 ≤ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
    rw [Submodule.map_span_le]
    rintro _ ⟨γ, rfl⟩
    apply Submodule.subset_span
    have hγ : (γ : GA L n) ∈ ((GQ0 L n).map (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))).subgroupOf (GA L n) := γ.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨γ₀, hγ₀, he⟩ := hγ
    refine ⟨γ₀, hγ₀, ?_⟩
    have hE : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← he]; rfl
    have hM := hA γ γ₀ hE
    show b.equivFun (a.ρ γ x) = _
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b, hxv, hM]
    rfl
  exact hmap (Submodule.mem_map_of_mem hmem)

end GlobalTheory.AlgWtHW
