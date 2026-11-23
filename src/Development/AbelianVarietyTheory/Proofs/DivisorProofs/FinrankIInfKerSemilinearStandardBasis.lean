module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_semilinear : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V]
    [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V),
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ →
    ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V),
      (∀ i v, a' i (f v) = f (a i v)) →
      finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) =
        finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  intro K V ι _ _ _ _ σ N f hli hsp a a' ha
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Module K V := Module.compHom V σ
  haveI : IsScalarTower K ℂ V := ⟨fun k c v => by
    show (σ k * c) • v = σ k • c • v
    rw [mul_smul]⟩
  let g : (Fin N → K) →ₗ[K] V :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun k x => f.map_smulₛₗ k x }
  have hsp' : Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩

    rw [← (Pi.basisFun K (Fin N)).sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [f.map_smulₛₗ, Pi.basisFun_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis (Fin N) ℂ V := Basis.mk hli hsp'.ge
  have hc : ∀ k, c k = f (Pi.single k 1) := fun k => Basis.mk_apply _ _ _
  let e := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv c (Equiv.refl _)
  have hbc : IsBaseChange ℂ g := by
    refine IsBaseChange.of_equiv e fun m => ?_
    have h : (e.toLinearMap.restrictScalars K ∘ₗ TensorProduct.mk K ℂ (Fin N → K) 1) = g := by
      refine (Pi.basisFun K (Fin N)).ext fun k => ?_
      have := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv_apply k c (Equiv.refl _)
      rw [Algebra.TensorProduct.basis_apply] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [this, Equiv.refl_apply, hc, Pi.basisFun_apply]
      rfl
    exact congrArg (fun φ => φ m) h
  exact (finrank_iInf_ker_baseChange K ℂ (Fin N → K) V ι g hbc a a' ha).1

end GlobalTheory.BadCount
