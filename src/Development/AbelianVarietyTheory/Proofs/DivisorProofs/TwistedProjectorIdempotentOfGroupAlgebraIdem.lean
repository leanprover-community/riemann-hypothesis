module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace GlobalTheory

theorem eOp_comp_self_of_conv_idem {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL)
    (he : ∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) : A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  set c : G0 → LL := fun g => eC g * ((A.chi g)⁻¹ : LLˣ) with hc
  have hchi : ∀ g k : G0, (((A.chi g)⁻¹ : LLˣ) : LL) * (((A.chi (g⁻¹ * k))⁻¹ : LLˣ) : LL)
      = (((A.chi k)⁻¹ : LLˣ) : LL) := by
    intro g k
    rw [← Units.val_mul, ← mul_inv, ← map_mul, mul_inv_cancel_left]
  have hcc : ∀ k, ∑ g, c g * c (g⁻¹ * k) = c k := by
    intro k
    calc ∑ g, c g * c (g⁻¹ * k)
        = ∑ g, (eC g * eC (g⁻¹ * k)) * (((A.chi k)⁻¹ : LLˣ) : LL) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [hc, ← hchi g k]; ring
      _ = c k := by rw [← Finset.sum_mul, he k]
  have hE : A.eOp eC = ∑ g, c g • A.ρ g := rfl
  rw [← Module.End.mul_eq_comp, hE, Finset.sum_mul_sum]
  calc ∑ g, ∑ h, (c g • A.ρ g) * (c h • A.ρ h)
      = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • A.ρ k := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft g) (fun k => (c g * c (g⁻¹ * k)) • A.ρ k)]
        refine Finset.sum_congr rfl fun h _ => ?_
        simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul_comm]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • A.ρ k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, c k • A.ρ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcc k]

end GlobalTheory
