module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.compl :
    UpperTheory.V.Af.StrongMultiplicityOne.Compl := by
  intro E _ _ n μ _ U l hs
  have hStable : Fb.Stab (orthRel (CuspidalSpectrum.cuspToL2 μ) (centralCuspForms E n) U) := by
    refine ⟨fun X φ hφ => ?_, fun k φ hφ => ?_, fun g φ hφ => ?_⟩
    · refine map_mem_orthRel (A' := fun y => -(gkModuleCusp E n).ρ X y) (Fb.stab_central.ρ X)
        (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hs.ρ X u hu)) hφ
      rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
      exact petersson_inner_lieAlgebra_skewAdjoint μ X (l hx) hy
    · refine map_mem_orthRel (A' := (gkModuleCusp E n).σ k⁻¹) (Fb.stab_central.σ k)
        (fun x hx y hy => ?_) (hs.σ k⁻¹) hφ
      have hInv : (gkModuleCusp E n).σ k ((gkModuleCusp E n).σ k⁻¹ x) = x := by
        change ((gkModuleCusp E n).σ k * (gkModuleCusp E n).σ k⁻¹) x = x
        simp only [← map_mul (gkModuleCusp E n).σ k k⁻¹, mul_inv_cancel, map_one,
          one_apply_eq_self]
      exact (petersson_inner_maximalCompact_invariant μ k (l (hs.σ k⁻¹ x hx)) hy).symm.trans
        (congrArg (fun z => inner ℂ (CuspidalSpectrum.cuspToL2 μ z)
          (CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp E n).σ k y))) hInv)
    · refine map_mem_orthRel (A' := finRepCusp E n g⁻¹) (Fb.stab_central.τ g)
        (fun x hx y hy => ?_) (hs.τ g⁻¹) hφ
      have hInv : finRepCusp E n g (finRepCusp E n g⁻¹ x) = x := by
        change (finRepCusp E n g * finRepCusp E n g⁻¹) x = x
        simp only [← map_mul (finRepCusp E n) g g⁻¹, mul_inv_cancel, map_one,
          one_apply_eq_self]
      exact (petersson_inner_finiteAdelic_invariant μ g (l (hs.τ g⁻¹ x hx)) hy).symm.trans
        (congrArg (fun z => inner ℂ (CuspidalSpectrum.cuspToL2 μ z)
          (CuspidalSpectrum.cuspToL2 μ (finRepCusp E n g y))) hInv)
  exact ⟨orthRel (CuspidalSpectrum.cuspToL2 μ) (centralCuspForms E n) U,
    hStable, CuspidalSpectrum.sup_orthRel_centralCuspForms μ U l hs.ρ hs.τ,
    fun φ hφ φ' hφ' => hφ'.2 φ hφ⟩
