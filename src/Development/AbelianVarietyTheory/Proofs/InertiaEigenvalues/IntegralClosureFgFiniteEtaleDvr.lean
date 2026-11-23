module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NormDetMulProdSqLeOfEntryLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.IntegralClosureFG

theorem integralClosure_fg (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A] :
    (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  classical
  let b0 := Module.finBasis E A
  have hex : ∀ i, ∃ d : O, d ≠ 0 ∧ IsIntegral O (d • b0 i) := by
    intro i
    have h : IsAlgebraic E (b0 i) := Algebra.IsAlgebraic.isAlgebraic _
    have h' : IsAlgebraic O (b0 i) := (IsFractionRing.isAlgebraic_iff O E A).2 h
    obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
    exact ⟨d, hd, hi⟩
  choose d hd0 hdi using hex
  have hu : ∀ i, IsUnit (algebraMap O E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let D : E := (Algebra.traceMatrix E b).det
  have hD : D ≠ 0 := by
    have h1 := (GlobalTheory.discr_ne_zero_iff_of_etale (K := E) (A := A)
      (by simp) (b : Fin (Module.finrank E A) → A)).2 b.linearIndependent
    rwa [Algebra.discr_def] at h1
  have hint : ∀ e : E, IsIntegral O e → ∃ u : O, algebraMap O E u = e := by
    intro e he
    exact IsIntegrallyClosed.isIntegral_iff.1 he
  let S : Submodule O A := Submodule.span O (Set.range fun j => D⁻¹ • b j)
  have hS : S.FG := Submodule.fg_span (Set.finite_range _)
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ S := by
    intro x hx
    have hx' : IsIntegral O x := hx
    obtain ⟨v, hv⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum O E A (Fin (Module.finrank E A)) b x
      (fun i j => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        ((hb i).mul (hb j))))
      (fun i => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        (hx'.mul (hb i))))
    have hx2 : x = ∑ j, v j • (D⁻¹ • b j) := by
      have : x = D⁻¹ • (D • x) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
      rw [this, hv, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← algebraMap_smul E (v j) (D⁻¹ • b j), smul_smul, mul_comm]
    rw [hx2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI : IsNoetherian O S := isNoetherian_of_fg_of_noetherian S hS
  exact isNoetherian_submodule.1 this _ hle

end GlobalTheory.IntegralClosureFG
