module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BaseChangeResidueSurjective
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
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_co :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsCO O R], ∃ _ : IsCO O' (Til O O' R), IsLocalHom (Til.ι O O' R) ∧ Til.s O O' R ∈ maximalIdeal (Til O O' R) := by
  intro O O' _ _ _ _ _ _ _ R _ _ _
  haveI hT := UpperTheory.V.CA.cl_bc O O' R
  let f : R →+* O' ⊗[O] R := (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom
  have hint : f.IsIntegral := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact f.isIntegralElem_zero
    | tmul o r =>
      have ho : IsIntegral O ((Algebra.TensorProduct.includeLeft : O' →ₐ[O] O' ⊗[O] R) o) :=
        (Algebra.IsIntegral.isIntegral (R := O) o).map _
      rw [Algebra.TensorProduct.includeLeft_apply] at ho
      obtain ⟨p, hp, hpe⟩ := ho
      have h1 : f.IsIntegralElem (o ⊗ₜ[O] (1 : R)) := by
        refine ⟨p.map (algebraMap O R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hc : f.comp (algebraMap O R) = algebraMap O (O' ⊗[O] R) :=
          (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).comp_algebraMap
        rw [hc]
        exact hpe
      have he : o ⊗ₜ[O] r = (o ⊗ₜ[O] (1 : R)) * f r := by
        show _ = _ * ((1 : O') ⊗ₜ[O] r)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [he]
      exact RingHom.IsIntegralElem.mul f h1 f.isIntegralElem_map
    | add x y hx hy => exact RingHom.IsIntegralElem.add f hx hy
  have hloc : IsLocalHom f := by
    refine ((IsLocalRing.local_hom_tfae f).out 1 5).mpr ?_
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hint (maximalIdeal (O' ⊗[O] R))
    exact IsLocalRing.eq_maximalIdeal this
  haveI hco : IsCO O' (Til O O' R) := UpperTheory.V.Alg.co_mvps O' (O' ⊗[O] R) Unit
  refine ⟨hco, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have hr' : IsUnit (PowerSeries.C ((1 : O') ⊗ₜ[O] r) : PowerSeries (O' ⊗[O] R)) := hr
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at hr'
    exact hloc.map_nonunit r hr'
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    show ¬ IsUnit (PowerSeries.X : PowerSeries (O' ⊗[O] R))
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
