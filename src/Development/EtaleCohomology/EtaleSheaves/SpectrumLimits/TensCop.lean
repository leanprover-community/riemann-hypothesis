module

public import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits
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
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

open PiTensorProduct in
theorem tensCop : TensCop := by
  intro A A' _ _ φ n
  letI : Algebra A A' := φ.toAlgebra
  refine ⟨PiTensorProduct A (fun _ : Fin (n + 1) => A'), inferInstance, algebraMap A _, fun i => (singleAlgHom (A := fun _ => A') i).toRingHom,
    fun i => ?_, ?_, ?_⟩
  · exact (singleAlgHom (A := fun _ => A') i).comp_algebraMap
  · rw [eq_top_iff]
    intro x _
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [Algebra.smul_def]
      refine Subring.mul_mem _ ?_ ?_
      · rw [← (singleAlgHom (A := fun _ => A') 0).commutes r]
        exact Subring.subset_closure (Set.mem_iUnion.2 ⟨0, _, rfl⟩)
      · have : tprod A f = ∏ i, singleAlgHom (A := fun _ => A') i (f i) := by
          simp only [singleAlgHom_apply, ← tprod_prod]
          congr 1
          exact (Finset.univ_prod_mulSingle f).symm
        rw [this]
        exact Subring.prod_mem _ fun i _ => Subring.subset_closure (Set.mem_iUnion.2 ⟨i, _, rfl⟩)
    | add x y hx hy => exact Subring.add_mem _ (hx trivial) (hy trivial)
  · intro R _ g c hg
    letI : Algebra A R := c.toAlgebra
    have hc : ∀ i r, g i (algebraMap A A' r) = algebraMap A R r := fun i r => by
      change g i (φ r) = c r
      rw [← RingHom.comp_apply, hg i]
    let ga : Fin (n + 1) → (A' →ₐ[A] R) := fun i => AlgHom.mk (g i) (hc i)
    let F : (Π _ : Fin (n + 1), A') →ₘₗ[A] R :=
      (MultilinearMap.mkPiAlgebra A (Fin (n + 1)) R).compLinearMap (fun i => (ga i).toLinearMap)
    let H := liftAlgHom F (by simp [F]) (by intro x y; simp [F, Finset.prod_mul_distrib])
    have hH : ∀ i a, H (singleAlgHom (A := fun _ => A') i a) = g i a := by
      intro i a
      change lift F (tprod A (MonoidHom.mulSingle (fun _ => A') i a)) = _
      rw [lift.tprod]
      simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      rw [Finset.prod_eq_single i]
      · simp [ga]
      · intro j _ hj
        simp [ga, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
      · simp
    refine ⟨H.toRingHom, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
    · ext a
      exact hH i a
    · ext a
      exact H.commutes a
    · have hc2 : ∀ r, h2 (algebraMap A (PiTensorProduct A (fun _ : Fin (n + 1) => A')) r) = algebraMap A R r := fun r => by
        change h2 (algebraMap A _ r) = c r
        rw [← RingHom.comp_apply, h2c]
      let H2 : (PiTensorProduct A (fun _ : Fin (n + 1) => A')) →ₐ[A] R := AlgHom.mk h2 hc2
      have : H2 = H := by
        apply PiTensorProduct.algHom_ext
        intro i
        ext a
        change h2 (singleAlgHom (A := fun _ => A') i a) = H (singleAlgHom (A := fun _ => A') i a)
        rw [hH]
        exact RingHom.congr_fun (h2l i) a
      exact congrArg AlgHom.toRingHom this

end LateralTheory.E.LevelsGenPf
