module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory UpperTheory.V.Af.CohB

theorem UpperTheory.cohomology_part_split :
    UpperTheory.V.Af.CohB.PartSplit := by
  classical
  intro Γ X I _ _ _ c hc d ξ
  let p : ∀ i, (X → Fin d → ℂ) →ₗ[ℂ] (↥(part c hc i) → Fin d → ℂ) := fun i =>
    { toFun := fun f x => f x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : ∀ i, (↥(part c hc i) → Fin d → ℂ) →ₗ[ℂ] (X → Fin d → ℂ) := fun i =>
    { toFun := fun f x => if h : c x = i then f ⟨x, h⟩ else 0
      map_add' := fun f g => funext fun x => by
        by_cases h : c x = i <;> simp [h]
      map_smul' := fun a f => funext fun x => by
        by_cases h : c x = i <;> simp [h] }
  refine ⟨fun i => Rep.ofHom ⟨p i, fun γ => ?_⟩, fun i => Rep.ofHom ⟨e i, fun γ => ?_⟩, ?_⟩
  · refine LinearMap.ext fun f => funext fun x => ?_
    rfl
  · refine LinearMap.ext fun f => funext fun x => ?_
    change (if h : c x = i then (funRep ↥(part c hc i) ξ γ f) ⟨x, h⟩ else 0) =
      Matrix.mulVec (ξ γ) (if h : c (γ⁻¹ • x) = i then f ⟨γ⁻¹ • x, h⟩ else 0)
    by_cases h : c x = i
    · rw [dite_eq_left h, dite_eq_left ((hc _ _).trans h)]
      rfl
    · rw [dite_eq_right h, dite_eq_right (fun h' => h ((hc _ _).symm.trans h')), Matrix.mulVec_zero]
  · apply Rep.hom_ext
    rw [Rep.sum_hom]
    apply Representation.IntertwiningMap.ext
    refine LinearMap.ext fun f => funext fun x => ?_
    rw [Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply, Finset.sum_apply]
    change ∑ i, (if h : c x = i then f x else 0) = f x
    simp
