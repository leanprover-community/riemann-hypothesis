module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

theorem tensInc : TensInc := by
  intro k _ _ _ _ s d V _ _ σ
  refine ⟨PiTensorProduct.map fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype, ?_, ?_⟩
  · intro u w h
    have hl : ∀ a, ∃ g : V a →ₗ[ℂ] fixed (σ a) (KOne k (Fin (d a))),
        g ∘ₗ (fixed (σ a) (KOne k (Fin (d a)))).subtype = LinearMap.id := fun a =>
      LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
    choose g hg using hl
    have e : PiTensorProduct.map g ∘ₗ
        (PiTensorProduct.map fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) = LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      simp only [hg]
      exact PiTensorProduct.map_id
    have h1 := LinearMap.congr_fun e u
    have h2 := LinearMap.congr_fun e w
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, h]
  · intro x z
    have key : ∀ a, (fixed (σ a) (KOne k (Fin (d a)))).subtype ∘ₗ
        levelZero (σ a) (redLevi k (fun a => Fin (d a)) x a) =
          σ a ((x : (a : Fin s) → GL (Fin (d a)) k) a) ∘ₗ (fixed (σ a) (KOne k (Fin (d a)))).subtype :=
      fun a => LinearMap.ext fun v => levelZero_apply (σ a) ⟨_, x.2 a (Set.mem_univ a)⟩ v
    change (PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) ∘ₗ
        PiTensorProduct.map (fun a => levelZero (σ a) (redLevi k (fun a => Fin (d a)) x a))) z =
      (PiTensorProduct.map (fun a => σ a ((x : (a : Fin s) → GL (Fin (d a)) k) a)) ∘ₗ
        PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype)) z
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    simp only [key]

end UpperTheory.Gal.InertialTypesAlt
