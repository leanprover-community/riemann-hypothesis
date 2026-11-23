module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isFrame_tens : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  intro X C _ V hV L L' u u' ⟨τ, hτg, hτf⟩ ⟨τ', hτ'g, hτ'f⟩
  dsimp only [IsFrame, IsGenOn, tens]
  refine ⟨fun T p ↦ res (inf_le_inf_left (V T) (inf_le_left : L.U p.1 ⊓ L'.U p.2 ≤ L.U p.1)) (τ T p.1) *
      res (inf_le_inf_left (V T) (inf_le_right : L.U p.1 ⊓ L'.U p.2 ≤ L'.U p.2)) (τ' T p.2), ?_, ?_⟩
  · intro T p q
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτg T p.1 q.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'g T p.2 q.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L.U p.1 ⊓ L.U q.1 := ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L'.U p.2 ⊓ L'.U q.2 := ⟨⟨hy.1.1, hy.1.2.2⟩, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ L.U p.1 ⊓ L'.U p.2 ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.2, hy.2⟩
    have m4 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := hy.1
    have m5 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m3, gm_res (𝟙 X) y _ m4, gm_res (𝟙 X) y _ m5]
    rw [h1, h2]
    ac_rfl
  · intro T T' a p
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτf T T' a p.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'f T T' a p.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L.U p.1 := ⟨hy.1, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L'.U p.2 := ⟨hy.1, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := ⟨hV a hy.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m1, gm_res (𝟙 X) y _ m2, gm_res (𝟙 X) y _ m3]
    rw [h1, h2]
    ac_rfl

end GlobalTheory.LBObs
