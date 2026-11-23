module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem hom_descends_to_fg_intermediateField : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (A B : Over (Sp K)) (f : (Over.pullback (spMap (algebraMap K C))).obj A ⟶ (Over.pullback (spMap (algebraMap K C))).obj B), LocallyOfFiniteType A.hom → QuasiCompact A.hom → IsSeparated A.hom → LocallyOfFiniteType B.hom → ∃ (L : IntermediateField K C) (f₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ B.left), L.FG ∧ f₀ ≫ B.hom = pullback.fst _ _ ≫ A.hom ∧ ∀ i : pullback A.hom (spMap (algebraMap K C)) ⟶ pullback A.hom (spMap (algebraMap K L)), i ≫ pullback.fst _ _ = pullback.fst _ _ → i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (algebraMap L C) → i ≫ f₀ = f.left ≫ pullback.fst _ _ := by
  intro K C _ _ _ A B f _ _ _ _
  have hw : f.left ≫ pullback.snd B.hom (spMap (algebraMap K C)) =
      pullback.snd A.hom (spMap (algebraMap K C)) := by
    simpa using Over.w f
  have hφ : (f.left ≫ pullback.fst _ _) ≫ B.hom = pullback.fst _ _ ≫ A.hom := by
    rw [Category.assoc, pullback.condition, reassoc_of% hw, pullback.condition]
  obtain ⟨R, ψ, hR, hψ, hRψ⟩ := Spread.exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) hφ
  obtain ⟨t, rfl⟩ := hR
  let L : IntermediateField K C := IntermediateField.adjoin K (t : Set C)
  have hle : Algebra.adjoin K (t : Set C) ≤ L.toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨L, Spread.bcMap A.hom (Subalgebra.inclusion hle) ≫ ψ, ⟨t, rfl⟩, ?_, ?_⟩
  · rw [Category.assoc, hψ, Spread.bcMap_fst_assoc]
  · intro i h₁ h₂
    rw [Spread.eq_bcMap A.hom L.val h₁ h₂, ← Category.assoc,
      Spread.bcMap_comp_of_eq A.hom _ _ (Algebra.adjoin K (t : Set C)).val fun _ ↦ rfl, hRψ]

end GlobalTheory
