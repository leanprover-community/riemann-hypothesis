module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open Limits

namespace GlobalTheory

theorem range_closedImmersion_eq_closure_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] (i : Y ⟶ X)
    [IsClosedImmersion i] : Set.range i = closure {i (genericPoint Y)} := by
  have hc : IsClosedMap i := i.isClosedEmbedding.isClosedMap
  have h1 : Set.range i = i '' closure {genericPoint Y} := by
    rw [(genericPoint_spec Y).def, Set.image_univ]
  rw [h1]
  apply le_antisymm
  · exact image_closure_subset_closure_image i.continuous |>.trans (by rw [Set.image_singleton])
  · rw [← Set.image_singleton]
    exact closure_minimal (Set.image_mono subset_closure) (hc _ isClosed_closure)

theorem iso_of_closedImmersion_genericPoint_eq :
    ∀ (X Y Y' : Scheme.{0}) [IsIntegral Y] [IsIntegral Y'] (i : Y ⟶ X) (i' : Y' ⟶ X)
      [IsClosedImmersion i] [IsClosedImmersion i'], i (genericPoint Y) = i' (genericPoint Y') →
      ∃ g : Y' ⟶ Y, IsIso g ∧ g ≫ i = i' ∧ g (genericPoint Y') = genericPoint Y := by
  intro X Y Y' _ _ i i' _ _ h
  have hr : Set.range i = Set.range i' := by
    rw [range_closedImmersion_eq_closure_genericPoint, range_closedImmersion_eq_closure_genericPoint, h]
  have hs : Function.Surjective (pullback.snd i i') := by
    intro y'
    obtain ⟨y, hy⟩ : i' y' ∈ Set.range i := hr ▸ ⟨y', rfl⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy
    exact ⟨z, hz⟩
  have hf : Function.Surjective (pullback.fst i i') := by
    intro y
    obtain ⟨y', hy⟩ : i y ∈ Set.range i' := hr ▸ ⟨y, rfl⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy.symm
    exact ⟨z, hz⟩
  haveI : Surjective (pullback.snd i i') := ⟨hs⟩
  haveI : Surjective (pullback.fst i i') := ⟨hf⟩
  haveI : IsIso (pullback.snd i i') := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso (pullback.fst i i') := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.snd i i') ≫ pullback.fst i i', inferInstance, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    have e := congrArg (fun f : Y' ⟶ X => f (genericPoint Y')) (show (inv (pullback.snd i i') ≫ pullback.fst i i') ≫ i = i' by
      rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc])
    rw [Scheme.Hom.comp_apply] at e
    rw [e, h]

end GlobalTheory
