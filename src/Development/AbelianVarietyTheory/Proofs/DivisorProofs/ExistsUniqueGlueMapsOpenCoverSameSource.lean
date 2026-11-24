module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GlueDesc

theorem exists_unique_glue : ∀ (X Y P : Scheme.{0}) (J : Type) (e : J → (P ⟶ X)) (g : J → (P ⟶ Y)), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ P), a ≫ e i = b ≫ e j → a ≫ g i = b ≫ g j) → ∃ β : X ⟶ Y, (∀ j, e j ≫ β = g j) ∧ ∀ β' : X ⟶ Y, (∀ j, e j ≫ β' = g j) → β' = β := by
  intro X Y P J e g he hcov hcomp
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers J (fun _ => P) e (fun x => by
    obtain ⟨j, y, hy⟩ := hcov x
    exact ⟨j, y, hy⟩)
  have hm : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j :=
    fun i j => hcomp i j _ _ _ pullback.condition
  refine ⟨𝒰.glueMorphisms g hm, fun j => 𝒰.ι_glueMorphisms g hm j, fun β' hβ' => ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  change e j ≫ β' = e j ≫ _
  rw [hβ' j]
  exact (𝒰.ι_glueMorphisms g hm j).symm

end GlobalTheory.GlueDesc
