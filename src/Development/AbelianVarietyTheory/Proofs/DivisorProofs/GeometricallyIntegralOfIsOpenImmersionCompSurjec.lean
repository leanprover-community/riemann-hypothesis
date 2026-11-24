module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem geometricallyIntegral_of_isOpenImmersion_comp_surjective :
    ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  intro O Z T j f _ _ hs
  refine ⟨fun {K} _ y P fst snd h => ?_⟩
  have hZf : IsIntegral (pullback f y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) y _ _ (IsPullback.of_hasPullback f y)
  let fst' : P ⟶ pullback f y := pullback.lift (fst ≫ j) snd (by rw [Category.assoc]; exact h.w)
  have sq : IsPullback fst fst' j (pullback.fst f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd f y) (v₂₂ := f) (h₃₁ := y) ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f y)
    have e : fst' ≫ pullback.snd f y = snd := pullback.lift_snd _ _ _
    rw [e]; exact h
  have : IsOpenImmersion fst' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance
  have hsn : Surjective snd := MorphismProperty.of_isPullback (P := @Surjective) h hs
  have : Nonempty P := by
    obtain ⟨z, -⟩ := snd.surjective (Nonempty.some inferInstance : Spec (.of K))
    exact ⟨z⟩
  exact isIntegral_of_isOpenImmersion fst'

end GlobalTheory
