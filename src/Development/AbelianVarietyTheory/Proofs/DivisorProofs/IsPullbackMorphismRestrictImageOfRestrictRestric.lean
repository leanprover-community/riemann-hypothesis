module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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

namespace GlobalTheory

theorem isPullback_morphismRestrict_image_of_restrict_restrict :
    ∀ (P' X S T : Scheme.{0}) (a : X ⟶ P') (W : P'.Opens) (V : W.toScheme.Opens) (q : X ⟶ S)
      (h : P' ⟶ T) (π : S ⟶ T),
      IsPullback ((a ∣_ W) ∣_ V) (((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι ≫ q) (V.ι ≫ W.ι ≫ h) π →
      IsPullback (a ∣_ (W.ι ''ᵁ V)) ((a ⁻¹ᵁ (W.ι ''ᵁ V)).ι ≫ q) ((W.ι ''ᵁ V).ι ≫ h) π := by
  intro P' X S T a W V q h π H
  have e1hom : ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫
      X.isoOfEq (image_morphismRestrict_preimage a W V)).hom ≫ (a ⁻¹ᵁ (W.ι ''ᵁ V)).ι =
      ((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι := by
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
  refine IsPullback.of_iso H
    ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫ X.isoOfEq (image_morphismRestrict_preimage a W V))
    (W.ι.isoImage V) (Iso.refl S) (Iso.refl T) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (W.ι ''ᵁ V).ι]
    simp only [Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι]
    rw [reassoc_of% e1hom, morphismRestrict_ι_assoc, morphismRestrict_ι]
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [reassoc_of% e1hom]
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.Hom.isoImage_hom_ι_assoc]
  · simp

end GlobalTheory
