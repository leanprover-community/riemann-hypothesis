module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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

namespace GlobalTheory.Mum

theorem isOpen_range_of_etale_of_universallyOpen_comp {Y Z T : Scheme.{0}} (i' : Z ⟶ Y) (h : Y ⟶ T)
    [Etale h] (hu : UniversallyOpen (i' ≫ h)) : IsOpen (Set.range i') := by
  have s_open : IsOpenImmersion (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback i' h) inferInstance
  have e : Set.range i' = (pullback.snd (i' ≫ h) h) '' Set.range (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  rw [e]
  exact (pullback.snd (i' ≫ h) h).isOpenMap _ (pullback.lift (𝟙 Z) i' _).isOpenEmbedding.isOpen_range

theorem exists_opens_range_eq_of_etale {X B T Z : Scheme.{0}} (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T)
    (hc : Etale c) (hj : IsPreimmersion j) (hφ : UniversallyOpen φ) (w : i ≫ c = φ ≫ j) :
    ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  let i' : Z ⟶ pullback c j := pullback.lift i φ w
  have hi' : i' ≫ pullback.snd c j = φ := pullback.lift_snd _ _ _
  have ho : IsOpen (Set.range i') :=
    isOpen_range_of_etale_of_universallyOpen_comp i' (pullback.snd c j) (by rw [hi']; exact hφ)
  have hemb := IsPreimmersion.isEmbedding (pullback.fst c j)
  obtain ⟨U, hU, hpre⟩ := hemb.isInducing.isOpen_iff.1 ho
  refine ⟨⟨U, hU⟩, ?_⟩
  have hr : Set.range i = (pullback.fst c j) '' Set.range i' := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [hr, ← hpre, Set.image_preimage_eq_inter_range, Scheme.Pullback.range_fst]
  rfl

end GlobalTheory.Mum
