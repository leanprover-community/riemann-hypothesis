module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SepDescent

def closedRange : MorphismProperty Scheme.{0} := fun _ _ f => IsClosed (Set.range f.base)

lemma range_iso_comp {X Y Z : Scheme.{0}} (e : X ≅ Y) (f : Y ⟶ Z) :
    Set.range (e.hom ≫ f).base = Set.range f.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.base x, by simp⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]

instance : closedRange.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    change IsClosed _
    rw [range_iso_comp]
    exact hf
  · intro X Y Z e f hf
    change IsClosed _
    have : Set.range (f ≫ e.hom).base = e.hom.base '' Set.range f.base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [this]
    exact e.hom.isClosedMap _ hf

instance : closedRange.DescendsAlong (@UniversallyClosed ⊓ @Surjective) := by
  apply MorphismProperty.DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  haveI : UniversallyClosed f := hf.1
  have hs : Function.Surjective f.base := hf.2.surj
  have e : Set.range g.base = f.base '' Set.range (pullback.fst f g).base := by
    rw [Scheme.Pullback.range_fst, Set.image_preimage_eq _ hs]
  change IsClosed _
  rw [e]
  exact f.isClosedMap _ hfst

instance : (@UniversallyClosed ⊓ @Surjective : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
  @MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _ inferInstance inferInstance

instance : (MorphismProperty.diagonal closedRange).DescendsAlong
    (@UniversallyClosed ⊓ @Surjective : MorphismProperty Scheme.{0}) :=
  inferInstance

end GlobalTheory.SepDescent


open GlobalTheory.SepDescent in
theorem GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), UniversallyClosed π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left),
    IsPullback β G'.hom G.hom π → IsSeparated G'.hom → IsSeparated G.hom := by
  intro R _ S π h1 h2 G' G β hp hs
  have hd : (MorphismProperty.diagonal closedRange) G.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal closedRange)
      (Q := @UniversallyClosed ⊓ @Surjective) hp.flip ⟨h1, h2⟩
      (pullback.diagonal G'.hom).isClosedMap.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hd⟩
