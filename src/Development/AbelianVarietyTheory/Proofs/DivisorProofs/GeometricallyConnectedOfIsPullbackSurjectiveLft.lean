module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geometricallyConnected_of_isPullback_of_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  intro R _ S π hlft hsurj G' G β hpb hG'
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let jK : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨t, ht⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := AlgebraicClosure K) π (jK ≫ y)
  have hct : ConnectedSpace ↥(pullback G'.hom t) :=
    pullback_of_geometrically hG'.geometrically_connectedSpace _ t
  have hP : IsPullback (pullback.fst G'.hom t ≫ β) (pullback.snd G'.hom t) G.hom (t ≫ π) :=
    (IsPullback.of_hasPullback G'.hom t).paste_horiz hpb
  rw [← ht] at hP
  have hc' : ConnectedSpace ↥(pullback G.hom (jK ≫ y)) :=
    hP.isoPullback.hom.homeomorph.connectedSpace_iff.mp hct
  have hjK : Surjective jK := ⟨fun z ↦ by
    obtain ⟨w⟩ : Nonempty ↥(Spec (.of (AlgebraicClosure K))) := inferInstance
    exact ⟨w, Subsingleton.elim _ _⟩⟩
  have hc'' : ConnectedSpace ↥(pullback (pullback.snd G.hom y) jK) :=
    (pullbackLeftPullbackSndIso G.hom y jK).hom.homeomorph.connectedSpace_iff.mpr hc'
  exact (pullback.fst (pullback.snd G.hom y) jK).surjective.connectedSpace
    (pullback.fst (pullback.snd G.hom y) jK).continuous

end GlobalTheory.Mum
