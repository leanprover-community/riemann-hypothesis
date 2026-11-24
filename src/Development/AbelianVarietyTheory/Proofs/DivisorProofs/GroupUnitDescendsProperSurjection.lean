module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pullback_one_left_fst {S P : Scheme.{0}} (f : P ⟶ S) (G' : Over S) [GrpObj G'] :
    (η[(Over.pullback f).obj G'] : _ ⟶ _).left ≫ pullback.fst G'.hom f = f ≫ η[G'].left := by
  simp [Functor.monObjObj]

theorem descend_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R))
    (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom →
    pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β →
    ∃ e : 𝟙_ (Over (Sp R)) ⟶ G, ∀ (T : Over S),
      (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hβ φ hφ hc
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_id_snd
  have hfl : Flat (𝟙 (Sp R)) := inferInstance

  have heq : pullback.fst π π ≫ (η[G'].left ≫ β) = pullback.snd π π ≫ (η[G'].left ≫ β) := by
    have h1 := pullback_one_left_fst (pullback.fst π π) G'
    have h2 := pullback_one_left_fst (pullback.snd π π) G'
    have hu : (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left =
        (η : _ ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    calc pullback.fst π π ≫ (η[G'].left ≫ β)
        = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β := by
          rw [reassoc_of% h1]
      _ = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left ≫
            pullback.fst G'.hom (pullback.snd π π) ≫ β := by rw [hc]
      _ = pullback.snd π π ≫ (η[G'].left ≫ β) := by rw [reassoc_of% hu, reassoc_of% h2]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S G.left π (𝟙 _) π (𝟙 S) hP hS hI hfl sq _ heq

  have hepi : ∀ {W : Scheme.{0}} (a b : Sp R ⟶ W), π ≫ a = π ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc'⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S W π (𝟙 _) π (𝟙 S) hP hS hI hfl sq (π ≫ a)
      (by rw [pullback.condition_assoc])
    exact (hc' a rfl).trans (hc' b hab.symm).symm
  have hsec : h₀ ≫ G.hom = 𝟙 (Sp R) := by
    apply hepi
    rw [reassoc_of% hh₀, hβ.w]
    simp
  refine ⟨Over.homMk h₀ (by simpa using hsec), fun T => ?_⟩
  simp [Hom.one_def]
  rw [hh₀]

end GlobalTheory.Mum
