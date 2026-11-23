module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
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

theorem glue_overlap_cocycle : ∀ (B S X : Scheme.{0}) (π : S ⟶ B), Surjective π → ∀ (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, V i i = ⊤) ∧ (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) := by
  intro B S X π hπ U J e he V τ hV hτ
  have hp : Function.Surjective (pullback.fst U.hom π) := (inferInstance : Surjective (pullback.fst U.hom π)).surj
  refine ⟨fun i => ?_, fun i j k x hx => ?_⟩
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨a, rfl⟩ := hp y
    exact (hV i i a).mpr ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := hp ((V i j).ι x)
    have hij : e i a ∈ Set.range (e j) := (hV i j a).mp (by
      rw [ha]
      have hx' : (V i j).ι x ∈ Set.range (V i j).ι := ⟨x, rfl⟩
      rwa [Scheme.Opens.range_ι] at hx')
    obtain ⟨b, hb⟩ := hij
    have hik : e i a ∈ Set.range (e k) := (hV i k a).mp (by rw [ha]; exact hx)
    obtain ⟨t, ht1, ht2⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (e i) (e j)) a b hb.symm
    have hrange : Set.range (pullback.fst (e i) (e j) ≫ pullback.fst U.hom π) ⊆ Set.range (V i j).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (pullback.fst U.hom π) (pullback.fst (e i) (e j) z) ∈ V i j
      rw [hV i j]
      refine ⟨pullback.snd (e i) (e j) z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    let v := IsOpenImmersion.lift (V i j).ι (pullback.fst (e i) (e j) ≫ pullback.fst U.hom π) hrange
    have hv : v ≫ (V i j).ι = pullback.fst (e i) (e j) ≫ pullback.fst U.hom π := IsOpenImmersion.lift_fac _ _ _
    have key := hτ i j _ (pullback.fst (e i) (e j)) (pullback.snd (e i) (e j)) v pullback.condition hv
    have hvt : v t = x := by
      apply (V i j).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, ht1, ha]
    have : τ i j x = pullback.fst U.hom π b := by
      rw [← hvt, ← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, ht2]
    rw [this, hV j k, hb]
    exact hik

end GlobalTheory.Mum
