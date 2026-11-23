module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalQuotientTransitionIsomorphisms
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_local_quotient_transition_isomorphisms : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) →
    ∃ b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left,
      (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) ∧
      (∀ j k, IsPullback (b j k) (pullback.fst _ _ ≫ (B j).hom) ((B k).hom ≫ 𝒰.f k) (𝒰.f j)) ∧
      ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left := by
  first | exact @GlobalTheory.QuotTransition.exists_transition | exact GlobalTheory.QuotTransition.exists_transition | (intros; apply GlobalTheory.QuotTransition.exists_transition <;> assumption)
