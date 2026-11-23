module

public import Mathlib.AlgebraicGeometry.Pullbacks
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

theorem GlobalTheory.Mum.descent_eqn_of_chart_projection : ∀ (B S X G : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)) (ψ : J → (U.left ⟶ G)) (β : X ⟶ G), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ j, e j ≫ β = pullback.fst _ _ ≫ ψ j) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  intro B S X G π f Φ U J e ψ β he hcov hf hβ hch
  let 𝒰 : (pullback f (pullback.fst π π)).OpenCover :=
    Scheme.Cover.mkOfCovers J (fun j => pullback (e j) (pullback.fst f (pullback.fst π π)))
      (fun j => pullback.snd _ _) (by
        intro q
        obtain ⟨j, y, hy⟩ := (by simpa [Set.mem_range] using hcov (pullback.fst f (pullback.fst π π) q) :
          ∃ j, ∃ y, (e j) y = pullback.fst f (pullback.fst π π) q)
        obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback
          (IsPullback.of_hasPullback (e j) (pullback.fst f (pullback.fst π π))) y q hy
        exact ⟨j, p, hp⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ (fun (j : J) => ?_)
  change pullback.snd (e j) (pullback.fst f (pullback.fst π π)) ≫ _ =
    pullback.snd (e j) (pullback.fst f (pullback.fst π π)) ≫ _
  have hc := pullback.condition (f := e j) (g := pullback.fst f (pullback.fst π π))
  generalize pullback.snd (e j) (pullback.fst f (pullback.fst π π)) = z at hc ⊢
  generalize pullback.fst (e j) (pullback.fst f (pullback.fst π π)) = y₁ at hc
  have h1 : y₁ ≫ pullback.snd U.hom π = (z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.fst π π := by
    calc y₁ ≫ pullback.snd U.hom π = y₁ ≫ e j ≫ f := by rw [hf]
      _ = z ≫ pullback.fst f (pullback.fst π π) ≫ f := by rw [reassoc_of% hc]
      _ = z ≫ pullback.snd f (pullback.fst π π) ≫ pullback.fst π π := by rw [pullback.condition]
      _ = _ := (Category.assoc _ _ _).symm
  have h2 : (y₁ ≫ pullback.fst U.hom π) ≫ U.hom =
      ((z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.snd π π) ≫ π := by
    calc (y₁ ≫ pullback.fst U.hom π) ≫ U.hom = y₁ ≫ pullback.snd U.hom π ≫ π := by
          rw [Category.assoc, pullback.condition]
      _ = (z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.fst π π ≫ π := by rw [reassoc_of% h1]; simp only [Category.assoc]
      _ = _ := by rw [pullback.condition]; simp only [Category.assoc]
  have hΦ := hch j _ y₁ (pullback.lift _ _ h2) _ (pullback.lift_fst _ _ _).symm h1
    (pullback.lift_snd _ _ _) z hc.symm rfl
  calc z ≫ pullback.fst f (pullback.fst π π) ≫ β = y₁ ≫ e j ≫ β := by
        rw [reassoc_of% hc]
    _ = pullback.lift _ _ h2 ≫ e j ≫ β := by
        rw [hβ, pullback.lift_fst_assoc, Category.assoc]
    _ = z ≫ Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
        have h3 := congrArg (· ≫ β) hΦ
        simpa only [Category.assoc] using h3.symm
