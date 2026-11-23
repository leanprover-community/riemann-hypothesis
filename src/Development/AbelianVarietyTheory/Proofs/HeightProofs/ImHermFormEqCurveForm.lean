module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CurveFormSign
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

namespace GlobalTheory.CMPointCompare


variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} {B G' : Over Y} [GrpObj C] [GrpObj G] [GrpObj B] [GrpObj G']
  {f : Y ⟶ S} {x : Y ⟶ X} {β : B.left ⟶ C.left} {π : G'.left ⟶ G.left}

variable (hβ : IsGrpPullback B C f β) (hπ : IsGrpPullback G' G x π)



variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} [GrpObj C] [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}
  {Φ : MapOver C G f x}


section General

open GlobalTheory.CM

theorem hom_ext_of_complexPoints {R : Type} [CommRing R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {B G : Over (Sp R)} [Smooth B.hom] [IsSeparated G.hom] {a b : B ⟶ G}
    (h : ∀ p : Over.mk (spMap σ) ⟶ B, p ≫ a = p ≫ b) : a = b := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom σ) hσ
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback B.hom (spMap σ)) ?_
  have : IsReduced (pullback B.hom (spMap σ)) :=
    isReduced_of_smooth_complex _ (pullback.snd B.hom (spMap σ)) inferInstance
  refine ComplexPoints.hom_ext_of_points (pullback.snd B.hom (spMap σ)) G.hom (by simp) fun x hx => ?_
  have e := congrArg (fun z => z.left) (h (Over.homMk (x ≫ pullback.fst _ _) (by
    show (x ≫ _) ≫ _ = spMap σ
    rw [Category.assoc, pullback.condition, reassoc_of% hx])))
  exact (Category.assoc _ _ _).symm.trans (e.trans (Category.assoc _ _ _))

end General


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)


end GlobalTheory.CMPointCompare
