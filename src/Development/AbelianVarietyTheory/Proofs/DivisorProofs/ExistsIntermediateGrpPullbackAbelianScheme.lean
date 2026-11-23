module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.RingTheory.DividedPowers.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory.SqLift

theorem exists_intermediate_grpPullback : ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (ρ : R →+* R₁) (π₁ : R₁ →+* R₀) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap (π₁.comp ρ)) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left),
      IsGrpPullback A₀ A₁ (spMap π₁) i₁ ∧ IsGrpPullback A₁ A (spMap ρ) i₂ ∧ i₁ ≫ i₂ = i ∧ IsAbelianScheme A₁ ∧
      SmoothOfRelativeDimension g A₁.hom := by
  intro R R₁ R₀ _ _ _ ρ π₁ g A₀ _ A _ i h hA hg
  have e : spMap (π₁.comp ρ) = spMap π₁ ≫ spMap ρ := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ := isGrpPullback_pullback A (spMap ρ)
  have hw : i ≫ A.hom = (A₀.hom ≫ spMap π₁) ≫ spMap ρ := by
    rw [h.1.w, e, Category.assoc]
  let i₁ : A₀.left ⟶ ((Over.pullback (spMap ρ)).obj A).left := h₂.1.lift i (A₀.hom ≫ spMap π₁) hw
  have c₁ : i₁ ≫ Limits.pullback.fst A.hom (spMap ρ) = i := h₂.1.lift_fst _ _ _
  have c₂ : i₁ ≫ ((Over.pullback (spMap ρ)).obj A).hom = A₀.hom ≫ spMap π₁ := h₂.1.lift_snd _ _ _
  have h₁ : IsGrpPullback A₀ ((Over.pullback (spMap ρ)).obj A) (spMap π₁) i₁ :=
    h₂.cancel (h.congr e c₁.symm) c₂
  refine ⟨(Over.pullback (spMap ρ)).obj A, Functor.grpObjObj, i₁, Limits.pullback.fst A.hom (spMap ρ), h₁, h₂, c₁,
    isAbelianScheme_pullback_obj (spMap ρ) A hA, ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg

end GlobalTheory.SqLift
