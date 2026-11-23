module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem abelianScheme_constLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (s : R₀ →+* R), π.comp s = RingHom.id R₀ →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left) (_ : IsGrpPullback A₀ A (spMap π) i),
        IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom := by
  intro R R₀ _ _ π s hs A₀ _ g hA hg
  have hAs := isGrpPullback_pullback A₀ (spMap s)
  have hid : spMap π ≫ spMap s = 𝟙 (Sp R₀) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
    exact Spec.map_id _
  have hBA := isGrpPullback_pullback ((Over.pullback (spMap s)).obj A₀) (spMap π)
  have hB0 := (hBA.comp hAs).congr hid rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso hB0 (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h0B := isGrpPullback_of_iso e.symm
  refine ⟨(Over.pullback (spMap s)).obj A₀, inferInstance, _, (h0B.comp hBA).congr (Category.id_comp _) rfl,
    isAbelianScheme_pullback_obj (spMap s) A₀ hA, ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg

end GlobalTheory
