module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelAutActsOnRaisedModelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelLevelOneDescendsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfUnitBall
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem System.levelStructureConditions_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hpq hlev S p W hp hW i
  obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW i
  have hdvd : l₀.Dvd i.l := ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 i.l l₀ h).1
  obtain ⟨hded, hunit, -⟩ := (GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW
  have hgood : Good (S.Y p W hp hW i).t := by
    obtain ⟨b, r, ν, -, -, ⟨A⟩⟩ := hR
    exact good_pullback L3.gtBaseChange E H _ _ _ _ A.π A.mu (S.B (S.ch p) l₀ h.1).good
  refine ⟨⟨?_, fun hA => ?_, ?_, ?_, ?_, ?_⟩, hgood.2.1⟩
  · exact GlobalTheory.T.levelAut_acts_on_raised_model L1 L2 L3 E H D Xo _ _ _ hpq l₀ _ i.l i.c _ _ _ hdvd hded hR
  · exact GlobalTheory.T.raised_model_level_one_descends L1 L2 L3 E H D Xo _ _ _ hlev l₀ _ i.l i.c _ _ _ (S.aux _).1.pos hdvd hA hded hR
  · exact GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model L1 L2 L3 E H D i.l _ _ _ _ _ _ (S.Y p W hp hW i).oF _ _ (ofModel (S.Y p W hp hW i)) hded
      hgood.2.2
  · obtain ⟨U, hU, hσ⟩ := GlobalTheory.torsion_section_extends_abLocus E H D i.l _ i.c _ _ (S.Y p W hp hW i) hded hgood.1
    exact ⟨U, hU, fun a n hn => ⟨hσ _ n (hunit n hn), hσ _ n (hunit n hn)⟩⟩
  · intro V K _ _ _ _ _ _ _
    exact GlobalTheory.goodRedExt_of_isDiscreteValuationRing hext E H D i.l _ i.c _ _ _ V K
  · intro V C _ _ _ _ _ _ _ hV _
    exact GlobalTheory.GoodRedUnitBall.goodRedExt_unitBall hext E H D Xo _ _ _ l₀ _ i.l i.c _ _ _ hR V C hV

end GlobalTheory.Models
