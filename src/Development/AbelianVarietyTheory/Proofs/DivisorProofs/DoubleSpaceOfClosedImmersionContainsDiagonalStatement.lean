module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceOfClosedImmersionContainsDiagonal
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) → Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ h) → IsProjOver (p₁ ≫ Y.str) ∧ ∃ δ : Y.X ⟶ Z, IsClosedImmersion δ ∧ δ ≫ p₁ = 𝟙 _ ∧ δ ≫ p₂ = 𝟙 _ ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ := by
  first | exact @GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift | exact GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift | (intros; apply GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift <;> assumption)
