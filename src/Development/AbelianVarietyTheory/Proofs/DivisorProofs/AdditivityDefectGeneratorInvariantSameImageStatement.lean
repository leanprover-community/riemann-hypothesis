module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivityDefectGeneratorInvariantSameImage
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer


theorem _root_.GlobalTheory.T.additivityDefect_generator_invariant_same_image : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsMonHom i → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → IsEquivGen i q χ M e → ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ (A ⊗ (A ⊗ T)).left), y₁ ≫ (pmap2 q T).left = y₂ ≫ (pmap2 q T).left → ∀ (k : (addBundle M).ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)), res h₁ (pullU y₁ _ (addGen q M e k)) = res h₂ (pullU y₂ _ (addGen q M e k)) := by
  first | exact @GlobalTheory.CharKer.addGen_invariant | exact GlobalTheory.CharKer.addGen_invariant | (intros; apply GlobalTheory.CharKer.addGen_invariant <;> assumption)
