module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsRestrictMatchingOpens
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pinched_charts_restrict_matching_opens : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  first | exact @GlobalTheory.Pinch.restrict_pinched | exact GlobalTheory.Pinch.restrict_pinched | (intros; apply GlobalTheory.Pinch.restrict_pinched <;> assumption)
