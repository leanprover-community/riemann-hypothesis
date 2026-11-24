module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeLocalizationSameFractionField
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_finiteType_localization_same_fractionField : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L), IsLocModel c R →
    ∃ (S : Subring L) (hS : ∀ a, c a ∈ S) (q : Ideal S), q.IsPrime ∧ (c.codRestrict S hS).FiniteType ∧
      (∀ f : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ f * b = a) ∧
      ∀ f : L, f ∈ R ↔ ∃ a b : S, b ∉ q ∧ f * b = a := by
  first | exact @GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization | exact GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization | (intros; apply GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization <;> assumption)
