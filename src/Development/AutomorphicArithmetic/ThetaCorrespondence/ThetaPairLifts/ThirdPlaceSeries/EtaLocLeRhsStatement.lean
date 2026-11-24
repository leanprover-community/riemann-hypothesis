module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaLocLeRhs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.star_bound_of_paired_character_condition : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ (constantSecondHub C1 : ℝ) (CT : ℕ), 0 ≤ constantSecondHub → 1 ≤ C1 → (CT : ℝ) ≤ L.sc.b → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) constantSecondHub CT → MultLe L → TwistedPlaces.ParametersPolynomiallyBounded L C1 P → SizeG L → StarH L (2000 * (constantSecondHub + 1) + 5 * C1) := by
  first | exact @_root_.GlobalTheory.NLinkTyp.main_alt_alt | exact _root_.GlobalTheory.NLinkTyp.main_alt_alt | (intros; apply _root_.GlobalTheory.NLinkTyp.main_alt_alt <;> assumption)
end
