module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsSpanTwistedOfIndepSpan
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
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.pullbackSectionsSpanTwisted_of_indep_span : ∀ (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), L.IsLB → (∀ W : T.Opens, GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W) → GlobalTheory.RelBasis.BoxSpan b p₁ p₂ := by
  first | exact @GlobalTheory.RelBasis.boxSpan_of_indep_span | exact GlobalTheory.RelBasis.boxSpan_of_indep_span | (intros; apply GlobalTheory.RelBasis.boxSpan_of_indep_span <;> assumption)
