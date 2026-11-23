module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectively
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat


theorem _root_.GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N), GlobalTheory.AmpleSpan.EmbedsBy π s → ∀ (f₁ f₂ : X ⟶ Y), f₁ ≫ π = f₂ ≫ π → (∀ x : X, ∃ σ : κ → X.presheaf.stalk x, (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧ (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) → f₁ = f₂ := by
  first | (exact @GlobalTheory.HomFixGerm.eq_of_germs) | (exact GlobalTheory.HomFixGerm.eq_of_germs) | (intros; apply GlobalTheory.HomFixGerm.eq_of_germs  <;> assumption)
