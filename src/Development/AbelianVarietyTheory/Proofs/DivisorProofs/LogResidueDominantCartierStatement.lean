module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
public import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResidueDominantCartier
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.log_residue_dominant_cartier : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  first | exact @GlobalTheory.FieldPair.mult_lt_of_adjKlt | exact GlobalTheory.FieldPair.mult_lt_of_adjKlt | (intros; apply GlobalTheory.FieldPair.mult_lt_of_adjKlt <;> assumption)
