module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InversionOfAdjunctionProj
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

theorem _root_.GlobalTheory.T.inversion_of_adjunction_proj_alt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g f : X.functionFieldˣ) (y : X) (S : DivOver p), TrBasis (Cartier.constFn p) x → 0 < m → IsIntegrallyClosed (X.presheaf.stalk y) → RegAt y (f : X.functionField) → (placeEquiv p S).IsPrimeOf (locRing y) → S.ord f = 1 → discrep S (dForm (Cartier.constFn p) x) m g = -1 → (∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing y) → discrep E (dForm (Cartier.constFn p) x) m g ≤ 0) → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ E : DivOver p, E.Through y → -1 < discrep E (dForm (Cartier.constFn p) x) m g + E.ord f := by
  first | exact @GlobalTheory.inversion_of_adjunction_proj | exact GlobalTheory.inversion_of_adjunction_proj | (intros; apply GlobalTheory.inversion_of_adjunction_proj <;> assumption)
