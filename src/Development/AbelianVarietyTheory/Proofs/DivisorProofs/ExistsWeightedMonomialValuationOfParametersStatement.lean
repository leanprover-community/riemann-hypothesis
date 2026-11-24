module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParameters
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

theorem _root_.GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q), letI := hQ.isLocalRing;
  ∀ (r N : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
  IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
  (∃ x : Fin N → L, TrBasis c x) →
  ∃ V : Place c, V.Contains Q ∧ (∀ q : Q, IsUnit q → V.ord q = 0) ∧ (∀ i, V.ord (z i) = wt i) ∧
    (∀ (d : ℕ) (q : Q), (q : L) ≠ 0 → q ∈ IsLocalRing.maximalIdeal Q ^ d → (d : ℤ) ≤ V.ord q) ∧
    ∀ y : Fin N → Q, IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) y) →
      V.formOrd (dForm c (fun i => (y i : L))) + 1 ≤ ∑ i, (wt i : ℤ) := by
  first | exact @GlobalTheory.MonoVal.monomial_place | exact GlobalTheory.MonoVal.monomial_place | (intros; apply GlobalTheory.MonoVal.monomial_place <;> assumption)
