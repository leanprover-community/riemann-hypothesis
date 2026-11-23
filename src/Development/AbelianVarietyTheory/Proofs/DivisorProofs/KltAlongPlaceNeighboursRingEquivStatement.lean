module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.kltAlongPlaceNeighbours_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (T : Subring K) (φ : K →₀ ℚ) (S : Place c) (S' : Place c'), TrBasis c x → (∀ a, e a ∈ S'.ring ↔ a ∈ S.ring) → AdjKlt c n T S (dForm c x) φ → AdjKlt c' n (T.map e.toRingHom) S' (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) := by
  first | exact @GlobalTheory.FieldPair.adjKlt_ringEquiv | exact GlobalTheory.FieldPair.adjKlt_ringEquiv | (intros; apply GlobalTheory.FieldPair.adjKlt_ringEquiv <;> assumption)
