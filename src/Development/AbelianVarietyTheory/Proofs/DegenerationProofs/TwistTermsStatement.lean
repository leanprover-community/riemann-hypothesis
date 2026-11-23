module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTerms
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

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.twist_terms_alt : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p : N.QT (m ^ 2)) (χ : N.X), (N.twist β u).txT m (N.twQ β u hm p) χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ ∧ (∀ (j : ℕ) (hj : j ∣ k) (q : N.QT j), j ≠ 0 → (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) + β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q q' : N.QT j), (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' ∧ N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' ∧ (N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q')) := by
  first | exact @GlobalTheory.Ex.twist_terms | exact GlobalTheory.Ex.twist_terms | (intros; apply GlobalTheory.Ex.twist_terms <;> assumption)
