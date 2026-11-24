module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotientEqOfPowSubSelfMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  first | exact @GlobalTheory.card_quotient_eq_of_pow_sub_self_mem | exact GlobalTheory.card_quotient_eq_of_pow_sub_self_mem | (intros; apply GlobalTheory.card_quotient_eq_of_pow_sub_self_mem <;> assumption)
