module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularQuotientPrimeElement
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

theorem _root_.GlobalTheory.T.regular_quotient_prime_element : ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P → IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  first | exact @_root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | exact _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | (intros; apply _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient <;> assumption)
