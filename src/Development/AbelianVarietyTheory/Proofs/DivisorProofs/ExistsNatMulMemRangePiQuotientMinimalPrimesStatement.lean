module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulMemRangePiQuotientMinimalPrimes
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


theorem _root_.GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧ ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)), (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈ (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  first | exact @GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes | exact GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes | (intros; apply GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes <;> assumption)
