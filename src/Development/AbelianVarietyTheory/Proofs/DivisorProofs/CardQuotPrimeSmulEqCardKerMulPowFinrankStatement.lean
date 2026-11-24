module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardQuotPrimeSmulEqCardKerMulPowFinrank
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

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime], Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) = Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) * p ^ Module.finrank ℤ M := by
  first | exact @GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank | exact GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank | (intros; apply GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank <;> assumption)
