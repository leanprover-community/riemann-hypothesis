module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_int_smul_mem_adicCompletionIntegers_of_elt (v : HeightOneSpectrum ℤ) (a : v.adicCompletion ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : v.adicCompletion ℚ) * a ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨d, hd, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [mul_comm]
  simpa using h

theorem exists_int_smul_isIntB : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  intro M _ _ κ b v y
  choose d hd0 hd using exists_int_smul_mem_adicCompletionIntegers_of_elt v
  set c := (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y with hc
  refine ⟨∏ i ∈ c.support, d (c i), Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _, fun i => ?_⟩
  rw [map_zsmul, ← hc, Finsupp.smul_apply, zsmul_eq_mul]
  by_cases hi : i ∈ c.support
  · rw [← Finset.prod_erase_mul _ _ hi, Int.cast_mul, mul_assoc]
    exact mul_mem (intCast_mem _ _) (hd _)
  · rw [Finsupp.notMem_support_iff.mp hi, mul_zero]
    exact zero_mem _

end GlobalTheory.AdicSpan
