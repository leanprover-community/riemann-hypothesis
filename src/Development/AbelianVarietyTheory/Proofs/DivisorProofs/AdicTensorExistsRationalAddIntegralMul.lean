module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem exists_rat_sub_le (v : HeightOneSpectrum ℤ) (c d : v.adicCompletion ℚ) (hd : d ≠ 0) :
    ∃ q : ℚ, Valued.v (c - algebraMap ℚ (v.adicCompletion ℚ) q) ≤ Valued.v d := by
  have hset : {y : v.adicCompletion ℚ | Valued.v y ≤ Valued.v d} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict d} := by
    ext y; simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff]
  have hball : IsOpen {y : v.adicCompletion ℚ | Valued.v y ≤ Valued.v d} := by
    rw [hset]; exact Valued.isOpen_closedBall _ (by simpa using hd)
  have ho : IsOpen {y : v.adicCompletion ℚ | Valued.v (c - y) ≤ Valued.v d} :=
    hball.preimage (continuous_const.sub continuous_id)
  obtain ⟨q, hq⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := ℤ) (K := ℚ) v).exists_mem_open ho
    ⟨c, by simp⟩
  exact ⟨q, hq⟩

theorem exists_tmul_add_mul_isIntB : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L)
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ ⊗[ℚ] L) (D : ℤ), D ≠ 0 →
    ∃ (y : L) (ρ : v.adicCompletion ℚ ⊗[ℚ] L), IsIntB v ℓ ρ ∧
      x = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y + (D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ := by
  intro L _ _ κ ℓ v x D hD
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  have hD' : (D : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) D]
    exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hD)
  choose q hq using fun i =>
    exists_rat_sub_le v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr x i) (D : v.adicCompletion ℚ) hD'
  refine ⟨∑ i, q i • ℓ i, ∑ i, (((Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr x i -
    algebraMap ℚ (v.adicCompletion ℚ) (q i)) / D) ⊗ₜ[ℚ] ℓ i, ?_, ?_⟩
  · intro k

    rw [map_sum, Finsupp.finsetSum_apply]
    simp only [repr_tmul_apply ℓ v, ℓ.repr_self, Finsupp.single_apply, apply_ite (algebraMap ℚ (v.adicCompletion ℚ)),
      map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (D : v.adicCompletion ℚ) := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hD'
    exact (div_le_one₀ h0).2 (hq k)
  · conv_lhs => rw [eq_sum_tmul ℓ v x]
    rw [TensorProduct.tmul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcast : (D : v.adicCompletion ℚ ⊗[ℚ] L) = (D : v.adicCompletion ℚ) ⊗ₜ[ℚ] (1 : L) := by
      have h := map_intCast (Algebra.TensorProduct.includeLeft : v.adicCompletion ℚ →ₐ[ℚ] v.adicCompletion ℚ ⊗[ℚ] L) D
      rw [Algebra.TensorProduct.includeLeft_apply] at h
      exact h.symm
    rw [hcast, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, Algebra.smul_def, mul_one, mul_div_cancel₀ _ hD', add_sub_cancel]

end GlobalTheory.AdicSpan
