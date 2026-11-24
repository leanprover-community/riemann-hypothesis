module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_nat_common_denom {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (c : ι → K) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∃ a : 𝓞 K, (a : K) = (k : K) * c i := by
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨(m * m).natAbs, Int.natAbs_pos.2 (mul_ne_zero hm0 hm0), fun i => ?_⟩
  have h := hm (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨(m : 𝓞 K) * ⟨m • c i, h⟩, ?_⟩
  have h2 : (((m * m).natAbs : ℕ) : K) = (m : K) * m := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]; push_cast; rfl
  rw [h2]
  change ((m : 𝓞 K) : K) * (m • c i) = _
  simp [mul_assoc]

theorem smul_mem_YYl (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : 𝓞 D.host.K)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L L') : (a : D.host.K) • y ∈ YYl D L L' := by
  have h := (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a) hy
  exact h

theorem exists_comm_YYl (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hb : OnB D b) (hL : SD D L) (hL' : SD D L') :
    ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  have hc : ∀ i, ∃ c : Fin r → D.host.K, ∑ j, c j • b j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hb.2]; trivial)
  choose c hc using hc
  obtain ⟨k, hk, hden⟩ := exists_nat_common_denom (K := D.host.K) (ι := (Fin s × Fin r) ⊕ (Fin s × Fin r))
    (Sum.elim (fun p => c p.1 p.2) (fun p => hYY D (b p.2) (y' p.1)))
  choose a ha using hden
  refine ⟨k, hk, fun x hx => ?_, fun j => ?_⟩
  · have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine ⟨fun j => ∑ i, t i * a (Sum.inl (i, j)), ?_⟩
    conv_lhs => rw [hexp x]
    rw [← Nat.cast_smul_eq_nsmul D.host.K]
    simp only [← hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1

    rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ha, ht]
    simp only [Sum.elim_inl]
    ring
  · apply AddSubgroup.subset_closure
    rw [hexp (b j), ← Nat.cast_smul_eq_nsmul D.host.K, Finset.smul_sum]
    refine (YYl D L L').sum_mem fun i _ => ?_
    rw [smul_smul]
    have := ha (Sum.inr (i, j))
    simp only [Sum.elim_inr] at this
    rw [← this]
    exact smul_mem_YYl D L L' _ (hy i)

end GlobalTheory.ThetaConj
