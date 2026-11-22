module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRootsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel

@[expose] public section

open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevClosed

open Polynomial

theorem mem_adjoin_inv_of_isIntegral {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  obtain ⟨f, hm, hf⟩ := hi
  letI : Invertible z := invertibleOfNonzero hz
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) z f
  rw [hf, invOf_eq_inv] at h1
  have h2 : eval₂ (algebraMap R K) z⁻¹ f.reverse = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ hz)
  have h3 := divX_mul_X_add f.reverse
  rw [coeff_zero_reverse, hm.leadingCoeff] at h3
  have h4 := congrArg (eval₂ (algebraMap R K) z⁻¹) h3
  rw [h2, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, map_one] at h4
  have hzz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have h5 : z = -(aeval z⁻¹ (divX f.reverse)) := by
    rw [aeval_def]
    linear_combination z * h4 - eval₂ (algebraMap R K) z⁻¹ (divX f.reverse) * hzz
  have hm' : -(aeval z⁻¹ (divX f.reverse)) ∈ Algebra.adjoin R {z⁻¹} :=
    neg_mem (aeval_mem_adjoin_singleton R _)
  rwa [← h5] at hm'

end GlobalTheory.K5.LevClosed
