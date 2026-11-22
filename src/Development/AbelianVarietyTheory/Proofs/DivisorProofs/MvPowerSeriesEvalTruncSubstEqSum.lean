module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFinsuppProdConstFreeEqZeroOfDegreeLtStatement

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DivSub

theorem eval_trunc'_eq_sum {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] (w : σ → R)
    (n : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial.eval w (trunc' R n f) = ∑ β ∈ Finset.Iic n, coeff β f * ∏ i ∈ β.support, w i ^ β i := by
  have hsub : (trunc' R n f).support ⊆ Finset.Iic n := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, coeff_trunc'] at hm
    split_ifs at hm with h
    · exact Finset.mem_Iic.mpr h
    · exact absurd rfl hm
  rw [MvPolynomial.eval_eq, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [coeff_trunc', if_pos (Finset.mem_Iic.mp hm)]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

end GlobalTheory.DivSub
