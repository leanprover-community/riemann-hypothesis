module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.PairingEv

theorem mem_of_monomial_mem_of_tail_mem {σ R : Type} [CommRing R] [Fintype σ]
    (S : Submodule R (MvPowerSeries σ R)) (N : ℕ) (h1 : ∀ γ : σ →₀ ℕ, monomial γ (1 : R) ∈ S)
    (h2 : ∀ T : MvPowerSeries σ R, (∀ α : σ →₀ ℕ, α.degree < N → coeff α T = 0) → T ∈ S)
    (H : MvPowerSeries σ R) : H ∈ S := by
  classical
  have hP : ∀ P : MvPolynomial σ R, (P : MvPowerSeries σ R) ∈ S := fun P => by
    induction P using MvPolynomial.induction_on' with
    | monomial γ a =>
      rw [MvPolynomial.coe_monomial]
      have := S.smul_mem a (h1 γ)
      rwa [← map_smul, smul_eq_mul, mul_one] at this
    | add P Q hP hQ => rw [MvPolynomial.coe_add]; exact S.add_mem hP hQ
  have := S.add_mem (hP (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H))
    (h2 (H - (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H : MvPolynomial σ R)) ?_)
  · simpa using this
  · intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro j
    exact (Finsupp.le_degree j α).trans hα.le

theorem chart_ev₂_monomial {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}
    (c : QLog.Chart G d) (n : ℕ) (α β : Fin d →₀ ℕ) :
    c.ev₂ n (monomial (α.sumElim β) 1) = c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1) := by
  simp only [monomial_one_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, (c.isEval n).1, (c.isEval₂ n).1, Sum.elim_inl,
    Sum.elim_inr, Finsupp.sumElim_inl, Finsupp.sumElim_inr]
  have e1 := map_prod (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)
    (fun j => c.x n j ^ α j) Finset.univ
  have e2 := map_prod (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)
    (fun j => c.x n j ^ β j) Finset.univ
  simp only [map_pow, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] at e1 e2
  rw [← e1, ← e2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GlobalTheory.PairingEv
