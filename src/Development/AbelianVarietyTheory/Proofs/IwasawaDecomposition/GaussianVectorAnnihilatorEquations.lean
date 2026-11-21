import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY

section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscExpDeriv

theorem coeff_pow_eq_zero_of_degree_lt {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : MvPolynomial.coeff 0 q = 0) (n : ℕ) :
    ∀ γ : σ →₀ ℕ, γ.degree < n → MvPolynomial.coeff γ (q ^ n) = 0 := by
  induction n with
  | zero => intro γ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro γ h
    rw [pow_succ, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : x.1 + x.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h2 : x.2 = 0
    · rw [h2, hq, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h0 => h2 ((Finsupp.degree_eq_zero_iff _).1 h0)
      have hs : x.1.degree + x.2.degree = γ.degree := by rw [← hx', map_add]
      rw [ih x.1 (by omega), zero_mul]

theorem coeff_expPS_eq_sum {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : MvPolynomial.coeff 0 q = 0) (γ : σ →₀ ℕ) (N : ℕ) (hN : γ.degree < N) :
    MvPowerSeries.coeff γ (expPS q) =
      ∑ n ∈ Finset.range N, MvPolynomial.coeff γ (q ^ n) / (n.factorial : ℂ) := by
  change ∑ n ∈ Finset.range (γ.degree + 1), MvPolynomial.coeff γ (q ^ n) / (n.factorial : ℂ) = _
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => ?_
  rw [coeff_pow_eq_zero_of_degree_lt q hq n γ (by simp only [Finset.mem_range] at hn; omega),
    zero_div]

theorem coeff_deriv_expPS : ∀ (σ : Type) [DecidableEq σ] (q : MvPolynomial σ ℂ),
    MvPolynomial.coeff 0 q = 0 → ∀ (l : σ) (α : σ →₀ ℕ),
      ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS q) =
        MvPowerSeries.coeff α
          (((MvPolynomial.pderiv l q : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * expPS q) := by
  intro σ _ q hq l α
  rw [coeff_expPS_eq_sum q hq _ (α.degree + 1 + 1)
    (by rw [map_add, Finsupp.degree_single]; omega), Finset.mul_sum, MvPowerSeries.coeff_mul]
  have h1 : ∀ n : ℕ, ((α l : ℂ) + 1) *
      (MvPolynomial.coeff (α + Finsupp.single l 1) (q ^ n) / (n.factorial : ℂ)) =
      MvPolynomial.coeff α (MvPolynomial.pderiv l (q ^ n)) / (n.factorial : ℂ) := by
    intro n
    rw [MvPolynomial.coeff_pderiv]
    ring
  simp only [h1]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, MvPolynomial.coeff_zero, zero_div, add_zero]
  have h2 : ∀ n : ℕ, MvPolynomial.coeff α (MvPolynomial.pderiv l (q ^ (n + 1))) /
      (((n + 1).factorial : ℕ) : ℂ) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, MvPolynomial.coeff x.1 (MvPolynomial.pderiv l q) *
        (MvPolynomial.coeff x.2 (q ^ n) / (n.factorial : ℂ)) := by
    intro n
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, mul_comm, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_mul, Nat.factorial_succ, nsmul_eq_mul]
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    push_cast
    field_simp
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have hs : x.1.degree + x.2.degree = α.degree := by rw [← hx', map_add]
  rw [coeff_expPS_eq_sum q hq x.2 (α.degree + 1) (by omega), MvPolynomial.coeff_coe, Finset.mul_sum]

end GlobalTheory.OscExpDeriv
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

section General

variable {σ : Type} [DecidableEq σ] {F : Fock σ} {v : F.H} {E : MvPowerSeries σ ℂ}

omit [DecidableEq σ] in

theorem prod_factorial_add_single (α : σ →₀ ℕ) (l : σ) :
    (α + Finsupp.single l 1).prod (fun _ k => (k.factorial : ℂ)) =
      ((α l : ℂ) + 1) * α.prod (fun _ k => (k.factorial : ℂ)) := by
  rw [← FockSeq.mfact_cast, ← FockSeq.mfact_cast, Oscillator.mfact_add_single]
  push_cast
  ring

theorem inner_X_mul_monomial (h : HasCoeff F v E) (l : σ) (α : σ →₀ ℕ) :
    inner ℂ (F.ι (MvPolynomial.X l * MvPolynomial.monomial α 1)) v =
      α.prod (fun _ k => (k.factorial : ℂ)) *
        (((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E) := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm, h, prod_factorial_add_single]
  ring

theorem inner_pderiv_monomial (h : HasCoeff F v E) (m : σ) (α : σ →₀ ℕ) :
    inner ℂ (F.ι (MvPolynomial.pderiv m (MvPolynomial.monomial α 1))) v =
      α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (MvPowerSeries.X m * E) := by
  have e : ∀ (γ : σ →₀ ℕ) (c : ℂ), (MvPolynomial.monomial γ c : MvPolynomial σ ℂ) =
      c • MvPolynomial.monomial γ 1 := fun γ c => by simp [MvPolynomial.smul_monomial]
  rw [MvPolynomial.pderiv_monomial, e, map_smul, inner_smul_left, h, MvPowerSeries.X_def,
    MvPowerSeries.coeff_monomial_mul]
  by_cases h0 : α m = 0
  · have : ¬ Finsupp.single m 1 ≤ α := by rw [Finsupp.single_le_iff, h0]; omega
    simp [h0, this]
  · have hle : Finsupp.single m 1 ≤ α := Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero h0)
    obtain ⟨β, rfl⟩ := exists_add_of_le hle
    rw [if_pos hle, add_tsub_cancel_left, add_comm, prod_factorial_add_single]
    simp
    ring

theorem inner_X_mul_of_deriv {κ : Type} [Fintype κ] (h : HasCoeff F v E) (l : σ) (c : ℂ) (a : κ → ℂ) (m : κ → σ)
    (hE : ∀ α : σ →₀ ℕ, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E =
      MvPowerSeries.coeff α (((MvPolynomial.C c + ∑ k, MvPolynomial.C (a k) * MvPolynomial.X (m k) :
        MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * E)) (f : MvPolynomial σ ℂ) :
    inner ℂ (F.ι (MvPolynomial.X l * f)) v =
      c * inner ℂ (F.ι f) v + ∑ k, a k * inner ℂ (F.ι (MvPolynomial.pderiv (m k) f)) v := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [mul_add, map_add, inner_add_left, hf, hg, Finset.sum_add_distrib]
    ring
  | monomial α b =>
    have e : (MvPolynomial.monomial α b : MvPolynomial σ ℂ) = b • MvPolynomial.monomial α 1 := by
      simp [MvPolynomial.smul_monomial]
    have e2 : ((MvPolynomial.C c + ∑ k, MvPolynomial.C (a k) * MvPolynomial.X (m k) :
        MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
        MvPowerSeries.C c + ∑ k, MvPowerSeries.C (a k) * MvPowerSeries.X (m k) := by
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_sum]
      simp
    rw [e, mul_smul_comm]
    simp only [Derivation.map_smul, map_smul, inner_smul_left]
    simp only [inner_X_mul_monomial h, inner_pderiv_monomial h, h α, hE, e2, add_mul, Finset.sum_mul, map_add,
      map_sum, mul_assoc, MvPowerSeries.coeff_C_mul, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring

end General

variable {P Q : ℕ}

theorem pderiv_inl_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (i : Fin P) :
    MvPolynomial.pderiv (Sum.inl i) (gaussPoly A x) =
      MvPolynomial.C (x (Sum.inl i)) + ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inr j) := by
  simp only [gaussPoly, map_add, map_sum, mul_assoc, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  rw [add_comm, Finset.sum_comm]
  simp

theorem pderiv_inr_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (j : Fin Q) :
    MvPolynomial.pderiv (Sum.inr j) (gaussPoly A x) =
      MvPolynomial.C (x (Sum.inr j)) + ∑ i, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inl i) := by
  simp only [gaussPoly, map_add, map_sum, mul_assoc, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  rw [add_comm]
  simp

theorem gauss_annihilator (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H)
    (h : HasCoeff F v (expPS (gaussPoly A x))) :
    (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v =
      x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) ∧
    (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v =
      x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) := by
  refine ⟨fun i f => ?_, fun j f => ?_⟩
  · refine inner_X_mul_of_deriv h _ _ (fun j => A i j) (fun j => Sum.inr j) (fun α => ?_) f
    rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x), pderiv_inl_gaussPoly]
  · refine inner_X_mul_of_deriv h _ _ (fun i => A i j) (fun i => Sum.inl i) (fun α => ?_) f
    rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x), pderiv_inr_gaussPoly]

end GlobalTheory.OscGauss

end
end
