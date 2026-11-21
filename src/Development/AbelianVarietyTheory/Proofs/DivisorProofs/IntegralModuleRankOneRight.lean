import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuantumDetCentralCoeffsConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMemStatement

section
section
open Matrix GlobalTheory.TorFin

namespace GlobalTheory

open Module

theorem frame_first_column_first_row :
    ∀ (m : ℕ) (v φ : Fin (m + 1) → ℂ), φ ⬝ᵥ v = 1 → ∃ P P' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
      P * P' = 1 ∧ (∀ i, P i 0 = v i) ∧ ∀ j, P' 0 j = φ j := by
  intro m v φ h
  let L : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => φ ⬝ᵥ x
      map_add' := fun x y => dotProduct_add φ x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hL : ∀ x, L x = φ ⬝ᵥ x := fun x => rfl
  have hsurj : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • v, by rw [hL, dotProduct_smul, h]; simp⟩
  have hdim : Module.finrank ℂ (LinearMap.ker L) = m := by
    have := LinearMap.finrank_range_add_finrank_ker L
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
    omega
  let bN := Module.finBasisOfFinrankEq ℂ (LinearMap.ker L) hdim
  have hli : ∀ (c : ℂ), ∀ x ∈ LinearMap.ker L, c • v + x = 0 → c = 0 := by
    intro c x hx hc
    have := congrArg L hc
    rw [map_add, map_smul, LinearMap.mem_ker.mp hx, hL v, h, map_zero] at this
    simpa using this
  have hsp : ∀ z : Fin (m + 1) → ℂ, ∃ c : ℂ, z + c • v ∈ LinearMap.ker L := by
    intro z
    refine ⟨-(L z), ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, hL v, h]
    simp
  let b := Module.Basis.mkFinCons v bN hli hsp
  have hb : ⇑b = Fin.cons v (Subtype.val ∘ bN) := Module.Basis.coe_mkFinCons v bN hli hsp
  let e := Pi.basisFun ℂ (Fin (m + 1))
  have hcoord : b.coord 0 = L := by
    refine b.ext fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Basis.coord_apply, Basis.repr_self, hb]
      simp [hL, h]
    · rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
      have hmem : b k.succ ∈ LinearMap.ker L := by
        rw [hb]; simp
      rw [LinearMap.mem_ker.mp hmem]
      simp [Fin.succ_ne_zero]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip e b, ?_, ?_⟩
  · intro i
    rw [Basis.toMatrix_apply, hb]
    simp [e]
  · intro j
    rw [Basis.toMatrix_apply]
    have := congrArg (fun f : (Fin (m + 1) → ℂ) →ₗ[ℂ] ℂ => f (e j)) hcoord
    simp only [Basis.coord_apply] at this
    rw [this, hL]
    simp [e, dotProduct_single]

end GlobalTheory
end

open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_completion_first_column : ∀ (m : ℕ) (v φ : Fin (m + 1) → ℂ), φ ⬝ᵥ v = 1 → ∃ P P' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, P * P' = 1 ∧ (∀ i, P i 0 = v i) ∧ ∀ j, P' 0 j = φ j := by
  atlas_forward_decl GlobalTheory.frame_first_column_first_row
end

section
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_central_coeffs_conj : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ P P' : Matrix (Fin n) (Fin n) ℂ, P * P' = 1 → ∃ c : ℕ → A, c n = 1 ∧ (∀ k ≤ n, c k ∈ invAlg ρ) ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun a b => ρ (P * Matrix.single a b 1 * P')) u = ∑ k ∈ Finset.range (n + 1), u ^ k • c k := by
  first | exact @GlobalTheory.qdet_frame_coeff_mem_invAlg | exact GlobalTheory.qdet_frame_coeff_mem_invAlg | (intros; apply GlobalTheory.qdet_frame_coeff_mem_invAlg <;> assumption)
end

section
section
open Matrix GlobalTheory.TorFin

theorem GlobalTheory.isIntMod_of_monic_dvd_affine : ∀ (A : Type) [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H : A),
    (∀ i ∈ I, H * i ∈ I) → ∀ (N : ℕ) (c q : ℕ → A), c N = 1 → (∀ k ≤ N, c k ∈ Z) →
    (∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • c k - (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k ∈ I) →
    IsIntMod Z I H := by
  intro A _ _ Z I H hH N c q hcN hcZ hI
  classical
  let q' : ℕ → A := fun k => if k < N then q k else 0
  let e : ℕ → A := fun k => (if k = 0 then 0 else q' (k - 1)) + H * q' k
  have hE : ∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • e k =
      (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k := by
    intro u
    have h1 : ∑ k ∈ Finset.range (N + 1), u ^ k • (if k = 0 then 0 else q' (k - 1)) =
        ∑ k ∈ Finset.range N, u ^ (k + 1) • q k := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, smul_zero, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      exact Finset.sum_congr rfl fun k hk => by simp [q', Finset.mem_range.1 hk]
    have h2 : ∑ k ∈ Finset.range (N + 1), u ^ k • (H * q' k) = ∑ k ∈ Finset.range N, u ^ k • (H * q k) := by
      rw [Finset.sum_range_succ]
      simp only [q', lt_irrefl, if_false, mul_zero, smul_zero, add_zero]
      exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
    simp only [e, smul_add, Finset.sum_add_distrib]
    rw [h1, h2, add_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by rw [smul_mul_assoc, one_mul, smul_smul, pow_succ']
    · exact Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _).symm
  have hT : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * e k = 0 := by
    have h1 : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (if k = 0 then 0 else q' (k - 1)) =
        ∑ k ∈ Finset.range N, (-H) ^ (k + 1) * q k := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, mul_zero, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      exact Finset.sum_congr rfl fun k hk => by simp [q', Finset.mem_range.1 hk]
    have h2 : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (H * q' k) = ∑ k ∈ Finset.range N, (-H) ^ k * (H * q k) := by
      rw [Finset.sum_range_succ]
      simp only [q', lt_irrefl, if_false, mul_zero, add_zero]
      exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
    simp only [e, mul_add, Finset.sum_add_distrib]
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pow_succ, mul_assoc, ← mul_add, neg_mul, neg_add_cancel, mul_zero]
  have hd : ∀ k < N + 1, c k - e k ∈ I := GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem A I (N + 1) (fun k => c k - e k) fun u => by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hE]
    exact hI u
  have hpow : ∀ k, ∀ i ∈ I, (-H) ^ k * i ∈ I := by
    intro k
    induction k with
    | zero => intro i hi; simpa using hi
    | succ k ih => intro i hi; rw [pow_succ', mul_assoc, neg_mul]; exact I.neg_mem (hH _ (ih i hi))
  have hcI : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k ∈ I := by
    have : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k = ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (c k - e k) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hT, sub_zero]
    rw [this]
    exact I.sum_mem fun k hk => hpow k _ (hd k (Finset.mem_range.1 hk))
  refine ⟨N, ?_⟩
  set S := Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z} with hS
  have hterm : ∀ k < N, (-H) ^ k * c k ∈ S := by
    intro k hk
    have hm : H ^ k * c k ∈ S := Submodule.subset_span ⟨k, hk, c k, hcZ k hk.le, rfl⟩
    rw [neg_pow]
    rcases neg_one_pow_eq_or A k with h | h <;> rw [h]
    · simpa using hm
    · rw [neg_one_mul, neg_mul]; exact S.neg_mem hm
  have hN : (-H) ^ N ∈ I ⊔ S := by
    have : (-H) ^ N = ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k - ∑ k ∈ Finset.range N, (-H) ^ k * c k := by
      rw [Finset.sum_range_succ, hcN, mul_one, add_sub_cancel_left]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hcI)
      (Submodule.mem_sup_right (S.sum_mem fun k hk => hterm k (Finset.mem_range.1 hk)))
  rw [neg_pow] at hN
  rcases neg_one_pow_eq_or A N with h | h <;> rw [h] at hN
  · simpa using hN
  · rw [neg_one_mul] at hN; simpa using (I ⊔ S).neg_mem hN
end

open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_module_of_char_poly : ∀ (A : Type) [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H : A), (∀ i ∈ I, H * i ∈ I) → ∀ (N : ℕ) (c q : ℕ → A), c N = 1 → (∀ k ≤ N, c k ∈ Z) → (∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • c k - (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k ∈ I) → IsIntMod Z I H := by
  atlas_forward_decl GlobalTheory.isIntMod_of_monic_dvd_affine
end

section
section
open Matrix GlobalTheory.TorFin

namespace GlobalTheory

theorem capelli_tm_sub_eq {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (w x : ℂ)
    (a b : Fin n) :
    Formalism.REAL.Tm E (w - x) a b = w • (if a = b then (1 : A) else 0) + Formalism.REAL.Tm E (-x) a b := by
  unfold Formalism.REAL.Tm
  split_ifs <;> simp [Algebra.smul_def, sub_eq_add_neg, map_add, add_assoc]

theorem mul_single_mul_eq_vecMulVec {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P * Matrix.single a b 1 * P' = vecMulVec (fun i => P i a) (fun j => P' b j) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, vecMulVec_apply, Finset.sum_ite_eq, ite_and]

theorem rho_vecMulVec_isIntMod_invAlg : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 →
    IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ}) (ρ (vecMulVec v φ)) := by
  intro n A _ _ ρ hρ v φ hφv
  cases n with
  | zero => simp [dotProduct] at hφv
  | succ m =>
  obtain ⟨P, P', hPP', hPv, hP'φ⟩ := GlobalTheory.T.matrix_completion_first_column m v φ hφv
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  obtain ⟨c, hcN, hcZ, hc⟩ := GlobalTheory.T.quantum_det_central_coeffs_conj (m+1) A ρ hρ P P' hPP'
  have hadj : ∀ X, ρ X ∈ Algebra.adjoin ℂ (Set.range ρ) := fun X => Algebra.subset_adjoin ⟨X, rfl⟩
  have hTm : ∀ w a b, Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P')) w a b
      ∈ Algebra.adjoin ℂ (Set.range ρ) := by
    intro w a b
    refine add_mem ?_ (hadj _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact zero_mem _
  have hE0 : ∀ a, ρ (P * Matrix.single a 0 1 * P') = ρ (vecMulVec (fun i => P i a) φ) := by
    intro a
    rw [mul_single_mul_eq_vecMulVec]
    congr 2
    funext j
    exact hP'φ j
  have hEH : ρ (P * Matrix.single 0 0 1 * P') = ρ (vecMulVec v φ) := by
    rw [hE0]
    congr 2
    funext i
    exact hPv i
  have hcol : ∀ a : Fin (m+1), a ≠ 0 → φ ⬝ᵥ (fun i => P i a) = 0 := by
    intro a ha
    have := congrFun (congrFun hP'P 0) a
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Ne.symm ha)] at this
    simpa [dotProduct, hP'φ] using this
  have hHI : ∀ x ∈ leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ},
      ρ (vecMulVec v φ) * x ∈ leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, ⟨u, hu, rfl⟩, w, hw, rfl⟩ := hx
      have h1 : ρ (vecMulVec v φ) * ρ (vecMulVec u φ)
          = ρ (vecMulVec u φ) * ρ (vecMulVec v φ) - ρ (vecMulVec u φ) := by
        have := hρ (vecMulVec v φ) (vecMulVec u φ)
        rw [vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, hu, hφv, zero_smul, one_smul] at this
        have h0 : vecMulVec v (0 : Fin (m+1) → ℂ) = 0 := by ext i j; simp [vecMulVec_apply]
        rw [h0, zero_sub, map_neg] at this
        rw [eq_sub_iff_add_eq, ← sub_neg_eq_add, this]
        abel
      rw [← mul_assoc, h1, sub_mul, mul_assoc]
      exact sub_mem (Submodule.subset_span ⟨_, ⟨u, hu, rfl⟩, _, mul_mem (hadj _) hw, rfl⟩)
        (Submodule.subset_span ⟨_, ⟨u, hu, rfl⟩, w, hw, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  have hR : ∀ σ : Equiv.Perm (Fin (m+1)), ∃ d : ℕ → A, ∀ u : ℂ,
      (List.ofFn fun k : Fin m => Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P'))
        (u - ((k.succ : Fin (m+1)) : ℂ)) (σ k.succ) k.succ).prod
        = ∑ i ∈ Finset.range (m+1), u ^ i • d i := by
    intro σ
    obtain ⟨d, -, hd⟩ := GlobalTheory.prod_affine_polyMap_top m
      (fun k => if σ k.succ = k.succ then (1 : A) else 0)
      (fun k => Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P'))
        (-((k.succ : Fin (m+1)) : ℂ)) (σ k.succ) k.succ)
    exact ⟨d, fun u => by rw [← hd u]; congr 2; funext k; exact capelli_tm_sub_eq _ u _ _ _⟩
  choose d hd using hR
  refine GlobalTheory.T.integral_module_of_char_poly A (invAlg ρ) _ _ hHI (m+1) c
    (fun i => ∑ σ : Equiv.Perm (Fin (m+1)),
      if σ 0 = 0 then ((Equiv.Perm.sign σ : ℤ) : A) * d σ i else 0) hcN hcZ ?_
  intro u
  rw [← hc u]
  have hQ : ∑ k ∈ Finset.range (m+1), u ^ k • (∑ σ : Equiv.Perm (Fin (m+1)),
      if σ 0 = 0 then ((Equiv.Perm.sign σ : ℤ) : A) * d σ k else 0)
      = ∑ σ : Equiv.Perm (Fin (m+1)), if σ 0 = 0 then ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun k : Fin m => Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P'))
        (u - ((k.succ : Fin (m+1)) : ℂ)) (σ k.succ) k.succ).prod else 0 := by
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs
    · rw [hd σ u, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm]
    · simp
  rw [hQ]
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [List.ofFn_succ, List.prod_cons]
  simp only [id]
  by_cases h0 : σ 0 = 0
  · rw [if_pos h0]
    have hT : Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P')) (u - ((0 : Fin (m+1)) : ℂ)) (σ 0) 0
        = u • (1 : A) + ρ (vecMulVec v φ) := by
      unfold Formalism.REAL.Tm
      beta_reduce
      rw [if_pos h0, h0, hEH]
      simp [Algebra.smul_def]
    rw [hT, ← mul_assoc, ← mul_assoc, ← (Int.cast_commute _ _).eq, sub_self]
    exact zero_mem _
  · rw [if_neg h0, mul_zero, sub_zero]
    have hT : Formalism.REAL.Tm (fun a b => ρ (P * Matrix.single a b 1 * P')) (u - ((0 : Fin (m+1)) : ℂ)) (σ 0) 0
        = ρ (vecMulVec (fun i => P i (σ 0)) φ) := by
      unfold Formalism.REAL.Tm
      beta_reduce
      rw [if_neg h0, zero_add, hE0]
    rw [hT, ← zsmul_eq_mul]
    refine zsmul_mem ?_ _
    refine Submodule.subset_span ?_
    refine ⟨_, ⟨_, hcol _ h0, rfl⟩, _, Subalgebra.list_prod_mem _ ?_, rfl⟩
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact hTm _ _ _

end GlobalTheory
end

open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_module_rank_one_left : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 → IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ u, φ ⬝ᵥ u = 0 ∧ Y = vecMulVec u φ}) (ρ (vecMulVec v φ)) := by
  atlas_forward_decl GlobalTheory.rho_vecMulVec_isIntMod_invAlg
end

section
section
open Matrix GlobalTheory.TorFin

namespace GlobalTheory.TorFin

theorem isIntMod_of_neg_of_le {A : Type} [Ring A] [Algebra ℂ A] {Z Z' : Subalgebra ℂ A} {I I' : Submodule ℂ A} {H : A}
    (hZ : Z' ≤ Z) (hI : I' ≤ I) (h : IsIntMod Z' I' (-H)) : IsIntMod Z I H := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  have hs : Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z', a = (-H) ^ k * z} ≤
      Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z} := by
    rw [Submodule.span_le]
    rintro a ⟨k, hk, z, hz, rfl⟩
    have hm : H ^ k * z ∈ Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z} :=
      Submodule.subset_span ⟨k, hk, z, hZ hz, rfl⟩
    rcases neg_one_pow_eq_or A k with e | e
    · rw [SetLike.mem_coe, neg_pow, e, one_mul]; exact hm
    · rw [SetLike.mem_coe, neg_pow, e, neg_one_mul, neg_mul]; exact Submodule.neg_mem _ hm
  have hN' := (sup_le_sup hI hs) hN
  rcases neg_one_pow_eq_or A N with e | e
  · rwa [neg_pow, e, one_mul] at hN'
  · rw [neg_pow, e, neg_one_mul] at hN'; simpa using Submodule.neg_mem _ hN'

theorem intMod_vecMulVec_row : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A),
    IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 →
      IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ ψ, ψ ⬝ᵥ v = 0 ∧ Y = vecMulVec v ψ}) (ρ (vecMulVec v φ)) := by
  intro n A _ _ ρ hρ v φ hφ
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A, ∀ Y, ρ' Y = -ρ Yᵀ :=
    ⟨-(ρ ∘ₗ (transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap), fun Y => rfl⟩
  have hL : IsLieRep ρ' := by
    intro X Y
    rw [hρ', hρ', hρ', transpose_sub, transpose_mul, transpose_mul, ← map_neg, neg_sub, hρ Xᵀ Yᵀ]
    simp only [neg_mul_neg]
  have h1 := GlobalTheory.T.integral_module_rank_one_left n A ρ' hL φ v (by rw [dotProduct_comm]; exact hφ)
  have e1 : ρ' (vecMulVec φ v) = -ρ (vecMulVec v φ) := by rw [hρ', transpose_vecMulVec]
  rw [e1] at h1
  have hadj : Algebra.adjoin ℂ (Set.range ρ') = Algebra.adjoin ℂ (Set.range ρ) := by
    congr 1; ext a; constructor
    · rintro ⟨Y, rfl⟩; exact ⟨-Yᵀ, by rw [hρ', map_neg]⟩
    · rintro ⟨Y, rfl⟩; exact ⟨-Yᵀ, by rw [hρ', transpose_neg, transpose_transpose, map_neg, neg_neg]⟩
  have hZ : invAlg ρ' ≤ invAlg ρ := by
    intro T hT
    rw [mem_invAlg] at hT ⊢
    refine ⟨hadj ▸ hT.1, fun r g g' hg hr => hT.2 r g'ᵀ gᵀ ?_ ?_⟩
    · rw [← transpose_mul, hg, transpose_one]
    · intro Y
      rw [hρ', hρ', mul_neg, neg_mul, hr,
        show (g'ᵀ * Y * gᵀ)ᵀ = g * Yᵀ * g' by simp [transpose_mul, Matrix.mul_assoc]]
  have hI : leftIdl ρ' {Y | ∃ u, v ⬝ᵥ u = 0 ∧ Y = vecMulVec u v} ≤
      leftIdl ρ {Y | ∃ ψ, ψ ⬝ᵥ v = 0 ∧ Y = vecMulVec v ψ} := by
    unfold leftIdl
    rw [Submodule.span_le]
    rintro a ⟨Y, ⟨u, hu, rfl⟩, w, hw, rfl⟩
    rw [SetLike.mem_coe, hρ', transpose_vecMulVec, neg_mul]
    exact Submodule.neg_mem _ (Submodule.subset_span
      ⟨vecMulVec v u, ⟨u, by rw [dotProduct_comm]; exact hu, rfl⟩, w, hadj ▸ hw, rfl⟩)
  exact isIntMod_of_neg_of_le hZ hI h1

end GlobalTheory.TorFin
end

open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_module_rank_one_right : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ v φ : Fin n → ℂ, φ ⬝ᵥ v = 1 → IsIntMod (invAlg ρ) (leftIdl ρ {Y | ∃ ψ, ψ ⬝ᵥ v = 0 ∧ Y = vecMulVec v ψ}) (ρ (vecMulVec v φ)) := by
  atlas_forward_decl GlobalTheory.TorFin.intMod_vecMulVec_row
end
