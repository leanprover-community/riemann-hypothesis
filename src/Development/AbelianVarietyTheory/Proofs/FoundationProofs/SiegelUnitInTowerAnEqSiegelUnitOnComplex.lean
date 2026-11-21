import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionHolomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformation
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegral

section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Per

def qp (q u : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * u)

theorem multipliable_qp {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Multipliable fun m : ℕ => 1 - q ^ (m + 1) * u := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * u)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem qp_shift {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : qp q u = (1 - q * u) * qp q (q * u) := by
  have e : (fun m : ℕ => 1 - q ^ (m + 1 + 1) * u) = fun m : ℕ => 1 - q ^ (m + 1) * (q * u) := by
    funext m; ring
  have h : Multipliable fun m : ℕ => (fun m : ℕ => 1 - q ^ (m + 1) * u) (m + 1) := by
    show Multipliable fun m : ℕ => 1 - q ^ (m + 1 + 1) * u
    rw [e]; exact multipliable_qp hq _
  have := tprod_eq_zero_mul' (f := fun m : ℕ => 1 - q ^ (m + 1) * u) h
  simp only [e, zero_add, pow_one] at this
  exact this

def tp (q u : ℂ) : ℂ := (1 - u) * qp q u * qp q u⁻¹

theorem tp_shift {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) : tp q (q * u) = -u⁻¹ * tp q u := by
  have e : q * (q * u)⁻¹ = u⁻¹ := by field_simp
  unfold tp
  rw [← qp_shift hq u, qp_shift hq (q * u)⁻¹, e]
  have : 1 - u⁻¹ = -u⁻¹ * (1 - u) := by field_simp; ring
  rw [this]; ring

theorem tp_shift_pow {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) (k : ℕ) :
    tp q (q ^ k * u) = (-u⁻¹) ^ k * (q ^ (k.choose 2))⁻¹ * tp q u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : q ^ (k + 1) * u = q * (q ^ k * u) := by ring
    have e2 : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [e, tp_shift hq hq0 (mul_ne_zero (pow_ne_zero _ hq0) hu), ih, e2, pow_add q, pow_succ (-u⁻¹)]
    generalize (-u⁻¹) ^ k = A
    field_simp

theorem cth_eq {q t : ℂ} (hq : ‖q‖ < 1) (c : ℕ) (h1 : ∀ m : ℕ, 1 - q ^ (m + 1) * t ^ c ≠ 0)
    (h2 : ∀ m : ℕ, 1 - q ^ (m + 1) * (t ^ c)⁻¹ ≠ 0) :
    cth c q t = q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have pA := (multipliable_qp hq t).hasProd
  have pB := (multipliable_qp hq t⁻¹).hasProd
  obtain ⟨C, hC, pC⟩ := hasProd_geom hq _ h1
  obtain ⟨D, hD, pD⟩ := hasProd_geom hq _ h2
  have hP : HasProd (fun m : ℕ => cthFac c q t (m + 1)) (qp q t ^ (c ^ 2) * qp q t⁻¹ ^ (c ^ 2) * (C * D)⁻¹) := by
    have := ((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))
    simpa only [cthFac, div_eq_mul_inv, qp] using this
  have eC : qp q (t ^ c) = C := pC.tprod_eq
  have eD : qp q (t ^ c)⁻¹ = D := pD.tprod_eq
  unfold cth tp
  rw [hP.tprod_eq, eC, eD]
  simp only [div_eq_mul_inv, mul_inv, mul_pow]
  ring

theorem expo (c : ℕ) : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c.choose 2 : ℕ) : ℤ) := by
  have h : (c : ℤ) - (c : ℤ) ^ 2 = 2 * -((c.choose 2 : ℕ) : ℤ) := by
    induction c with
    | zero => simp
    | succ k ih =>
      have e2 : (k + 1).choose 2 = k + k.choose 2 := by
        rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
      rw [e2]; push_cast; linarith
  rw [h]; exact Int.mul_ediv_cancel_left _ (by norm_num)

theorem mono_shift {q t : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ht : t ≠ 0) (c : ℕ) :
    (-(q * t)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q (q * t) ^ (c ^ 2) / tp q ((q * t) ^ c)) =
      (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have hs : (-t⁻¹) ^ (c ^ 2) = (-(t ^ c)⁻¹) ^ c := by
    have hpar : (-1 : ℂ) ^ (c ^ 2) = (-1) ^ c := by
      rcases Nat.even_or_odd c with h | h
      · rw [h.neg_one_pow, (h.pow_of_ne_zero two_ne_zero).neg_one_pow]
      · rw [h.neg_one_pow, h.pow.neg_one_pow]
    rw [neg_pow, neg_pow (t ^ c)⁻¹, hpar, ← inv_pow, ← pow_mul, sq]
  have hn : (-(t ^ c)⁻¹) ^ c ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  have hqk : q ^ (c.choose 2) ≠ 0 := pow_ne_zero _ hq0
  have e : -(q * t) = q * -t := by ring
  rw [tp_shift hq hq0 ht, mul_pow q t c, tp_shift_pow hq hq0 (pow_ne_zero c ht), mul_pow, hs, e, mul_zpow, expo,
    zpow_neg q, zpow_natCast]
  generalize (-(t ^ c)⁻¹) ^ c = A at hn
  generalize q ^ (c.choose 2) = B at hqk
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

theorem sg_eq {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    sg c x τ = ee τ ^ ((c ^ 2 - 1) / 12) * ((-ee (pt x τ)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (tp (ee τ) (ee (pt x τ)) ^ (c ^ 2) / tp (ee τ) (ee (pt x τ) ^ c))) := by
  have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa using h.2.2
  unfold sg
  rw [cth_eq (norm_ee_lt_one τ) c (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).1)
    (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).2), mul_assoc]

theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (n : Fin 2 → ℤ) : admitted c fun i => x i + n i := by
  refine ⟨h.1, h.2.1, ?_⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact h.2.2 ⟨⟨a - c * n 0, by push_cast; rw [ha]; ring⟩, ⟨b - c * n 1, by push_cast; rw [hb]; ring⟩⟩

theorem sg_step {c : ℕ} {x y : Fin 2 → ℚ} (hx : admitted c x) (hy : admitted c y) (τ : ℍ) (h0 : y 0 = x 0 + 1) (h1 : y 1 = x 1) :
    sg c y τ = sg c x τ := by
  have e : ee (pt y τ) = ee τ * ee (pt x τ) := by
    rw [← ee_add]; congr 1; simp only [pt, h0, h1]; push_cast; ring
  rw [sg_eq hx, sg_eq hy, e, mono_shift (norm_ee_lt_one τ) (ee_ne_zero _) (ee_ne_zero _)]

theorem sg_fst {c : ℕ} {x : Fin 2 → ℚ} (hx : admitted c x) (τ : ℍ) (k : ℤ) :
    sg c (fun i => x i + (![k, 0] : Fin 2 → ℤ) i) τ = sg c x τ := by
  induction k using Int.induction_on with
  | zero =>
    congr 1; funext i; fin_cases i <;> simp
  | succ k ih =>
    rw [← ih]
    exact sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)
  | pred k ih =>
    rw [← ih]
    exact (sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)).symm

theorem sg_add_int : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x →
    sg c (fun i => x i + n i) τ = sg c x τ := by
  intro c x n τ hx
  rw [← sg_fst hx τ (n 0)]
  have e1 : ee (n 1 : ℂ) = 1 := by
    unfold ee
    rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
  unfold sg
  congr 1
  rw [← mul_one (ee (pt (fun i => x i + (![n 0, 0] : Fin 2 → ℤ) i) τ)), ← e1, ← ee_add]
  congr 1
  simp [pt]; ring

end GlobalTheory.Sieg.Per
end
end

section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_index_add_intVector : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x → sg c (fun i => x i + n i) τ = sg c x τ := by
  first | exact @GlobalTheory.Sieg.Per.sg_add_int | exact GlobalTheory.Sieg.Per.sg_add_int | (intros; apply GlobalTheory.Sieg.Per.sg_add_int <;> assumption)
end

section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral : ∀ (c M a : ℕ), 0 < M → a < M → ∃ k : ℤ, ∀ b : ℕ, admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ A : ℕ → ℂ, HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ A 0 ≠ 0 ∧ (∀ n, A n ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) ∧ (Nat.Coprime c M → ∀ n, A n ∈ Subring.closure {ee (1 / (M : ℂ))}) ∧ (b = 0 → ∀ n, ∃ z : ℤ, A n = z) := by
  first | exact @GlobalTheory.SiegQ.sg_expansion_int | exact GlobalTheory.SiegQ.sg_expansion_int | (intros; apply GlobalTheory.SiegQ.sg_expansion_int <;> assumption)
end

section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelMem

open Polynomial in

theorem mem_range_of_isIntegral {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {α : ℂ}
    (hα : IsIntegral ℚ α) : α ∈ Set.range ε := by
  have h0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hα
  have e : ((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
  have hb : α ∈ (((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε).roots := by
    rw [e, Polynomial.mem_roots (Polynomial.map_ne_zero h0), Polynomial.IsRoot,
      ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ α
  rw [Polynomial.Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

theorem isIntegral_ee {M : ℕ} (hM : 0 < M) : IsIntegral ℚ (ee (1 / (M : ℂ))) := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h : ee (1 / (M : ℂ)) ^ M = 1 := by
    rw [ee, ← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I := by field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  exact IsIntegral.of_pow hM (by rw [h]; exact isIntegral_one)

theorem isIntegral_of_mem_adjoin {M : ℕ} (hM : 0 < M) {z : ℂ}
    (hz : z ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) : IsIntegral ℚ z := by
  haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_ee hM)
  have h := Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))})
  exact IntermediateField.isIntegral_iff.1 h

theorem act_zero (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 0 = x 0 * (γ 0 0 : ℚ) + x 1 * (γ 1 0 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem act_one' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 1 = x 0 * (γ 0 1 : ℚ) + x 1 * (γ 1 1 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : admitted c x) (γ : SL(2, ℤ)) : admitted c (act x γ) := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hx.2.2 ⟨⟨m0 * γ 1 1 - m1 * γ 1 0, ?_⟩, ⟨m1 * γ 0 0 - m0 * γ 0 1, ?_⟩⟩⟩
  all_goals
    have hdet : ((γ 0 0 : ℤ) : ℚ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at this
      exact_mod_cast this
    rw [act_zero] at hm0
    rw [act_one'] at hm1
    push_cast
  · linear_combination (γ 1 1 : ℚ) * hm0 - (γ 1 0 : ℚ) * hm1 + ((c : ℚ) * x 0) * hdet
  · linear_combination (γ 0 0 : ℚ) * hm1 - (γ 0 1 : ℚ) * hm0 + ((c : ℚ) * x 1) * hdet

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem exp_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {c M : ℕ} (hM : 0 < M)
    {y : Fin 2 → ℚ} (P : Fin 2 → ℤ) (hP : ∀ i, (M : ℚ) * y i = P i) (hy : admitted c y) :
    ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c y τ) := by
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : ∀ i, ((P i % (M : ℤ)).toNat : ℚ) = ((P i % (M : ℤ) : ℤ) : ℚ) := fun i => by
    rw [← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)]
  have hlt : (P 0 % (M : ℤ)).toNat < M := by
    have := Int.emod_lt_of_pos (P 0) (by exact_mod_cast hM : (0 : ℤ) < M)
    omega
  set a0 : ℕ := (P 0 % (M : ℤ)).toNat with ha0
  set a1 : ℕ := (P 1 % (M : ℤ)).toNat with ha1
  set x' : Fin 2 → ℚ := ![(a0 : ℚ) / M, (a1 : ℚ) / M] with hx'
  have hx'i : ∀ i, x' i = ((P i % (M : ℤ) : ℤ) : ℚ) / M := fun i => by
    fin_cases i
    · simp [x', ha0, hr]
    · simp [x', ha1, hr]
  set n : Fin 2 → ℤ := fun i => P i / (M : ℤ) with hn
  have hyx : y = fun i => x' i + n i := by
    funext i
    have h1 : y i = (P i : ℚ) / M := by rw [← hP i]; field_simp
    have h2 : (P i : ℚ) = (M : ℚ) * ((P i / (M : ℤ) : ℤ) : ℚ) + ((P i % (M : ℤ) : ℤ) : ℚ) := by
      have h3 : P i = (M : ℤ) * (P i / (M : ℤ)) + P i % (M : ℤ) := by rw [Int.emod_def]; ring
      exact_mod_cast h3
    rw [h1, hx'i, h2]
    simp only [n]
    field_simp
    ring
  have hadm : admitted c x' := by
    refine ⟨hy.1, hy.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hy.2.2 ⟨⟨m0 + c * n 0, ?_⟩, ⟨m1 + c * n 1, ?_⟩⟩⟩
    · rw [hyx]; push_cast; rw [hm0]; ring
    · rw [hyx]; push_cast; rw [hm1]; ring
  have hper : ∀ τ : ℍ, sg c y τ = sg c x' τ := fun τ => by
    rw [hyx]; exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x' n τ hadm
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt
  obtain ⟨A, hQ, -, hA, -, -⟩ := hk a1 hadm
  have hε : ∀ j, ε (Function.invFun ε (A j)) = A j := fun j =>
    Function.invFun_eq (mem_range_of_isIntegral ε (isIntegral_of_mem_adjoin hM (hA j)))
  classical
  refine ⟨fun m => if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0, k,
    fun m hm => by simp [not_le.2 hm], fun τ => ?_⟩
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + k) := fun i j h => by simpa using h
  rw [← Function.Injective.hasSum_iff hinj (fun m hm => by
    have : ¬ k ≤ m := fun h => hm ⟨(m - k).toNat, by simp; omega⟩
    simp [this])]
  have h1 := (hQ τ).mul_left (ee ((k : ℂ) / M * (τ : ℂ)))
  have key : ee ((k : ℂ) / M * (τ : ℂ)) * (sg c x' τ * ee (-((k : ℂ) / M) * (τ : ℂ))) = sg c y τ := by
    rw [hper, mul_left_comm, ee, ee, ← Complex.exp_add]
    have : 2 * ↑Real.pi * Complex.I * ((k : ℂ) / ↑M * ↑τ) + 2 * ↑Real.pi * Complex.I * (-((k : ℂ) / ↑M) * ↑τ) = 0 := by
      ring
    rw [this, Complex.exp_zero, mul_one]
  rw [key] at h1
  have e : (fun m : ℤ => ε (if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / M)) ∘ (fun j : ℕ => (j : ℤ) + k) =
      fun j : ℕ => ee ((k : ℂ) / M * (τ : ℂ)) * (A j * Complex.exp (2 * Real.pi * Complex.I * j * τ / M)) := by
    funext j
    simp only [Function.comp_apply, le_add_iff_nonneg_left, Nat.cast_nonneg, if_true, add_sub_cancel_right,
      Int.toNat_natCast, hε]
    rw [mul_left_comm, ee, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact e ▸ h1

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem an_siegel_eq : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), admitted c x → T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  intro Ω _ _ _ ε T c x hx
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  set M : ℕ := (x 0).den * (x 1).den with hMdef
  have hM : 0 < M := Nat.mul_pos (x 0).den_pos (x 1).den_pos
  set Px : Fin 2 → ℤ := ![(x 0).num * (x 1).den, (x 1).num * (x 0).den] with hPx
  have hMx : ∀ i, (M : ℚ) * x i = Px i := fun i => by
    fin_cases i
    · simp only [hMdef, hPx, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 0)]; ring
    · simp only [hMdef, hPx, Matrix.cons_val_one, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 1)]; ring
  have hd : DifferentiableOn ℂ (sgC c x) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c x hx)
  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ := by
    intro γ hγ τ
    haveI : NeZero M := ⟨hM.ne'⟩
    obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have d00 : (M : ℤ) ∣ γ 0 0 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g00, sub_self])
    have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g01
    have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g10
    have d11 : (M : ℤ) ∣ γ 1 1 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g11, sub_self])
    obtain ⟨t00, h00⟩ := d00
    obtain ⟨t01, h01⟩ := d01
    obtain ⟨t10, h10⟩ := d10
    obtain ⟨t11, h11⟩ := d11
    have e : act x γ = fun i => x i + (![Px 0 * t00 + Px 1 * t10, Px 0 * t01 + Px 1 * t11] : Fin 2 → ℤ) i := by
      have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * t00 := by
        have : γ 0 0 = 1 + M * t00 := by rw [← h00]; ring
        rw [this]; push_cast; ring
      have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * t11 := by
        have : γ 1 1 = 1 + M * t11 := by rw [← h11]; ring
        rw [this]; push_cast; ring
      have q01 : ((γ 0 1 : ℤ) : ℚ) = M * t01 := by rw [h01]; push_cast; ring
      have q10 : ((γ 1 0 : ℤ) : ℚ) = M * t10 := by rw [h10]; push_cast; ring
      have r0 : act x γ 0 = x 0 + ((Px 0 * t00 + Px 1 * t10 : ℤ) : ℚ) := by
        rw [act_zero, q00, q10]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      have r1 : act x γ 1 = x 1 + ((Px 0 * t01 + Px 1 * t11 : ℤ) : ℚ) := by
        rw [act_one', q01, q11]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      funext i
      fin_cases i
      · simpa using r0
      · simpa using r1
    rw [e]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ τ hx
  refine SiegelModel.an_siegel T M hM hd (fun γ τ => GlobalTheory.T.siegel_function_transformation c x γ τ hx) hlev (fun γ => ?_)
  refine exp_int ε hM (fun i => Px 0 * γ 0 i + Px 1 * γ 1 i) (fun i => ?_) (admissible_act_SL2 hx γ)
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [← hMx 0, ← hMx 1]
  ring

end GlobalTheory.KZ.SiegelMem
end
end
