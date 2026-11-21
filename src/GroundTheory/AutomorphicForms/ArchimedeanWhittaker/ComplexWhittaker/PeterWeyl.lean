import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.InstMeasurableSpaceU2
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqZeroOfForallIntegralCoeff

namespace GroundTheory.Automorphic.ArchWhittakerC

namespace PW

open Matrix MeasureTheory Complex Finset Polynomial

noncomputable def ent (a b : Fin 2) (k : U2) : ℂ := (k : Matrix (Fin 2) (Fin 2) ℂ) a b

noncomputable def detU (k : U2) : ℂ := (k : Matrix (Fin 2) (Fin 2) ℂ).det

theorem continuous_ent (a b : Fin 2) : Continuous (ent a b) :=
  (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)

theorem continuous_detU : Continuous detU :=
  Continuous.matrix_det continuous_subtype_val

theorem detU_ne_zero (k : U2) : detU k ≠ 0 := det_ne_zero_of_U2 k

theorem detU_eq (k : U2) : detU k = ent 0 0 k * ent 1 1 k - ent 0 1 k * ent 1 0 k :=
  Matrix.det_fin_two _

theorem continuous_detU_zpow (q : ℤ) : Continuous fun k => detU k ^ q :=
  continuous_detU.zpow₀ q fun k => Or.inl (detU_ne_zero k)

noncomputable def mono (α β γ δ : ℕ) (k : U2) : ℂ :=
  ent 0 0 k ^ α * ent 0 1 k ^ β * ent 1 0 k ^ γ * ent 1 1 k ^ δ

theorem continuous_mono (α β γ δ : ℕ) : Continuous (mono α β γ δ) :=
  ((((continuous_ent 0 0).pow α).mul ((continuous_ent 0 1).pow β)).mul
    ((continuous_ent 1 0).pow γ)).mul ((continuous_ent 1 1).pow δ)

theorem integrable_of_continuous {f : U2 → ℂ} (hf : Continuous f) : Integrable f μK :=
  (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩).integrable μK

theorem integrable_of_continuous' {f : U2 → ℝ} (hf : Continuous f) : Integrable f μK :=
  (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩).integrable μK

variable (g : U2 → ℂ)

noncomputable def abelian₂ (q : ℤ) (f : U2 → ℂ) : ℂ := ∫ k, f k * detU k ^ q * g k ∂μK

variable {g}

theorem integrable_Lam (hg : Continuous g) (q : ℤ) {f : U2 → ℂ} (hf : Continuous f) :
    Integrable (fun k => f k * detU k ^ q * g k) μK :=
  integrable_of_continuous ((hf.mul (continuous_detU_zpow q)).mul hg)

theorem Lam_sub (hg : Continuous g) (q : ℤ) {f f' : U2 → ℂ} (hf : Continuous f)
    (hf' : Continuous f') : abelian₂ g q (fun k => f k - f' k) = abelian₂ g q f - abelian₂ g q f' := by
  unfold abelian₂
  rw [← integral_sub (integrable_Lam hg q hf) (integrable_Lam hg q hf')]
  congr 1; funext k; ring




theorem mono_shift (α β γ δ : ℕ) (k : U2) :
    mono (α + 1) β γ (δ + 1) k - mono α (β + 1) (γ + 1) δ k = mono α β γ δ k * detU k := by
  simp only [mono, detU_eq]; ring



noncomputable def coef (N m d : ℕ) (k : U2) : ℂ :=
  ∑ ij ∈ antidiagonal d, ((m.choose ij.1 * (N - m).choose ij.2 : ℕ) : ℂ) *
    mono (N - m - ij.2) ij.2 (m - ij.1) ij.1 k



theorem coeff_eq_zero_of_forall {N : ℕ} {a : ℕ → ℂ}
    (h : ∀ s : ℂ, ∑ i ∈ range (N + 1), s ^ i * a i = 0) : ∀ i ≤ N, a i = 0 := by
  intro i hi
  set p : ℂ[X] := ∑ j ∈ range (N + 1), C (a j) * X ^ j with hp
  have hp0 : p = 0 := by
    apply Polynomial.funext
    intro s
    rw [hp, eval_finset_sum, eval_zero, ← h s]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]
  have h1 := congrArg (fun p : ℂ[X] => p.coeff i) hp0
  simp only [hp, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at h1
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg (Ne.symm hj))
    (fun hi' => absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) hi'), if_pos rfl] at h1
  exact h1

theorem coeff_linear_pow (a b : ℂ) (m i : ℕ) :
    ((C a * X + C b) ^ m).coeff i = (m.choose i : ℂ) * a ^ i * b ^ (m - i) := by
  rw [add_pow]
  have e : ∀ j ∈ range (m + 1), (C a * X) ^ j * C b ^ (m - j) * (m.choose j : ℂ[X]) =
      C (a ^ j * b ^ (m - j) * (m.choose j : ℂ)) * X ^ j := by
    intro j _
    simp only [mul_pow, ← C_pow, map_mul, map_natCast]; ring
  rw [Finset.sum_congr rfl e, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases him : i ≤ m
  · rw [Finset.sum_eq_single i (fun j _ hj => if_neg (Ne.symm hj))
      (fun hi' => absurd (Finset.mem_range.2 (Nat.lt_succ_of_le him)) hi'), if_pos rfl]
    ring
  · rw [Finset.sum_eq_zero (fun j hj => if_neg (by
      have := Finset.mem_range.1 hj; omega)), Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem natDegree_linear_pow_le (a b : ℂ) (m : ℕ) : ((C a * X + C b) ^ m).natDegree ≤ m := by
  refine (natDegree_pow_le).trans ?_
  have : (C a * X + C b).natDegree ≤ 1 := natDegree_linear_le
  nlinarith

theorem coef_expand (N m : ℕ) (hm : m ≤ N) (r : ℂ) (k : U2) :
    (ent 1 0 k + r * ent 1 1 k) ^ m * (ent 0 0 k + r * ent 0 1 k) ^ (N - m) =
      ∑ d ∈ range (N + 1), r ^ d * coef N m d k := by
  have hdeg : ((C (ent 1 1 k) * X + C (ent 1 0 k)) ^ m *
      (C (ent 0 1 k) * X + C (ent 0 0 k)) ^ (N - m)).natDegree < N + 1 := by
    have := (natDegree_mul_le (p := (C (ent 1 1 k) * X + C (ent 1 0 k)) ^ m)
      (q := (C (ent 0 1 k) * X + C (ent 0 0 k)) ^ (N - m))).trans
      (add_le_add (natDegree_linear_pow_le _ _ m) (natDegree_linear_pow_le _ _ (N - m)))
    omega
  set p : ℂ[X] := (C (ent 1 1 k) * X + C (ent 1 0 k)) ^ m *
    (C (ent 0 1 k) * X + C (ent 0 0 k)) ^ (N - m) with hp
  have hev : p.eval r = (ent 1 0 k + r * ent 1 1 k) ^ m * (ent 0 0 k + r * ent 0 1 k) ^ (N - m) := by
    simp [hp]; ring
  rw [← hev, eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_comm]
  congr 1
  rw [hp, coeff_mul, coef]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [coeff_linear_pow, coeff_linear_pow, mono]
  push_cast; ring

theorem continuous_coef (N m d : ℕ) : Continuous (coef N m d) := by
  unfold coef
  exact continuous_finset_sum _ fun ij _ => continuous_const.mul (continuous_mono _ _ _ _)


noncomputable def rowU (p q : ℂ) (h : normSq p + normSq q = 1) : U2 :=
  ⟨!![p, q; -(starRingEnd ℂ) q, (starRingEnd ℂ) p], by
    rw [Matrix.mem_unitaryGroup_iff]
    have h' : p * (starRingEnd ℂ) p + q * (starRingEnd ℂ) q = 1 := by
      rw [Complex.mul_conj, Complex.mul_conj]; exact_mod_cast h
    have h'' : (starRingEnd ℂ) q * q + (starRingEnd ℂ) p * p = 1 := by
      rw [← h']; ring
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose] <;>
      first | linear_combination h' | ring⟩

noncomputable def colU (p q : ℂ) (h : normSq p + normSq q = 1) : U2 :=
  ⟨!![p, -(starRingEnd ℂ) q; q, (starRingEnd ℂ) p], by
    rw [Matrix.mem_unitaryGroup_iff]
    have h' : p * (starRingEnd ℂ) p + q * (starRingEnd ℂ) q = 1 := by
      rw [Complex.mul_conj, Complex.mul_conj]; exact_mod_cast h
    have h'' : (starRingEnd ℂ) q * q + (starRingEnd ℂ) p * p = 1 := by
      rw [← h']; ring
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose] <;>
      first | linear_combination h' | ring⟩




theorem star_eq_adjugate (k : U2) :
    star (k : Matrix (Fin 2) (Fin 2) ℂ) = (detU k)⁻¹ • (k : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
  have h1 : star (k : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ :=
    (Matrix.inv_eq_left_inv (Matrix.UnitaryGroup.star_mul_self k)).symm
  rw [h1, Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

theorem conj_ent (k : U2) :
    (starRingEnd ℂ) (ent 0 0 k) = (detU k)⁻¹ * ent 1 1 k ∧
    (starRingEnd ℂ) (ent 0 1 k) = (detU k)⁻¹ * -ent 1 0 k ∧
    (starRingEnd ℂ) (ent 1 0 k) = (detU k)⁻¹ * -ent 0 1 k ∧
    (starRingEnd ℂ) (ent 1 1 k) = (detU k)⁻¹ * ent 0 0 k := by
  have h := star_eq_adjugate k
  have e : ∀ a b : Fin 2, (starRingEnd ℂ) (ent a b k) =
      ((detU k)⁻¹ • (k : Matrix (Fin 2) (Fin 2) ℂ).adjugate) b a := by
    intro a b
    rw [← h]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> simp [Matrix.adjugate_fin_two, ent]

theorem conj_detU (k : U2) : (starRingEnd ℂ) (detU k) = (detU k)⁻¹ := by
  have h : (star (k : Matrix (Fin 2) (Fin 2) ℂ)).det = (detU k)⁻¹ := by
    rw [star_eq_adjugate, Matrix.det_smul, Matrix.det_adjugate, Fintype.card_fin]
    have hd := detU_ne_zero k
    simp only [detU] at hd ⊢
    norm_num
    field_simp
  rw [← h, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]; rfl

noncomputable def monoDet (α β γ δ : ℕ) (q : ℤ) : C(U2, ℂ) :=
  ⟨fun k => mono α β γ δ k * detU k ^ q, (continuous_mono _ _ _ _).mul (continuous_detU_zpow q)⟩

@[simp] theorem monoDet_apply (α β γ δ : ℕ) (q : ℤ) (k : U2) :
    monoDet α β γ δ q k = mono α β γ δ k * detU k ^ q := rfl

def monoSet : Set C(U2, ℂ) := {f | ∃ (α β γ δ : ℕ) (q : ℤ), f = monoDet α β γ δ q}

theorem monoDet_mul (α β γ δ α' β' γ' δ' : ℕ) (q q' : ℤ) :
    monoDet α β γ δ q * monoDet α' β' γ' δ' q' =
      monoDet (α + α') (β + β') (γ + γ') (δ + δ') (q + q') := by
  ext k
  simp only [ContinuousMap.mul_apply, monoDet_apply, mono, pow_add,
    zpow_add₀ (detU_ne_zero k)]
  ring

theorem star_monoDet (α β γ δ : ℕ) (q : ℤ) :
    star (monoDet α β γ δ q) = ((-1 : ℂ) ^ (β + γ)) •
      monoDet δ γ β α (-((α + β + γ + δ : ℕ) : ℤ) - q) := by
  ext k
  obtain ⟨h00, h01, h10, h11⟩ := conj_ent k
  have hd := detU_ne_zero k
  have hz : detU k ^ (-((α + β + γ + δ : ℕ) : ℤ) - q) =
      (detU k)⁻¹ ^ (α + β + γ + δ) * (detU k)⁻¹ ^ q := by
    rw [zpow_sub₀ hd, _root_.zpow_neg, zpow_natCast, inv_pow, _root_.inv_zpow, div_eq_mul_inv]
  simp only [ContinuousMap.star_apply, monoDet_apply, ContinuousMap.smul_apply, smul_eq_mul, mono,
    star_mul', star_pow, Complex.star_def, h00, h01, h10, h11, map_zpow₀, conj_detU, hz]
  simp only [mul_pow]
  rw [neg_pow (ent 1 0 k), neg_pow (ent 0 1 k)]
  ring

set_option synthInstance.maxHeartbeats 400000 in

noncomputable def monoAlg : StarSubalgebra ℂ C(U2, ℂ) :=
  { (Submodule.span ℂ monoSet).toSubalgebra
      (Submodule.subset_span ⟨0, 0, 0, 0, 0, by ext k; simp [mono]⟩)
      (fun x y hx hy => by
        have hmul := Submodule.mul_mem_mul hx hy
        rw [Submodule.span_mul_span] at hmul
        refine (Submodule.span_le.2 ?_) hmul
        rintro _ ⟨f, ⟨α, β, γ, δ, q, rfl⟩, f', ⟨α', β', γ', δ', q', rfl⟩, rfl⟩
        exact Submodule.subset_span ⟨_, _, _, _, _, monoDet_mul _ _ _ _ _ _ _ _ _ _⟩) with
    star_mem' := by
      intro x hx
      change x ∈ Submodule.span ℂ monoSet at hx
      change star x ∈ Submodule.span ℂ monoSet
      induction hx using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨α, β, γ, δ, q, rfl⟩ := hf
        rw [star_monoDet]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, _, _, _, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx }



theorem eq_zero_of_forall_integral_coeff {g : U2 → ℂ} (hg : Continuous g)
    (h : ∀ (n : ℕ) (q : ℤ) (l₁ l₂ : U2), ∫ k, ((((l₁ * k * l₂ : U2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ n *
      ((k : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q * g k) ∂μK = 0) : g = 0 :=
  _root_.UpperTheory.Reformulated.B.Gwa7.eq_zero_of_forall_integral_coeff hg h

end PW

end GroundTheory.Automorphic.ArchWhittakerC
