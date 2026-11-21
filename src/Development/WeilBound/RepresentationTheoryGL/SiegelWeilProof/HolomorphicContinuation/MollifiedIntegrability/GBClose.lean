import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBBound

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem cls_zero (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s 0 p q R = fun y => Fr s p q R (herm y) := by
  funext y
  simp [cls, Fr, evUV, uM, vM]

theorem herm_spectral (y : E n) : ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ lam : Fin n → ℝ,
    herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ := by
  have hH := herm_isHermitian y
  refine ⟨hH.eigenvectorUnitary, hH.eigenvectorUnitary.2, hH.eigenvalues, ?_⟩
  conv_lhs => rw [hH.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

theorem conj_det (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (A : Mc n) : (k * A * kᴴ).det = A.det := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (k.det), mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]

theorem one_sub_conj (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (c : ℂ) (A : Mc n) :
    (1 : Mc n) + c • (k * A * kᴴ) = k * (1 + c • A) * kᴴ := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, Matrix.mul_smul, Matrix.smul_mul]

theorem det_one_add_herm (y : E n) : ∃ lam : Fin n → ℝ, ∀ c : ℂ,
    ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) ∧ ((1 : Mc n) + herm y * herm y).det = ∏ i, (1 + (lam i : ℂ) ^ 2) := by
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨lam, fun c => ⟨?_, ?_⟩⟩
  · rw [hy, one_sub_conj k hk, conj_det k hk]
    rw [show (1 : Mc n) + c • Matrix.diagonal (fun i => (lam i : ℂ)) = Matrix.diagonal (fun i => 1 + c * lam i) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]]
    simp
  · have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
      rw [hy]
      calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
          = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp

theorem dP_eq (y : E n) : ∃ lam : Fin n → ℝ, dP y = ∏ i, (1 + lam i ^ 2) ∧
    (((dP y : ℝ) : ℂ) = ((1 : Mc n) + herm y * herm y).det) ∧
    ∀ c : ℂ, ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) := by
  obtain ⟨lam, h⟩ := det_one_add_herm y
  have h2 := (h 0).2
  have hre : dP y = ∏ i, (1 + lam i ^ 2) := by
    simp only [dP, h2]
    rw [show (∏ i, (1 + (lam i : ℂ) ^ 2)) = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  refine ⟨lam, hre, ?_, fun c => (h c).1⟩
  rw [hre, h2]; push_cast; rfl

theorem dP_pos (y : E n) : 0 < dP y := by
  obtain ⟨lam, h, -⟩ := dP_eq y
  rw [h]; exact Finset.prod_pos fun i _ => by positivity

theorem herm_mem_Ugood (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : herm y ∈ Ugood s := by
  obtain ⟨lam, -, -, h⟩ := dP_eq y
  have key : ∀ c : ℂ, (c = 1 ∨ c = -1) → ((1 : Mc n) + (c * (Complex.I * s)) • herm y).det ≠ 0 := by
    intro c hc
    rw [h, Finset.prod_ne_zero_iff]
    intro i _ h0
    have h1 := congrArg Complex.re h0
    rcases hc with rfl | rfl <;> rcases hs with rfl | rfl <;> simp at h1
  refine ⟨isUnit_iff_ne_zero.2 ?_, isUnit_iff_ne_zero.2 ?_⟩
  · have := key (-1) (Or.inr rfl); rwa [neg_one_mul, neg_smul, ← sub_eq_add_neg] at this
  · have := key 1 (Or.inl rfl); rwa [one_mul] at this

theorem dP_of_spectral (y : E n) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (lam : Fin n → ℝ)
    (hy : herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ) : dP y = ∏ i, (1 + lam i ^ 2) := by
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
    rw [hy]
    calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
        = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : ((1 : Mc n) + herm y * herm y).det = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) := by
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp
  simp only [dP, h2, Complex.ofReal_re]

theorem det_u_mul_det_v (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (uM s y).det * (vM s y).det = (((dP y : ℝ) : ℂ))⁻¹ := by
  obtain ⟨lam, -, hdP, -⟩ := dP_eq y
  have hg := herm_mem_Ugood s hs y
  have hprod : ((1 : Mc n) - (Complex.I * s) • herm y) * (1 + (Complex.I * s) • herm y) = 1 + herm y * herm y := by
    have hs2 : (Complex.I * s) * (Complex.I * s) = -1 := by
      rcases hs with rfl | rfl <;> simp [← sq, Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs2]
    simp [neg_smul]; abel
  have h1 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) - (Complex.I * s) • herm y) hg.1
  have h2 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) + (Complex.I * s) • herm y) hg.2
  rw [hdP, ← hprod, Matrix.det_mul]
  simp only [uM, vM]
  apply eq_inv_of_mul_eq_one_left
  calc ((1 - (Complex.I * s) • herm y)⁻¹).det * ((1 + (Complex.I * s) • herm y)⁻¹).det *
        ((1 - (Complex.I * s) • herm y).det * (1 + (Complex.I * s) • herm y).det)
      = (((1 - (Complex.I * s) • herm y)⁻¹).det * (1 - (Complex.I * s) • herm y).det) *
        (((1 + (Complex.I * s) • herm y)⁻¹).det * (1 + (Complex.I * s) • herm y).det) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

theorem cls_nat (s : ℂ) (hs : s = 1 ∨ s = -1) (i p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s (i : ℂ) p q R = cls s 0 (p + i) (q + i) R := by
  funext y
  have h := det_u_mul_det_v s hs y
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul, Complex.cpow_neg, Complex.cpow_natCast, pow_add]
  rw [show ((((dP y : ℝ) : ℂ)) ^ i)⁻¹ = ((uM s y).det * (vM s y).det) ^ i by rw [h, inv_pow]]
  ring

theorem prod_flatMap_real {α : Type} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem prod_blocks (N : ℕ) (g : Fin N → Fin n → ℝ) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).prod = ∏ j, ∏ k, g j k := by
  rw [prod_flatMap_real, Fin.prod_univ_def]
  congr 1

theorem length_blocks {α : Type} (N : ℕ) (g : Fin N → Fin n → α) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).length = N * n := by
  simp

theorem prod_sqrt_perm (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∏ k, Real.sqrt (w (σ k) * w k) = ∏ k, w k := by
  have h1 : ∀ k, Real.sqrt (w (σ k) * w k) = Real.sqrt (w (σ k)) * Real.sqrt (w k) := fun k =>
    Real.sqrt_mul (hw _).le _
  simp_rw [h1, Finset.prod_mul_distrib, Equiv.prod_comp σ (fun k => Real.sqrt (w k)), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (hw k).le

theorem conj_mem_Ugood (s : ℂ) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Mc n) (hb : b ∈ Ugood s) :
    k * b * kᴴ ∈ Ugood s := by
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, one_sub_conj k hk, conj_det k hk, neg_smul, ← sub_eq_add_neg]; exact hb.1
  · rw [one_sub_conj k hk, conj_det k hk]; exact hb.2

def conjL (k : Mc n) : Mc n →ₗ[ℂ] Mc n := (LinearMap.mulLeft ℂ k).comp (LinearMap.mulRight ℂ kᴴ)

theorem conjL_apply (k c : Mc n) : conjL k c = k * c * kᴴ := by
  simp [conjL, Matrix.mul_assoc]

theorem contDiff_conj (k : Mc n) : ContDiff ℂ (⊤ : ℕ∞) (fun c : Mc n => k * c * kᴴ) := by
  have : (fun c : Mc n => k * c * kᴴ) = (LinearMap.toContinuousLinearMap (conjL k) : Mc n → Mc n) := by
    funext c; simp [conjL_apply]
  rw [this]; exact ContinuousLinearMap.contDiff _

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem ratBound (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (s : ℂ) (hs : s = 1 ∨ s = -1)
    (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ∃ C : ℝ, ∀ y : E n, ‖(Delta^[N] (cls s 0 p q R)) y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
  obtain ⟨hUo, hFc, c₀, C₀, hc₀, hb⟩ := hB n s hs p q R
  set K : ℝ := ((N * n : ℕ) : ℝ) with hK
  set C₁ : ℝ := max C₀ 0 with hC₁
  refine ⟨(Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁, fun y => ?_⟩
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  set w : Fin n → ℝ := fun i => 1 + |lam i| with hw
  have hwpos : ∀ i, 0 < w i := fun i => by simp only [hw]; positivity
  set W : ℝ := ∏ i, w i with hW
  have hWpos : 0 < W := Finset.prod_pos fun i _ => hwpos i
  set d : Mc n := Matrix.diagonal (fun i => (lam i : ℂ)) with hd
  set ρ : Fin n → Fin n → ℝ := fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|)) with hρ
  have hρpos : ∀ i j, 0 < ρ i j := fun i j => mul_pos hc₀ (Real.sqrt_pos.2 (mul_pos (hwpos i) (hwpos j)))
  have hlink := (hL n (Fr s p q R) (Ugood s) hUo hFc (herm_mem_Ugood s hs)).1 N y
  rw [cls_zero, hlink, hy]
  set F' : Mc n → ℂ := fun c => Fr s p q R (k * c * kᴴ) with hF'
  set U' : Set (Mc n) := {c | k * c * kᴴ ∈ Ugood s} with hU'
  have hU'o : IsOpen U' := hUo.preimage (contDiff_conj k).continuous
  have hF'c : ContDiffOn ℂ (⊤ : ℕ∞) F' U' := hFc.comp (contDiff_conj k).contDiffOn (fun c hc => hc)
  have hdisc : pdisc d ρ ⊆ U' := fun b hb' => (hb k hk lam b hb').1
  have hdmem : d ∈ U' := hdisc (fun i j => by simp [hρpos i j |>.le])
  have hherm' : ∀ y', herm y' ∈ U' := fun y' => conj_mem_Ugood s k hk _ (herm_mem_Ugood s hs y')
  rw [← hI n (Fr s p q R) (Ugood s) hUo hFc k hk N d hdmem, (hL n F' U' hU'o hF'c hherm').2 N d hdmem]
  have hM : ∀ b ∈ pdisc d ρ, ‖F' b‖ ≤ C₁ * W ^ (-((p + q : ℕ) : ℝ)) := fun b hb' =>
    ((hb k hk lam b hb').2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hWpos.le _))
  have hword : ∀ τ : Fin N → Equiv.Perm (Fin n),
      ‖word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖ ≤
        ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
    intro τ
    have h := hC n F' U' hU'o hF'c d ρ hρpos hdisc _ hM ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
    rw [prod_blocks N (fun j k => (((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)).length : ℝ) /
      ρ (τ j k) k)]
    rw [length_blocks]
    show ∏ j, ∏ k, K / ρ ((τ j) k) k = ((K / c₀) ^ n / W) ^ N
    have hblock : ∀ j, ∏ k, K / ρ ((τ j) k) k = (K / c₀) ^ n / W := by
      intro j
      have hs := prod_sqrt_perm (τ j) w hwpos
      simp only [hw] at hs
      simp only [hρ]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hs, div_pow]
      simp only [hW, hw]
      field_simp
    rw [Finset.prod_congr rfl fun j _ => hblock j, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsgn : ∀ τ : Fin N → Equiv.Perm (Fin n), ‖(((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))‖ = 1 := by
    intro τ
    have h : ∀ j, |((Equiv.Perm.sign (τ j) : ℤ))| = 1 := fun j => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (τ j)) with h | h <;> simp [h]
    have h2 : |∏ j, ((Equiv.Perm.sign (τ j) : ℤ))| = 1 := by
      rw [Finset.abs_prod, Finset.prod_eq_one fun j _ => h j]
    rw [Complex.norm_intCast]
    exact_mod_cast h2
  have hdP : dP y ≤ W ^ (2 : ℝ) := by
    rw [dP_of_spectral y k hk lam hy, Real.rpow_two, hW, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    simp only [hw]
    have : lam i ^ 2 = |lam i| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg (lam i)]
  have hWe : ∀ e : ℝ, 0 ≤ e → W ^ (-e) ≤ (dP y) ^ (-e / 2) := by
    intro e he
    have h1 : W ^ (-e) = (W ^ (2 : ℝ)) ^ (-e / 2) := by
      rw [← Real.rpow_mul hWpos.le]; ring_nf
    rw [h1]
    exact Real.rpow_le_rpow_of_nonpos (dP_pos y) hdP (by linarith)
  calc ‖∑ τ : Fin N → Equiv.Perm (Fin n), (((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ)) *
          word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖
      ≤ ∑ τ : Fin N → Equiv.Perm (Fin n), ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        rw [norm_mul, hsgn τ, one_mul]; exact hword τ
    _ = (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (W ^ (-((p + q + N : ℕ) : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : W ^ (-((p + q + N : ℕ) : ℝ)) = W ^ (-((p + q : ℕ) : ℝ)) * (W ^ N)⁻¹ := by
          rw [show (-((p + q + N : ℕ) : ℝ)) = (-((p + q : ℕ) : ℝ)) + (-(N : ℝ)) by push_cast; ring,
            Real.rpow_add hWpos, Real.rpow_neg hWpos.le, Real.rpow_natCast, Real.rpow_neg hWpos.le, Real.rpow_natCast]
        rw [this, div_pow]; ring
    _ ≤ (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_left (hWe _ (by positivity)) ?_
        refine mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (pow_nonneg (div_nonneg (by positivity) hc₀.le) _) _))
          (le_max_right _ _)

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_herm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (herm (n := n)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have hc : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => ((x a b : ℝ) : ℂ)) := fun a b =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin n → ℝ) a))
  simp only [herm]
  push_cast
  exact (((hc i j).add (hc j i)).div_const 2).add ((contDiff_const.mul ((hc i j).sub (hc j i))).div_const 2)

theorem clsGainB_of (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (hT : Twist) (hLg : Lagr) : ClsGain := by
  intro n s hs p q N R
  obtain ⟨hUo, hFc, -⟩ := hB n s hs p q R
  have hH : ContDiff ℝ (⊤ : ℕ∞) (cls s 0 p q R) := by
    rw [cls_zero]
    rw [contDiff_iff_contDiffAt]
    intro y
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Fr s p q R) (herm y) :=
      ((hFc.restrict_scalars ℝ).contDiffAt (hUo.mem_nhds (herm_mem_Ugood s hs y)))
    exact h1.comp y (contDiff_herm n).contDiffAt
  obtain ⟨G, hGc, hG⟩ := hT n (cls s 0 p q R) hH N
  have hcls : ∀ z : ℂ, cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y := by
    intro z; funext y; simp only [cls, neg_zero, Complex.cpow_zero, one_mul]; ring
  set D := n * N with hD
  have hrat : ∀ i : ℕ, ∃ C : ℝ, ∀ y : E n,
      ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖ ≤ C * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2) :=
    fun i => ratBound hC hI hB hL s hs (p + i) (q + i) N R
  choose Ci hCi using hrat
  obtain ⟨CL, hCL⟩ := hLg D
  set Cm : ℝ := ∑ i ∈ Finset.range (D + 1), |Ci i| with hCm
  refine ⟨D + 1, fun j => Polynomial.X ^ (j : ℕ), fun j => G j, fun j => (hGc j).continuous, ⟨CL * Cm, ?_⟩, ?_⟩
  · intro j y
    have hdp := dP_pos y
    have hval : ∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y‖ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
      intro i hi
      have e1 := hG (i : ℂ) y
      rw [← hcls, cls_nat s hs i p q R] at e1
      have hne : (((dP y : ℝ) : ℂ)) ^ (-(i : ℂ)) ≠ 0 := by
        rw [Complex.cpow_neg, Complex.cpow_natCast]; exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hdp.ne'))
      have e2 : ∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y =
          (((dP y : ℝ) : ℂ)) ^ i * (Delta^[N] (cls s 0 (p + i) (q + i) R)) y := by
        rw [e1, Complex.cpow_neg, Complex.cpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hdp.ne')), one_mul]
      rw [e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdp.le]
      have hb := hCi i y
      have hCi_le : |Ci i| ≤ Cm := by
        rw [hCm]
        exact Finset.single_le_sum (f := fun i => |Ci i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      calc dP y ^ i * ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖
          ≤ dP y ^ i * (Ci i * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg hdp.le _)
        _ = Ci i * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
            rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hdp]
            congr 2; push_cast; ring
        _ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCi_le) (Real.rpow_nonneg hdp.le _)
    have := hCL (fun j => G j y) _ hval j (Nat.lt_succ_iff.1 j.2)
    simpa [mul_assoc] using this
  · intro z y
    rw [hcls z, hG z y]
    congr 1
    rw [Finset.sum_range (fun j => z ^ j * G j y)]
    simp [Polynomial.eval_pow, Polynomial.eval_X]

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section
noncomputable section

open Matrix Metric

namespace PositivityTheory.Rg.Sw.WR.K.GB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffOn_cpart {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (i j : Fin n) : ContDiffOn ℂ (⊤ : ℕ∞) (cpart i j F) U := by
  letI : NormedAddCommGroup (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedSpace
  have hle : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
  have h1 : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => fderiv ℂ F b) U :=
    hF.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hU hle
  have h2 := (ContinuousLinearMap.apply ℂ ℂ (Matrix.single i j (1 : ℂ))).contDiff.comp_contDiffOn h1
  exact h2

theorem contDiffOn_word {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) : ∀ L : List (Fin n × Fin n), ContDiffOn ℂ (⊤ : ℕ∞) (word L F) U
  | [] => hF
  | ij :: L => contDiffOn_cpart hU (contDiffOn_word hU hF L) ij.1 ij.2

theorem mem_pdisc_self (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) : b ∈ pdisc b r := by
  intro i j
  simp only [sub_self, norm_zero]
  exact (hr i j).le

theorem shift_apply (b : Mc n) (w : ℂ) (i j a c : Fin n) :
    (b + w • Matrix.single i j (1 : ℂ)) a c - b a c = if i = a ∧ j = c then w else 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left]
  by_cases h : i = a ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ h, if_neg h, mul_zero]

theorem shift_mem (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    (hw : ‖w‖ ≤ r i j) : b + w • Matrix.single i j (1 : ℂ) ∈ pdisc b r := by
  intro a c
  rw [shift_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact hw
  · simpa using (hr a c).le

theorem shift_sub (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    {K l : ℝ} (hK : 0 < K) (hl : 0 ≤ l) (hlK : l + 1 = K) (hw : ‖w‖ = r i j / K) :
    pdisc (b + w • Matrix.single i j (1 : ℂ)) (fun a c => r a c * (l / K)) ⊆ pdisc b r := by
  intro x hx a c
  have h1 := hx a c
  have h2 : ‖x a c - b a c‖ ≤ ‖x a c - (b + w • Matrix.single i j (1 : ℂ)) a c‖ +
      ‖(b + w • Matrix.single i j (1 : ℂ)) a c - b a c‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [shift_apply] at h2
  have hlK' : l / K ≤ 1 := by rw [div_le_one hK]; linarith
  split_ifs at h2 with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [hw] at h2
    have : r i j * (l / K) + r i j / K = r i j := by
      field_simp
      rw [← hlK]
    linarith
  · simp only [norm_zero, add_zero] at h2
    have := mul_le_of_le_one_right (hr a c).le hlK'
    linarith

theorem cauchy_gen {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (M : ℝ) : ∀ (L : List (Fin n × Fin n)) (b : Mc n) (r : Fin n → Fin n → ℝ), (∀ i j, 0 < r i j) →
      pdisc b r ⊆ U → (∀ x ∈ pdisc b r, ‖F x‖ ≤ M) →
      ‖word L F b‖ ≤ (L.map fun ij => (L.length : ℝ) / r ij.1 ij.2).prod * M := by
  intro L
  induction L with
  | nil =>
    intro b r hr _ hM
    simp only [word, List.foldr_nil, List.map_nil, List.prod_nil, one_mul]
    exact hM b (mem_pdisc_self b hr)
  | cons ij L ih =>
    intro b r hr hsub hM
    set K : ℝ := (L.length : ℝ) + 1 with hKdef
    have hK : 0 < K := by positivity
    set δ : ℝ := r ij.1 ij.2 / K with hδdef
    have hδ : 0 < δ := div_pos (hr _ _) hK
    have hδr : δ ≤ r ij.1 ij.2 := div_le_self (hr _ _).le (by simp [hKdef])
    set E : Mc n := Matrix.single ij.1 ij.2 (1 : ℂ) with hE
    set G : Mc n → ℂ := word L F with hG
    have hGd : ContDiffOn ℂ (⊤ : ℕ∞) G U := contDiffOn_word hU hF L
    set f : ℂ → ℂ := fun w => G (b + w • E) with hf
    have hφ : ∀ w : ℂ, HasDerivAt (fun w : ℂ => b + w • E) E w := by
      intro w
      have h := ((hasDerivAt_id w).smul_const E).const_add b
      rw [one_smul] at h
      exact h
    have hin : ∀ w : ℂ, ‖w‖ ≤ δ → b + w • E ∈ U := fun w hw =>
      hsub (shift_mem b hr ij.1 ij.2 (hw.trans hδr))
    have hdiffG : ∀ x ∈ U, DifferentiableAt ℂ G x := fun x hx =>
      ((hGd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    have hfd : DifferentiableOn ℂ f (closedBall 0 δ) := by
      intro w hw
      have hw' : ‖w‖ ≤ δ := by simpa using hw
      exact ((hdiffG _ (hin w hw')).hasFDerivAt.comp_hasDerivAt w (hφ w)).differentiableAt.differentiableWithinAt
    have hderiv : deriv f 0 = word (ij :: L) F b := by
      have h0 : b + (0 : ℂ) • E = b := by simp
      have hb : DifferentiableAt ℂ G (b + (0 : ℂ) • E) := by
        rw [h0]; exact hdiffG b (hsub (mem_pdisc_self b hr))
      have h3 : HasDerivAt f (fderiv ℂ G (b + (0 : ℂ) • E) E) 0 := hb.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hφ 0)
      rw [h3.deriv, h0]
      rfl
    set B : ℝ := (L.map fun ij => K / r ij.1 ij.2).prod * M with hB
    have hsphere : ∀ w ∈ sphere (0 : ℂ) δ, ‖f w‖ ≤ B := by
      intro w hw
      have hw' : ‖w‖ = δ := by simpa using hw
      rcases Nat.eq_zero_or_pos L.length with hL | hL
      · have hLnil : L = [] := List.length_eq_zero_iff.mp hL
        subst hLnil
        show ‖F (b + w • E)‖ ≤ B
        simp only [hB, List.map_nil, List.prod_nil, one_mul]
        exact hM _ (shift_mem b hr ij.1 ij.2 (hw'.le.trans hδr))
      · have hl : (0 : ℝ) < L.length := by exact_mod_cast hL
        set r' : Fin n → Fin n → ℝ := fun a c => r a c * ((L.length : ℝ) / K) with hr'
        have hr'pos : ∀ a c, 0 < r' a c := fun a c => mul_pos (hr a c) (div_pos hl hK)
        have hs := shift_sub b hr ij.1 ij.2 (w := w) hK hl.le (by simp [hKdef]) hw'
        have := ih (b + w • E) r' hr'pos (hs.trans hsub) (fun x hx => hM x (hs hx))
        have heq : (L.map fun ij => (L.length : ℝ) / r' ij.1 ij.2) = (L.map fun ij => K / r ij.1 ij.2) := by
          apply List.map_congr_left
          intro x _
          simp only [hr']
          field_simp
        rw [heq] at this
        exact this
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (hfd.diffContOnCl_ball subset_rfl) hsphere
    rw [hderiv] at hc
    calc ‖word (ij :: L) F b‖ ≤ B / δ := hc
      _ = ((ij :: L).map fun ij' => ((ij :: L).length : ℝ) / r ij'.1 ij'.2).prod * M := by
        simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hB, hδdef, ← hKdef]
        field_simp

theorem cauchyW : CauchyW := by
  intro n F U hU hF b₀ ρ hρ hP M hM L
  exact cauchy_gen hU hF M L b₀ ρ hρ hP hM

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section
noncomputable section

open Matrix Finset

namespace PositivityTheory.Rg.Sw.WR.K.GB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace Inv

def E (p : Fin n × Fin n) : Mc n := Matrix.single p.1 p.2 1

def dd (H : Mc n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b H

def wd (L : List (Mc n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun H g => dd H g) F

theorem top_succ_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [← WithTop.coe_one, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.2 le_top

theorem dd_smooth {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (H : Mc n) : ContDiffOn ℂ (⊤ : ℕ∞) (dd H F) U :=
  (hF.fderiv_of_isOpen hU top_succ_le).clm_apply contDiffOn_const

theorem wd_smooth {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (L : List (Mc n)) : ContDiffOn ℂ (⊤ : ℕ∞) (wd L F) U := by
  induction L with
  | nil => exact hF
  | cons H L ih => exact dd_smooth hU ih H

theorem diffAt {G : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hG : ContDiffOn ℂ (⊤ : ℕ∞) G U)
    {x : Mc n} (hx : x ∈ U) : DifferentiableAt ℂ G x :=
  (hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

theorem dd_congr {f g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (h : ∀ y ∈ U, f y = g y) (H : Mc n)
    {x : Mc n} (hx : x ∈ U) : dd H f x = dd H g x := by
  unfold dd
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) h)]

theorem wd_congr {f g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (h : ∀ y ∈ U, f y = g y)
    (L : List (Mc n)) : ∀ x ∈ U, wd L f x = wd L g x := by
  induction L with
  | nil => exact h
  | cons H L ih => intro x hx; exact dd_congr hU ih H hx

theorem dd_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → Mc n → ℂ) (H : Mc n) {x : Mc n}
    (hg : ∀ i ∈ s, DifferentiableAt ℂ (g i) x) :
    dd H (fun y => ∑ i ∈ s, a i * g i y) x = ∑ i ∈ s, a i * dd H (g i) x := by
  unfold dd
  have h : HasFDerivAt (fun y => ∑ i ∈ s, a i * g i y) (∑ i ∈ s, a i • fderiv ℂ (g i) x) x :=
    HasFDerivAt.fun_sum fun i hi => (hg i hi).hasFDerivAt.const_mul (a i)
  rw [h.fderiv]
  simp

theorem eq_sum_E (H : Mc n) : H = ∑ p : Fin n × Fin n, H p.1 p.2 • E p := by
  ext a b
  simp [E, Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, ite_and]

theorem dd_expand (H : Mc n) (f : Mc n → ℂ) (x : Mc n) :
    dd H f x = ∑ p : Fin n × Fin n, H p.1 p.2 * dd (E p) f x := by
  conv_lhs => rw [eq_sum_E H]
  simp [dd, map_sum, map_smul]

theorem two_le_top' : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
  exact WithTop.coe_le_coe.2 le_top

theorem dd_swap {g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hg : ContDiffOn ℂ (⊤ : ℕ∞) g U)
    (a b : Mc n) {x : Mc n} (hx : x ∈ U) : dd b (dd a g) x = dd a (dd b g) x := by
  have hc : ContDiffAt ℂ (⊤ : ℕ∞) g x := hg.contDiffAt (hU.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℂ g x :=
    hc.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact two_le_top')
  have hd : DifferentiableAt ℂ (fderiv ℂ g) x := (hc.fderiv_right top_succ_le).differentiableAt (by simp)
  have key : ∀ v w : Mc n, fderiv ℂ (fun y => fderiv ℂ g y v) x w = fderiv ℂ (fderiv ℂ g) x w v := by
    intro v w
    have h := (ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp x hd.hasFDerivAt
    exact congrArg (fun L => L w) h.fderiv
  unfold dd
  rw [key, key]
  exact hsymm b a

theorem wd_perm {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    {L L' : List (Mc n)} (h : L.Perm L') : ∀ x ∈ U, wd L F x = wd L' F x := by
  induction h with
  | nil => intro x _; rfl
  | cons a _ ih => intro x hx; exact dd_congr hU ih a hx
  | swap a b l => intro x hx; exact dd_swap hU (wd_smooth hU hF l) a b hx
  | trans _ _ ih1 ih2 => intro x hx; rw [ih1 x hx, ih2 x hx]

theorem wd_comp (T : Mc n →L[ℂ] Mc n) {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (L : List (Mc n)) :
    ∀ x, T x ∈ U → wd L (fun c => F (T c)) x = wd (L.map T) F (T x) := by
  induction L with
  | nil => intro x _; rfl
  | cons H L ih =>
    intro x hx
    have hV : IsOpen (T ⁻¹' U) := hU.preimage T.continuous
    show dd H (wd L (fun c => F (T c))) x = dd (T H) (wd (L.map T) F) (T x)
    rw [dd_congr hV (g := fun c => wd (L.map T) F (T c)) (fun y hy => ih y hy) H hx]
    unfold dd
    have hG : DifferentiableAt ℂ (wd (L.map T) F) (T x) := diffAt hU (wd_smooth hU hF _) hx
    have h := hG.hasFDerivAt.comp x T.hasFDerivAt
    exact congrArg (fun L => L H) h.fderiv

theorem wd_expand {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ∀ (m : ℕ) (v : Fin m → Mc n), ∀ x ∈ U, wd (List.ofFn v) F x =
      ∑ r : Fin m → Fin n × Fin n, (∏ t, v t (r t).1 (r t).2) * wd (List.ofFn fun t => E (r t)) F x := by
  intro m
  induction m with
  | zero => intro v x _; simp [wd]
  | succ m ih =>
    intro v x hx
    rw [List.ofFn_succ]
    show dd (v 0) (wd (List.ofFn fun i => v i.succ) F) x = _
    rw [dd_congr hU (fun y hy => ih (fun i => v i.succ) y hy) (v 0) hx]
    rw [dd_sum _ _ _ _ (fun r _ => diffAt hU (wd_smooth hU hF _) hx)]
    simp_rw [dd_expand (v 0), Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n × Fin n).sum_comp
      (fun r : Fin (m + 1) → Fin n × Fin n => (∏ t, v t (r t).1 (r t).2) * wd (List.ofFn fun t => E (r t)) F x),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r' _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ]
    show _ = _ * dd (E p) (wd (List.ofFn fun t => E (r' t)) F) x
    ring

theorem sum_perm_of_noninj {α : Type*} [AddCommMonoid α] (h : (Fin n → Fin n) → α)
    (h0 : ∀ c, ¬ Function.Injective c → h c = 0) :
    ∑ c : Fin n → Fin n, h c = ∑ π : Equiv.Perm (Fin n), h π := by
  classical
  rw [← Finset.sum_filter_of_ne (f := h) (p := Function.Injective) (fun c _ hc => by_contra fun hn => hc (h0 c hn))]
  refine Finset.sum_bij' (fun c hc => Equiv.ofBijective c
      ((Finite.injective_iff_bijective).1 (Finset.mem_filter.1 hc).2)) (fun π _ => ⇑π) ?_ ?_ ?_ ?_ ?_
  · intro c _; exact Finset.mem_univ _
  · intro π _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, π.injective⟩
  · intro c _; rfl
  · intro π _; ext; rfl
  · intro c _; rfl

theorem det_sub_zero (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) (hc : ¬ Function.Injective c) :
    (A.submatrix c id).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hc
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])

theorem alg (A B : Matrix (Fin n) (Fin n) ℂ) (Φ : (Fin n → Fin n × Fin n) → ℂ)
    (hΦ : ∀ r (π : Equiv.Perm (Fin n)), Φ (r ∘ π) = Φ r) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ r : Fin n → Fin n × Fin n, (∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r =
      A.det * B.det * ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (fun t => (σ t, t)) := by
  classical
  have s1 : ∀ r : Fin n → Fin n × Fin n, ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r) =
      (A.submatrix (fun t => (r t).1) id).det * (∏ t, B (r t).2 t) * Φ r := by
    intro r
    rw [← Matrix.det_transpose, Matrix.det_apply', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id]
    ring
  have e1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ r : Fin n → Fin n × Fin n, (∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r =
      ∑ r : Fin n → Fin n × Fin n, (A.submatrix (fun t => (r t).1) id).det * (∏ t, B (r t).2 t) * Φ r := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => s1 r
  rw [e1]
  let eP := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin n) (fun _ => Fin n)
  rw [← eP.symm.sum_comp, Fintype.sum_prod_type]
  have e2 : ∀ c : Fin n → Fin n, ∑ d : Fin n → Fin n,
      (A.submatrix (fun t => ((eP.symm (c, d)) t).1) id).det * (∏ t, B ((eP.symm (c, d)) t).2 t) * Φ (eP.symm (c, d)) =
      (A.submatrix c id).det * ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (c t, d t)) := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [eP, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    ring
  simp_rw [e2]
  rw [sum_perm_of_noninj _ (fun c hc => by rw [det_sub_zero A c hc, zero_mul])]
  have e3 : ∀ π : Equiv.Perm (Fin n), (A.submatrix π id).det * ∑ d : Fin n → Fin n,
      (∏ t, B (d t) t) * Φ (fun t => (π t, d t)) =
      ((Equiv.Perm.sign π : ℤ) : ℂ) * A.det * ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) := by
    intro π
    rw [Matrix.det_permute]
    have : ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (π t, d t)) =
        ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) := by
      refine Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl (Fin n))) _ _ fun d => ?_
      have h1 : (fun t => (π t, d t)) = (fun i => (i, (Equiv.arrowCongr π (Equiv.refl (Fin n)) d) i)) ∘ π := by
        funext t; simp [Equiv.arrowCongr_apply]
      rw [h1, hΦ]
      congr 1
      refine Finset.prod_congr rfl fun t _ => ?_
      simp [Equiv.arrowCongr_apply]
    rw [this]
  simp_rw [e3]
  have e4 : ∑ π : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * A.det *
        ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) =
      A.det * ∑ e : Fin n → Fin n, (B.submatrix e id).det * Φ (fun i => (i, e i)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.det_apply' (B.submatrix e id), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Matrix.submatrix_apply, id]
    ring
  rw [e4, sum_perm_of_noninj _ (fun c hc => by rw [det_sub_zero B c hc, zero_mul])]
  have e5 : ∀ ρ : Equiv.Perm (Fin n), (B.submatrix ρ id).det * Φ (fun i => (i, ρ i)) =
      B.det * (((Equiv.Perm.sign ρ⁻¹ : ℤ) : ℂ) * Φ (fun t => (ρ⁻¹ t, t))) := by
    intro ρ
    rw [Matrix.det_permute, Equiv.Perm.sign_inv]
    have h2 : (fun i => (i, ρ i)) = (fun t => (ρ⁻¹ t, t)) ∘ ρ := by
      funext i; simp
    rw [h2, hΦ]
    ring
  simp_rw [e5, ← Finset.mul_sum]
  rw [Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) (fun ρ => ((Equiv.Perm.sign ρ⁻¹ : ℤ) : ℂ) * Φ (fun t => (ρ⁻¹ t, t)))
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (fun t => (σ t, t))) (fun ρ => rfl)]
  ring

theorem deltaC_eq (F : Mc n → ℂ) (x : Mc n) : DeltaC F x = ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * wd (List.ofFn fun t => E (σ t, t)) F x := by
  unfold DeltaC
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [List.ofFn_eq_map, wd, List.foldr_map]
  rfl

theorem deltaC_smooth {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC F) U := by
  have : DeltaC F = fun x => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * wd (List.ofFn fun t => E (σ t, t)) F x := funext (deltaC_eq F)
  rw [this]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (wd_smooth hU hF _)

theorem deltaC_congr {f g : Mc n → ℂ} {V : Set (Mc n)} (hV : IsOpen V) (h : ∀ y ∈ V, f y = g y)
    {x : Mc n} (hx : x ∈ V) : DeltaC f x = DeltaC g x := by
  rw [deltaC_eq, deltaC_eq]
  exact Finset.sum_congr rfl fun σ _ => by rw [wd_congr hV h _ x hx]

theorem conj_single (k : Mc n) (p : Fin n × Fin n) (c d : Fin n) :
    (k * E p * kᴴ) c d = k c p.1 * (k.map star) d p.2 := by
  simp [E, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]

theorem invar_one {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    {k : Mc n} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Mc n) (hb : k * b * kᴴ ∈ U) :
    DeltaC (fun c => F (k * c * kᴴ)) b = DeltaC F (k * b * kᴴ) := by
  let Tl : Mc n →ₗ[ℂ] Mc n :=
    { toFun := fun c => k * c * kᴴ
      map_add' := fun x y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a x => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let T : Mc n →L[ℂ] Mc n := LinearMap.toContinuousLinearMap Tl
  have hT : ∀ c, T c = k * c * kᴴ := fun c => rfl
  have hFT : (fun c => F (k * c * kᴴ)) = fun c => F (T c) := by funext c; rw [hT]
  have hTb : T b ∈ U := by rw [hT]; exact hb
  rw [deltaC_eq, deltaC_eq, hFT]
  have h1 : ∀ σ : Equiv.Perm (Fin n), wd (List.ofFn fun t => E (σ t, t)) (fun c => F (T c)) b =
      ∑ r : Fin n → Fin n × Fin n, (∏ t, (k (r t).1 (σ t) * (k.map star) (r t).2 t)) *
        wd (List.ofFn fun t => E (r t)) F (k * b * kᴴ) := by
    intro σ
    rw [wd_comp T hU hF _ b hTb, List.map_ofFn, hT b, wd_expand hU hF n _ _ hb]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [Function.comp_apply, hT]
    exact conj_single k (σ t, t) (r t).1 (r t).2
  simp_rw [h1]
  rw [alg k (k.map star) (fun r => wd (List.ofFn fun t => E (r t)) F (k * b * kᴴ))
    (fun r π => wd_perm hU hF (Equiv.Perm.ofFn_comp_perm π fun t => E (r t)) _ hb)]
  have hu : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk
  have hdet : k.det * (k.map star).det = 1 := by
    have h2 : (k.map star).det = star k.det := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
      rfl
    have h3 := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h3
    rw [h2, mul_comm]
    exact h3
  rw [hdet, one_mul]

theorem invar_iter {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ∀ N : ℕ, ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC^[N] F) U := by
  intro N
  induction N with
  | zero => exact hF
  | succ N ih => rw [Function.iterate_succ_apply']; exact deltaC_smooth hU ih

end Inv

open PositivityTheory.Rg.Sw.WR.K.GB.Inv in
theorem invar : Invar := by
  intro n F U hU hF k hk N
  induction N with
  | zero => intro b _; rfl
  | succ N ih =>
    intro b hb
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hV : IsOpen {c : Mc n | k * c * kᴴ ∈ U} :=
      hU.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    rw [deltaC_congr hV (g := fun c => (DeltaC^[N] F) (k * c * kᴴ)) (fun y hy => ih y hy) hb]
    exact invar_one hU (invar_iter hU hF N) hk b hb

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hermL (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] Mc n :=
  LinearMap.toContinuousLinearMap
    { toFun := herm
      map_add' := fun x y => by
        ext i j; simp only [herm, Pi.add_apply, Matrix.add_apply]; push_cast; ring
      map_smul' := fun c x => by
        ext i j; simp only [herm, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, RingHom.id_apply]
        rw [Complex.real_smul]; push_cast; ring }

theorem hermL_apply (x : Fin n → Fin n → ℝ) : hermL n x = herm x := rfl

theorem vkl_re (k l a b : Fin n) :
    (vkl k l a b).re = (if a = k ∧ b = l then 1 / 2 else 0) + (if a = l ∧ b = k then 1 / 2 else 0) := by
  unfold vkl; split_ifs <;> simp

theorem vkl_im (k l a b : Fin n) :
    (vkl k l a b).im = (if a = k ∧ b = l then 1 / 2 else 0) + (if a = l ∧ b = k then -1 / 2 else 0) := by
  unfold vkl; split_ifs <;> simp

theorem herm_re_im_vkl (k l : Fin n) :
    herm (fun a b => (vkl k l a b).re) + Complex.I • herm (fun a b => (vkl k l a b).im) =
      Matrix.single l k (1 : ℂ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  unfold herm
  dsimp only
  rw [vkl_re, vkl_re, vkl_im, vkl_im]
  have e1 : (if j = k ∧ i = l then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e2 : (if j = l ∧ i = k then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e3 : (if i = k ∧ j = l then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e4 : (if i = l ∧ j = k then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e5 : (if i = l ∧ j = k then (-1 / 2 : ℝ) else 0) = -1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e6 : (if j = l ∧ i = k then (-1 / 2 : ℝ) else 0) = -1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e7 : (if l = i ∧ k = j then (1 : ℂ) else 0) = (((if i = l ∧ j = k then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    by_cases h : i = l ∧ j = k
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e1, e2, e3, e4, e5, e6, e7]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

variable {F G : Mc n → ℂ} {U : Set (Mc n)}

theorem dkl_comp_herm (k l : Fin n) (y : Fin n → Fin n → ℝ) (hd : DifferentiableAt ℂ G (herm y)) :
    Dkl k l (fun y => G (herm y)) y = cpart l k G (herm y) := by
  have hG : HasFDerivAt G ((fderiv ℂ G (herm y)).restrictScalars ℝ) (herm y) :=
    hd.hasFDerivAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun y => G (herm y)) (((fderiv ℂ G (herm y)).restrictScalars ℝ).comp (hermL n)) y :=
    hG.comp y (hermL n).hasFDerivAt
  unfold Dkl dirC cpart
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_re_im_vkl k l, map_add, map_smul, smul_eq_mul]

theorem cpart_contDiffOn (i j : Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (cpart i j F) U := by
  have h := hF.fderiv_of_isOpen hU (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by norm_cast)
  exact h.clm_apply contDiffOn_const

theorem differentiableAt_of_cdo (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) {b : Mc n} (hb : b ∈ U) :
    DifferentiableAt ℂ F b :=
  ((hF.contDiffAt (hU.mem_nhds hb)).differentiableAt (by norm_cast))

theorem foldr_herm (τ : Fin n → Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U)
    (L : List (Fin n)) :
    L.foldr (fun k g => Dkl k (τ k) g) (fun y => F (herm y)) =
        (fun y => (L.foldr (fun k g => cpart (τ k) k g) F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (τ k) k g) F) U := by
  induction L with
  | nil => exact ⟨rfl, hF⟩
  | cons a L ih =>
    refine ⟨?_, cpart_contDiffOn _ _ hU ih.2⟩
    simp only [List.foldr_cons]
    rw [ih.1]
    funext y
    exact dkl_comp_herm a (τ a) y (differentiableAt_of_cdo hU ih.2 (hh y))

theorem deltaC_contDiffOn (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC F) U := by
  have : DeltaC F = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.finRange n).foldr (fun k g => cpart (σ k) k g) F b := by
    funext b; simp [DeltaC, Finset.sum_apply]
  rw [this]
  refine ContDiffOn.sum fun σ _ => ContDiffOn.const_smul _ ?_
  have key : ∀ L : List (Fin n), ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (σ k) k g) F) U := by
    intro L; induction L with
    | nil => exact hF
    | cons a L ih => exact cpart_contDiffOn _ _ hU ih
  exact key _

theorem delta_herm (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) :
    Delta (fun y => F (herm y)) = fun y => DeltaC F (herm y) := by
  funext y
  simp only [Delta, DeltaC, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [(foldr_herm σ hU hF hh _).1]

theorem iterate_herm (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) (N : ℕ) :
    (Delta^[N] (fun y => F (herm y))) = (fun y => (DeltaC^[N] F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC^[N] F) U := by
  induction N with
  | zero => exact ⟨rfl, hF⟩
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
    exact ⟨delta_herm hU ih.2 hh, deltaC_contDiffOn hU ih.2⟩

theorem eqOn_cpart (i j : Fin n) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (cpart i j H) (cpart i j H') U := fun b hb => by
  have : H =ᶠ[nhds b] H' := Filter.eventuallyEq_of_mem (hU.mem_nhds hb) h
  simp only [cpart, this.fderiv_eq]

theorem eqOn_word (L : List (Fin n × Fin n)) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (word L H) (word L H') U := by
  induction L with
  | nil => exact h
  | cons a L ih => exact eqOn_cpart a.1 a.2 hU ih

theorem word_contDiffOn (L : List (Fin n × Fin n)) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (word L F) U := by
  induction L with
  | nil => exact hF
  | cons a L ih => exact cpart_contDiffOn _ _ hU ih

theorem cpart_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (i j : Fin n) (hU : IsOpen U)
    (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (cpart i j (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * cpart i j (f t) x) U := by
  intro b hb
  have hd : ∀ t ∈ s, DifferentiableAt ℂ (fun x => c t * f t x) b := fun t _ =>
    (differentiableAt_of_cdo hU (hf t) hb).const_mul (c t)
  simp only [cpart]
  have hs : HasFDerivAt (fun x => ∑ t ∈ s, c t * f t x) (∑ t ∈ s, fderiv ℂ (fun x => c t * f t x) b) b :=
    HasFDerivAt.fun_sum (fun t ht => (hd t ht).hasFDerivAt)
  rw [hs.fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : HasFDerivAt (fun x => c t * f t x) (c t • fderiv ℂ (f t) b) b :=
    (differentiableAt_of_cdo hU (hf t) hb).hasFDerivAt.const_mul (c t)
  rw [h1.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem word_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (L : List (Fin n × Fin n))
    (hU : IsOpen U) (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (word L (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * word L (f t) x) U := by
  induction L with
  | nil => intro b _; rfl
  | cons a L ih =>
    intro b hb
    have h1 := eqOn_cpart a.1 a.2 hU ih hb
    simp only [word, List.foldr_cons] at h1 ⊢
    rw [h1]
    exact cpart_sum s c (fun t => word L (f t)) a.1 a.2 hU (fun t => word_contDiffOn L hU (hf t)) hb

theorem word_append (L₁ L₂ : List (Fin n × Fin n)) (H : Mc n → ℂ) :
    word (L₁ ++ L₂) H = word L₁ (word L₂ H) := by
  simp [word, List.foldr_append]

def blk (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (σ k, k)

theorem deltaC_eq_word (H : Mc n → ℂ) :
    DeltaC H = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * word (blk σ) H b := by
  funext b
  simp only [DeltaC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, word, blk, List.foldr_map]

theorem flat_succ {N : ℕ} (τ : Fin (N + 1) → Equiv.Perm (Fin n)) :
    (List.finRange (N + 1)).flatMap (fun j => blk (τ j)) =
      blk (τ 0) ++ (List.finRange N).flatMap (fun j => blk (τ j.succ)) := by
  rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem deltaC_iter_word (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (N : ℕ) :
    Set.EqOn (DeltaC^[N] F) (fun b => ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => blk (τ j)) F b) U := by
  induction N with
  | zero => intro b _; simp [word]
  | succ N ih =>
    intro b hb
    rw [Function.iterate_succ_apply', deltaC_eq_word]
    dsimp only
    have step : ∀ σ : Equiv.Perm (Fin n), word (blk σ) (DeltaC^[N] F) b =
        ∑ τ : Fin N → Equiv.Perm (Fin n), ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
          word (blk σ ++ (List.finRange N).flatMap fun j => blk (τ j)) F b := by
      intro σ
      rw [eqOn_word (blk σ) hU ih hb]
      have hw := word_sum (Finset.univ : Finset (Fin N → Equiv.Perm (Fin n)))
        (fun τ => ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))
        (fun τ => word ((List.finRange N).flatMap fun j => blk (τ j)) F) (blk σ) hU
        (fun τ => word_contDiffOn _ hU hF) hb
      rw [hw]
      simp only [word_append]
    simp only [step, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Equiv.Perm (Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.consEquiv_apply, flat_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
    push_cast
    ring

theorem link : Link := by
  intro n F U hU hF hh
  exact ⟨fun N y => by rw [(iterate_herm hU hF hh N).1],
    fun N b hb => (deltaC_iter_word hU hF N hb).trans (by simp only [blk])⟩

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

namespace TW

variable {n : ℕ}

theorem dirC_mul {f g : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => f x * g x) w y = f y * dirC g w y + g y * dirC f w y := by
  unfold dirC
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dirC_const_mul {f : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (a : ℂ)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => a * f x) w y = a * dirC f w y := by
  unfold dirC
  rw [(hf.hasFDerivAt.const_mul a).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dirC_sum {ι : Type*} (s : Finset ι) {A : ι → E n → ℂ} {y : E n}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) y) (w : Fin n → Fin n → ℂ) :
    dirC (fun x => ∑ i ∈ s, A i x) w y = ∑ i ∈ s, dirC (A i) w y := by
  unfold dirC
  rw [(HasFDerivAt.fun_sum (fun i hi => (h i hi).hasFDerivAt)).fderiv]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

theorem dirC_exp {g : E n → ℂ} {y : E n} (hg : DifferentiableAt ℝ g y) (w : Fin n → Fin n → ℂ) :
    dirC (fun x => Complex.exp (g x)) w y = Complex.exp (g y) * dirC g w y := by
  unfold dirC
  rw [hg.hasFDerivAt.cexp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dirC_zero (w : Fin n → Fin n → ℂ) (y : E n) : dirC (0 : E n → ℂ) w y = 0 := by
  simp [dirC]

theorem diff_of {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : E n) : DifferentiableAt ℝ f y :=
  (contDiff_infty_iff_fderiv.1 hf).1 y

theorem contDiff_dirC {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => dirC f w y) := by
  have h1 := (contDiff_infty_iff_fderiv.1 hf).2
  unfold dirC
  exact (h1.clm_apply contDiff_const).add (contDiff_const.mul (h1.clm_apply contDiff_const))

theorem contDiff_Dkl {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l f) := contDiff_dirC hf _

theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm]
  apply Complex.ext <;> simp <;> ring

theorem dP_pos (y : E n) : 0 < dP y := by
  have hH := herm_isHermitian y
  have h1 : (1 + herm y * herm y).PosDef := by
    have := (Matrix.PosDef.one (n := Fin n) (R := ℂ)).add_posSemidef
      (posSemidef_conjTranspose_mul_self (herm y))
    rwa [hH.eq] at this
  exact (Complex.pos_iff.1 h1.det_pos).1

theorem contDiff_coord (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => y a b) :=
  (contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin n → ℝ) a)

theorem contDiff_herm_entry (i j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => herm y i j) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((y i j + y j i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_coord i j).add (contDiff_coord j i))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((y i j - y j i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_coord i j).sub (contDiff_coord j i))
  simp only [herm]
  exact (h1.div_const 2).add ((contDiff_const.mul h2).div_const 2)

theorem contDiff_dPc : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (1 + herm y * herm y).det) := by
  have hM : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (1 + herm y * herm y) i j) := by
    intro i j
    simp only [Matrix.add_apply, Matrix.mul_apply]
    exact contDiff_const.add (ContDiff.sum fun k _ => (contDiff_herm_entry i k).mul (contDiff_herm_entry k j))
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)

theorem contDiff_dP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => dP y) := by
  unfold dP
  exact Complex.reCLM.contDiff.comp contDiff_dPc

def Lc (y : E n) : ℂ := ((Real.log (dP y) : ℝ) : ℂ)

theorem contDiff_Lc : ContDiff ℝ (⊤ : ℕ∞) (Lc (n := n)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_dP.log fun y => (dP_pos y).ne')

def W (z : ℂ) (y : E n) : ℂ := Complex.exp (-z * Lc y)

theorem contDiff_W_apply (z : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (W (n := n) z) :=
  (contDiff_const.mul contDiff_Lc).cexp

theorem cpow_eq (z : ℂ) (y : E n) : ((dP y : ℝ) : ℂ) ^ (-z) = W z y := by
  have hp := dP_pos y
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_log hp.le]
  unfold W Lc
  congr 1
  ring

def om (k l : Fin n) : E n → ℂ := Dkl k l Lc

theorem contDiff_om (k l : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (om k l) := contDiff_Dkl contDiff_Lc k l

def sh (c : ℕ → E n → ℂ) : ℕ → E n → ℂ
  | 0 => fun _ => 0
  | j + 1 => c j

def TD (k l : Fin n) (c : ℕ → E n → ℂ) : ℕ → E n → ℂ :=
  fun j y => Dkl k l (c j) y - om k l y * sh c j y

theorem contDiff_sh {c : ℕ → E n → ℂ} (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sh c j) := by
  cases j with
  | zero => exact contDiff_const
  | succ j => exact hc j

theorem TD_smooth {c : ℕ → E n → ℂ} (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) (k l : Fin n) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (TD k l c j) :=
  (contDiff_Dkl (hc j) k l).sub ((contDiff_om k l).mul (contDiff_sh hc j))

theorem TD_supp {c : ℕ → E n → ℂ} {M : ℕ} (hM : ∀ j, M ≤ j → c j = 0) (k l : Fin n) :
    ∀ j, M + 1 ≤ j → TD k l c j = 0 := by
  intro j hj
  funext y
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : c (i + 1) = 0 := hM _ (by omega)
  have h2 : c i = 0 := hM _ (by omega)
  simp only [TD, sh, h1, h2, Dkl, dirC_zero, Pi.zero_apply, mul_zero, sub_zero]

theorem step (z : ℂ) (k l : Fin n) (c : ℕ → E n → ℂ) (M : ℕ) (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j))
    (hM : ∀ j, M ≤ j → c j = 0) :
    Dkl k l (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + 1), z ^ j * TD k l c j y := by
  funext y
  have hd : ∀ j, DifferentiableAt ℝ (c j) y := fun j => diff_of (hc j) y
  have hdz : ∀ j, DifferentiableAt ℝ (fun x => z ^ j * c j x) y := fun j => (hd j).const_mul _
  have hS : DifferentiableAt ℝ (fun x => ∑ j ∈ Finset.range M, z ^ j * c j x) y :=
    DifferentiableAt.fun_sum fun j _ => hdz j
  have hL : DifferentiableAt ℝ (Lc (n := n)) y := diff_of contDiff_Lc y
  have hW : dirC (W z) (vkl k l) y = W z y * (-z * om k l y) := by
    unfold W
    rw [dirC_exp (hL.const_mul _), dirC_const_mul hL]
    rfl
  have hcM : dirC (c M) (vkl k l) y = 0 := by rw [hM M le_rfl]; exact dirC_zero _ _
  unfold Dkl
  rw [dirC_mul (diff_of (contDiff_W_apply z) y) hS, dirC_sum _ (fun j _ => hdz j), hW]
  simp only [TD, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [sh, mul_zero, Dkl, hcM, add_zero, pow_zero, one_mul]
  have e1 : ∀ j ∈ Finset.range M, dirC (fun x => z ^ j * c j x) (vkl k l) y = z ^ j * dirC (c j) (vkl k l) y :=
    fun j _ => dirC_const_mul (hd j) _ _
  rw [Finset.sum_congr rfl e1]
  have key : ∑ j ∈ Finset.range M, z ^ (j + 1) * (om k l y * c j y) =
      z * om k l y * ∑ j ∈ Finset.range M, z ^ j * c j y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  ring

theorem foldr_smooth (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) → ∀ j, ContDiff ℝ (⊤ : ℕ∞) ((l.foldr (fun k c' => TD k (f k) c') c) j)
  | [], c, hc => hc
  | a :: l, c, hc => TD_smooth (foldr_smooth f l c hc) a (f a)

theorem foldr_supp (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ) (M : ℕ),
    (∀ j, M ≤ j → c j = 0) → ∀ j, M + l.length ≤ j → (l.foldr (fun k c' => TD k (f k) c') c) j = 0
  | [], c, M, hM => by simpa using hM
  | a :: l, c, M, hM => by
      intro j hj
      simp only [List.foldr_cons]
      exact TD_supp (M := M + l.length) (foldr_supp f l c M hM) a (f a) j
        (by simp only [List.length_cons] at hj; omega)

theorem word (z : ℂ) (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ) (M : ℕ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) → (∀ j, M ≤ j → c j = 0) →
    l.foldr (fun k g => Dkl k (f k) g) (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + l.length), z ^ j * (l.foldr (fun k c' => TD k (f k) c') c) j y
  | [], c, M, _, _ => by simp
  | a :: l, c, M, hc, hM => by
      rw [List.foldr_cons, word z f l c M hc hM, List.foldr_cons, List.length_cons, ← add_assoc]
      exact step z a (f a) _ (M + l.length) (foldr_smooth f l c hc) (foldr_supp f l c M hM)

def TDelta (c : ℕ → E n → ℂ) : ℕ → E n → ℂ := fun j y =>
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((List.finRange n).foldr (fun k c' => TD k (σ k) c') c) j y

theorem TDelta_smooth {c : ℕ → E n → ℂ} (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (TDelta c j) :=
  ContDiff.sum fun σ _ => contDiff_const.mul (foldr_smooth σ _ c hc j)

theorem TDelta_supp {c : ℕ → E n → ℂ} {M : ℕ} (hM : ∀ j, M ≤ j → c j = 0) :
    ∀ j, M + n ≤ j → TDelta c j = 0 := by
  intro j hj
  funext y
  simp only [TDelta, Pi.zero_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [foldr_supp σ (List.finRange n) c M hM j (by simpa using hj)]
  simp

theorem delta_step (z : ℂ) (c : ℕ → E n → ℂ) (M : ℕ) (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j))
    (hM : ∀ j, M ≤ j → c j = 0) :
    Delta (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + n), z ^ j * TDelta c j y := by
  funext y
  unfold Delta
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [word z _ (List.finRange n) c M hc hM, List.length_finRange]
  simp only [TDelta, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => by ring

theorem iter_smooth : ∀ (N : ℕ) {c : ℕ → E n → ℂ}, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) →
    ∀ j, ContDiff ℝ (⊤ : ℕ∞) ((TDelta^[N] c) j)
  | 0, _, hc => hc
  | N + 1, c, hc => by
      rw [Function.iterate_succ_apply]
      exact iter_smooth N (TDelta_smooth hc)

theorem iter (z : ℂ) : ∀ (N : ℕ) (c : ℕ → E n → ℂ) (M : ℕ), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) →
    (∀ j, M ≤ j → c j = 0) →
    Delta^[N] (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + n * N), z ^ j * (TDelta^[N] c) j y
  | 0, c, M, _, _ => by simp
  | N + 1, c, M, hc, hM => by
      rw [Function.iterate_succ_apply, delta_step z c M hc hM,
        iter z N (TDelta c) (M + n) (TDelta_smooth hc) (TDelta_supp hM), Function.iterate_succ_apply,
        show M + n + n * N = M + n * (N + 1) by ring]

end TW

open TW in
theorem twist : Twist := by
  intro n H hH N
  let c0 : ℕ → E n → ℂ := fun j => if j = 0 then H else 0
  have hc0 : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c0 j) := by
    intro j
    by_cases h : j = 0
    · simp only [c0, h, if_true]; exact hH
    · simp only [c0, h, if_false]; exact contDiff_const
  have hc0s : ∀ j, 1 ≤ j → c0 j = 0 := by
    intro j hj
    simp only [c0, show j ≠ 0 by omega, if_false]
  refine ⟨TDelta^[N] c0, iter_smooth N hc0, ?_⟩
  intro z y
  have h0 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * H y) =
      fun y => W z y * ∑ j ∈ Finset.range 1, z ^ j * c0 j y := by
    funext y
    simp [c0, cpow_eq]
  rw [h0, iter z N c0 1 hc0 hc0s, cpow_eq, add_comm 1 (n * N)]

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

theorem lagr : Lagr := by
  intro D
  set V : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ := Matrix.vandermonde fun i => ((i : ℕ) : ℂ) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hij : i < j := (Finset.mem_Ioi.1 hj)
    intro h
    have : ((j : ℕ) : ℂ) = ((i : ℕ) : ℂ) := by linear_combination h
    have := Nat.cast_injective this
    exact absurd (Fin.ext this) (ne_of_gt hij)
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.2 hdet
  set W := V⁻¹ with hW
  refine ⟨∑ j, ∑ i, ‖W j i‖, fun c B hB j hj => ?_⟩
  set cv : Fin (D + 1) → ℂ := fun j => c j with hcv
  have hvals : ∀ i : Fin (D + 1), V.mulVec cv i = ∑ j ∈ Finset.range (D + 1), (((i : ℕ) : ℕ) : ℂ) ^ j * c j := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hcv]
    rw [Fin.sum_univ_eq_sum_range (fun k => ((i : ℕ) : ℂ) ^ k * c k)]
  have hB' : ∀ i : Fin (D + 1), ‖V.mulVec cv i‖ ≤ B := fun i => by
    rw [hvals i]; exact hB i (Nat.lt_succ_iff.1 i.2)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  have hinv : W.mulVec (V.mulVec cv) = cv := by
    rw [Matrix.mulVec_mulVec, hW, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  set jj : Fin (D + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hc : c j = ∑ i, W jj i * V.mulVec cv i := by
    have := congrFun hinv jj
    simp only [Matrix.mulVec, dotProduct, hcv] at this ⊢
    rw [this]
  rw [hc]
  calc ‖∑ i, W jj i * V.mulVec cv i‖ ≤ ∑ i, ‖W jj i * V.mulVec cv i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖W jj i‖ * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB' i) (norm_nonneg _)
    _ = (∑ i, ‖W jj i‖) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ i, ‖W j i‖) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact Finset.single_le_sum (f := fun j => ∑ i, ‖W j i‖) (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _)
          (Finset.mem_univ jj)

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section
namespace PositivityTheory.Rg.Sw.WR.K.GB

theorem clsGainB : PositivityTheory.Rg.Sw.WR.ClsGain := clsGainB_of cauchyW invar pBound link twist lagr

end PositivityTheory.Rg.Sw.WR.K.GB
end
