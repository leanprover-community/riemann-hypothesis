import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FinrankUperpOfDet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

lemma isHerm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    (gramM k r z z' g).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [gramM]
  exact (ggHerm_swap _ (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r) _ _).symm

def PosCount : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 →
    Fintype.card {i // 0 < (isHerm k r z z' γ).eigenvalues i} ≤ r + 1

def NonposCount : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 →
    Fintype.card {i // ¬ 0 < (isHerm k r z z' γ).eigenvalues i} ≤ r + 1

end PI.FrameInd
end
end

section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section
namespace PI.FrameInd.CountsW

open PI.FrameInd

def extZ {n : Type*} (p : n → Prop) [DecidablePred p] : ({i // p i} → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun y i := if h : p i then y ⟨i, h⟩ else 0
  map_add' y y' := by funext i; by_cases h : p i <;> simp [h]
  map_smul' c y := by funext i; by_cases h : p i <;> simp [h]

lemma extZ_apply {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ) (i : n) :
    extZ p y i = if h : p i then y ⟨i, h⟩ else 0 := rfl

lemma extZ_eq_zero {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ)
    (hy : extZ p y = 0) : y = 0 := by
  funext ⟨i, h⟩
  have h1 := congrFun hy i
  simpa [extZ_apply, h] using h1

lemma diag_eq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A * (hA.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h

lemma U_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) (hw : (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w = 0) : w = 0 := by
  have hu : star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  calc w = (star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ w := by
        rw [hu, Matrix.one_mulVec]
    _ = star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w) := by
        rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hw, Matrix.mulVec_zero]

lemma re_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) :
    (herm A ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w) ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w)).re =
      ∑ i, hA.eigenvalues i * Complex.normSq (w i) := by
  rw [herm_mulVec_mulVec, diag_eq, herm, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [mulVec_diagonal, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma blockA_re (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hz : inWb k r z)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (hc : ∀ b, c (Sum.inr b) = 0) :
    (herm (gramM k r z z' γ) c c).re =
      (herm (Hpk k r) z z).re * Complex.normSq (c (Sum.inl (Fin.last r))) := by
  have hb : ∀ a b, gramM k r z z' γ (Sum.inl a) (Sum.inl b) = (herm (Hpk k r) z z • ggLastU r) a b :=
    fun a b => ggBlockA k r z hz a b
  simp only [herm, dotProduct, mulVec, Fintype.sum_sum_type, hc, star_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, hb, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last r) (fun a _ ha => by simp [ggLastU, ha]) (by simp)]
  rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by simp [ggLastU, hb]) (by simp)]
  simp [ggLastU, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem positive_count : PosCount := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  let p : Fin (r + 1) ⊕ Fin (r + 1) → Prop := fun i => 0 < hA.eigenvalues i
  let ψ : ({i // p i} → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Sum.inr : Fin (r + 1) → Fin (r + 1) ⊕ Fin (r + 1))).comp
      ((Matrix.mulVecLin (hA.eigenvectorUnitary : Matrix _ _ ℂ)).comp (extZ p))
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hinr : ∀ b, ((hA.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
        (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ extZ p y) (Sum.inr b) = 0 := by
      intro b
      have := congrFun hy b
      simpa [ψ, LinearMap.funLeft_apply] using this
    have h1 := re_diag hA (extZ p y)
    rw [blockA_re k r z z' γ hs.2.1.1 _ hinr] at h1
    have hT : (herm (Hpk k r) z z).re < 0 := by
      have := hs.2.1.2; simp only [Tz] at this; linarith
    have hl : (herm (Hpk k r) z z).re *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
          (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ extZ p y) (Sum.inl (Fin.last r))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hT.le (Complex.normSq_nonneg _)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (r + 1) ⊕ Fin (r + 1))),
        0 ≤ hA.eigenvalues i * Complex.normSq (extZ p y i) := by
      intro i _
      rw [extZ_apply]
      split_ifs with h
      · exact mul_nonneg h.le (Complex.normSq_nonneg _)
      · simp
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
      (le_antisymm (h1 ▸ hl) (Finset.sum_nonneg hnn))
    funext t
    have := hz t.1 (Finset.mem_univ _)
    rw [extZ_apply, dif_pos t.2] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt t.2)
    · simpa [Complex.normSq_eq_zero] using h
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem nonposCount_of (hN : NegBound) : NonposCount := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  let q : Fin (r + 1) ⊕ Fin (r + 1) → Prop := fun i => ¬ 0 < hA.eigenvalues i
  let Φ : ({i // q i} → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.mulVecLin (Vc k r z z' γ)).comp
      ((Matrix.mulVecLin (hA.eigenvectorUnitary : Matrix _ _ ℂ)).comp (extZ q))
  have hΦ : ∀ y, Φ y = Vc k r z z' γ *ᵥ ((hA.eigenvectorUnitary : Matrix _ _ ℂ) *ᵥ extZ q y) :=
    fun y => rfl
  have hre : ∀ y, (herm (Hpk k r) (Φ y) (Φ y)).re ≤ 0 := by
    intro y
    rw [hΦ, herm_Vc, re_diag]
    apply Finset.sum_nonpos
    intro i _
    rw [extZ_apply]
    split_ifs with h
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) (Complex.normSq_nonneg _)
    · simp
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hΦ] at hy
    exact extZ_eq_zero q y (U_eq_zero hA _ (Vc_inj k r z z' γ hdet _ hy))
  have h1 := hN k r (LinearMap.range Φ) (by rintro x ⟨y, rfl⟩; exact hre y)
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

end PI.FrameInd.CountsW
end
end

section
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

noncomputable section
namespace PI.FrameInd.NegB

lemma herm_Pk (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x x = ∑ i, star ((Pk k r *ᵥ x) i) * (dK k r i * (Pk k r *ᵥ x) i) := by
  unfold herm
  rw [← PJP k r, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
  simp only [dotProduct, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dK, Pi.star_apply]

lemma re_herm (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) :
    (herm (Hpk k r) x x).re =
      ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) := by
  rw [herm_Pk, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i.val < r + k <;>
    simp [h, dK, epsK, Complex.mul_re, Complex.normSq_apply, Complex.star_def] <;> ring

lemma Pk_inj (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (h : Pk k r *ᵥ x = 0) : x = 0 := by
  have hA : (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) * Pk k r = 1 := by
    rw [Matrix.mul_assoc, PJP, Hpk_sq]
  calc x = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) *ᵥ x := (Matrix.one_mulVec x).symm
    _ = (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) *ᵥ (Pk k r *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hA]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

def negMap (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (fun a : Fin (r + 1) => (⟨r + k + a.val, by omega⟩ : Fin (2 * r + k + 1)))).comp
    (Matrix.mulVecLin (Pk k r))

lemma eq_zero_of_negMap (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (hx : negMap k r x = 0)
    (hre : (herm (Hpk k r) x x).re ≤ 0) : x = 0 := by
  apply Pk_inj k r x
  have hneg : ∀ i : Fin (2 * r + k + 1), ¬ i.val < r + k → (Pk k r *ᵥ x) i = 0 := by
    intro i hi
    have h1 := congrFun hx ⟨i.val - (r + k), by omega⟩
    simp only [negMap, LinearMap.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
      Pi.zero_apply] at h1
    have h2 : (⟨r + k + (i.val - (r + k)), by omega⟩ : Fin (2 * r + k + 1)) = i := by
      ext
      simp only
      omega
    rw [h2] at h1
    exact h1
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ (if i.val < r + k then (1 : ℝ) else -1) *
      Complex.normSq ((Pk k r *ᵥ x) i) := by
    intro i _
    by_cases h : i.val < r + k
    · rw [if_pos h, one_mul]
      exact Complex.normSq_nonneg _
    · rw [if_neg h, hneg i h, map_zero, mul_zero]
  have hsum := re_herm k r x
  have hzero : ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) = 0 :=
    le_antisymm (hsum ▸ hre) (Finset.sum_nonneg hterm)
  ext i
  by_cases h : i.val < r + k
  · have h1 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)
    rw [if_pos h, one_mul] at h1
    simpa using Complex.normSq_eq_zero.mp h1
  · simpa using hneg i h

theorem negBound (k r : ℕ) (W : Submodule ℂ (Fin (2 * r + k + 1) → ℂ))
    (hW : ∀ x ∈ W, (herm (Hpk k r) x x).re ≤ 0) : Module.finrank ℂ W ≤ r + 1 := by
  have hinj : Function.Injective ((negMap k r).comp W.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : (a : Fin (2 * r + k + 1) → ℂ) = 0 :=
      eq_zero_of_negMap k r a ha (hW a a.2)
    exact Subtype.ext h1
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun] at h
  exact h

end PI.FrameInd.NegB
end
end

section
open Matrix Formalism.QuantumDeterminants

noncomputable section
namespace PI.FrameInd

theorem negative_bound : NegBound := fun k r S hS => NegB.negBound k r S hS

end PI.FrameInd
end
end

section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

lemma submatrix_conj {ι κ : Type*} [Fintype ι] [Fintype κ] (W M : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (W.submatrix id e)ᴴ * M * W.submatrix id e = (Wᴴ * M * W).submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

theorem signStep_of (hP : PosCount) (hN : NonposCount) : SignStep := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  set ev := hA.eigenvalues with hev
  have h1 : Fintype.card {i // 0 < ev i} ≤ r + 1 := hP k r z z' γ hs hp hdet
  have h2 : Fintype.card {i // ¬ 0 < ev i} ≤ r + 1 := hN k r z z' γ hs hp hdet
  have h3 := Fintype.card_subtype_compl (fun i : Fin (r + 1) ⊕ Fin (r + 1) => 0 < ev i)
  have h4 : Fintype.card {i : Fin (r + 1) ⊕ Fin (r + 1) // 0 < ev i} ≤
      Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) := Fintype.card_subtype_le _
  simp only [Fintype.card_sum, Fintype.card_fin] at h3 h4
  have hcP : Fintype.card {i // 0 < ev i} = r + 1 := by omega
  have hcN : Fintype.card {i // ¬ 0 < ev i} = r + 1 := by omega
  have hne : ∀ i, ev i ≠ 0 := by
    intro i h0
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h0]; simp)
  let eP : {i // 0 < ev i} ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcP
  let eN : {i // ¬ 0 < ev i} ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcN
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (r + 1) ⊕ Fin (r + 1) :=
    (Equiv.sumCongr eP.symm eN.symm).trans (Equiv.sumCompl fun i => 0 < ev i)
  let U : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ := hA.eigenvectorUnitary
  let s : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)
  let f : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := fun i => if 0 < ev i then 1 else -1
  have hW : (U * diagonal s)ᴴ * gramM k r z z' γ * (U * diagonal s) = diagonal f := by
    have hd : Uᴴ * gramM k r z z' γ * U = diagonal (fun i => ((ev i : ℝ) : ℂ)) := CountsW.diag_eq hA
    rw [conjTranspose_mul, diagonal_conjTranspose]
    calc (star s |> diagonal) * Uᴴ * gramM k r z z' γ * (U * diagonal s)
        = diagonal (star s) * (Uᴴ * gramM k r z z' γ * U) * diagonal s := by simp only [Matrix.mul_assoc]
      _ = diagonal f := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        have hpos : 0 < |ev i| := abs_pos.2 (hne i)
        have hsq : Real.sqrt |ev i| * Real.sqrt |ev i| = |ev i| := Real.mul_self_sqrt hpos.le
        have hsq0 : Real.sqrt |ev i| ≠ 0 := by positivity
        simp only [s, f, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        have : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = if 0 < ev i then 1 else -1 := by
          rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
          split_ifs with h
          · rw [abs_of_pos h, inv_mul_cancel₀ (hne i)]
          · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hne i)), inv_neg, neg_mul,
              inv_mul_cancel₀ (hne i)]
        rw [this]; split_ifs <;> simp
  have hfe : f ∘ e = Sum.elim (fun _ => 1) (fun _ => -1) := by
    funext i
    rcases i with a | a
    · simp [f, e, Equiv.sumCompl_apply_inl, (eP.symm a).2]
    · simp [f, e, Equiv.sumCompl_apply_inr, (eN.symm a).2]
  have hD : ((U * diagonal s).submatrix id e)ᴴ * gramM k r z z' γ * (U * diagonal s).submatrix id e =
      diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [submatrix_conj, hW, submatrix_diagonal_equiv, hfe]
  refine ⟨(U * diagonal s).submatrix id e, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hD
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at this
    refine (Finset.prod_ne_zero_iff.2 fun i _ => ?_) this.symm
    rcases i with a | a <;> simp
  · rw [hD]
    ext i j
    rcases i with a | a <;> rcases j with b | b <;> simp [diagonal_apply, one_apply] <;> split_ifs <;> simp

theorem signStep : SignStep :=
  signStep_of PI.FrameInd.CountsW.positive_count (PI.FrameInd.CountsW.nonposCount_of negative_bound)

end PI.FrameInd
end
end
