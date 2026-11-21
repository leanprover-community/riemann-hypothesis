import Mathlib
import Formalism.PeriodIntegrals.CntLocalParts
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.CardLeOfNegFamily

section
noncomputable section

namespace PI.CntNotPosW

open Matrix Formalism.BasicNotions Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Form

variable (S : HSpace E)

theorem hl_sub (x y z : S.V) : S.hT (x - y) z = S.hT x z - S.hT y z := by
  simp
theorem hl_add (x y z : S.V) : S.hT (x + y) z = S.hT x z + S.hT y z := by
  simp
theorem hl_smul (c : E) (x z : S.V) : S.hT (c • x) z = star c * S.hT x z := by
  simp [starRingEnd_apply]
theorem hl_sum {ι : Type} (s : Finset ι) (x : ι → S.V) (z : S.V) :
    S.hT (∑ i ∈ s, x i) z = ∑ i ∈ s, S.hT (x i) z := by
  rw [map_sum, LinearMap.sum_apply]
theorem hr_sub (x y z : S.V) : S.hT z (x - y) = S.hT z x - S.hT z y := by
  simp
theorem hr_add (x y z : S.V) : S.hT z (x + y) = S.hT z x + S.hT z y := by
  simp
theorem hr_smul (c : E) (x z : S.V) : S.hT z (c • x) = c * S.hT z x := by
  simp
theorem hr_sum {ι : Type} (s : Finset ι) (x : ι → S.V) (z : S.V) :
    S.hT z (∑ i ∈ s, x i) = ∑ i ∈ s, S.hT z (x i) := by
  exact map_sum (S.hT z) x s
theorem h_swap (x y : S.V) : S.hT y x = star (S.hT x y) := by
  exact (S.herm.eq x y).symm
theorem h_zero_swap {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [h_swap, h, star_zero]

end Form

section Flags

variable {S : HSpace E} {r : ℕ} {T T' : ℕ}

def Pm (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => S.hT (F.e a) (F'.e b)

def ed (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (b : Fin r) : S.V :=
  ∑ c, (Pm F F')⁻¹ c b • F'.e c

def vv (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (a : Fin r) : S.V := F.e a - ed F F' a

def cz (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (b : Fin r) : E := S.hT (ed F F' b) F.z

def zt (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : S.V := F.z - ∑ a, cz F F' a • F.e a

def cz' (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (b : Fin r) : E := S.hT (F.e b) F'.z

def zt' (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : S.V := F'.z - ∑ a, cz' F F' a • ed F F' a

def beta (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : E := S.hT (zt F F') (zt' F F')

def zt2 (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : S.V :=
  zt' F F' + (beta F F' / (T : E)) • zt F F'

variable (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E))

theorem h_e_ed (hP : (Pm F F').det ≠ 0) (a b : Fin r) :
    S.hT (F.e a) (ed F F' b) = if a = b then 1 else 0 := by
  have h1 : Pm F F' * (Pm F F')⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP)
  have h2 := congrFun (congrFun h1 a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  rw [← h2]
  unfold ed
  rw [hr_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hr_smul, mul_comm]
  rfl

theorem h_ed_e (hP : (Pm F F').det ≠ 0) (a b : Fin r) :
    S.hT (ed F F' a) (F.e b) = if a = b then 1 else 0 := by
  rw [h_swap, h_e_ed F F' hP b a]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem h_ed_ed (a b : Fin r) : S.hT (ed F F' a) (ed F F' b) = 0 := by
  simp [ed, hl_sum, hr_sum, hl_smul, hr_smul, F'.e_iso]

theorem h_ed_zp (a : Fin r) : S.hT (ed F F' a) F'.z = 0 := by
  simp [ed, hl_sum, hl_smul, F'.z_orth]

theorem h_zp_ed (a : Fin r) : S.hT F'.z (ed F F' a) = 0 := by
  exact h_zero_swap _ (h_ed_zp F F' a)

theorem h_z_e (a : Fin r) : S.hT F.z (F.e a) = 0 := by
  exact h_zero_swap _ (F.z_orth a)

theorem h_v_v (hP : (Pm F F').det ≠ 0) (a b : Fin r) :
    S.hT (vv F F' a) (vv F F' b) = if a = b then -2 else 0 := by
  unfold vv
  rw [hl_sub, hr_sub, hr_sub, F.e_iso, h_e_ed F F' hP, h_ed_e F F' hP, h_ed_ed]
  split_ifs <;> ring

theorem h_ed_zt (hP : (Pm F F').det ≠ 0) (b : Fin r) : S.hT (ed F F' b) (zt F F') = 0 := by
  unfold zt
  rw [hr_sub, hr_sum]
  simp only [hr_smul, h_ed_e F F' hP]
  simp [cz]

theorem h_e_zt (b : Fin r) : S.hT (F.e b) (zt F F') = 0 := by
  simp [zt, hr_sub, hr_sum, hr_smul, F.z_orth, F.e_iso]

theorem h_zt_zt : S.hT (zt F F') (zt F F') = -(T : E) := by
  have h1 : S.hT (∑ a, cz F F' a • F.e a) (zt F F') = 0 := by
    simp [hl_sum, hl_smul, h_e_zt]
  have h2 : S.hT F.z (zt F F') = -(T : E) := by
    simp [zt, hr_sub, hr_sum, hr_smul, h_z_e, F.z_norm]
  calc S.hT (zt F F') (zt F F')
      = S.hT F.z (zt F F') - S.hT (∑ a, cz F F' a • F.e a) (zt F F') := hl_sub S _ _ _
    _ = -(T : E) := by rw [h1, h2, sub_zero]

theorem h_e_zt' (hP : (Pm F F').det ≠ 0) (b : Fin r) : S.hT (F.e b) (zt' F F') = 0 := by
  unfold zt'
  rw [hr_sub, hr_sum]
  simp only [hr_smul, h_e_ed F F' hP]
  simp [cz']

theorem h_ed_zt' (b : Fin r) : S.hT (ed F F' b) (zt' F F') = 0 := by
  simp [zt', hr_sub, hr_sum, hr_smul, h_ed_zp, h_ed_ed]

theorem h_zt'_zt' : S.hT (zt' F F') (zt' F F') = -(T' : E) := by
  have h1 : S.hT (∑ a, cz' F F' a • ed F F' a) (zt' F F') = 0 := by
    simp [hl_sum, hl_smul, h_ed_zt']
  have h2 : S.hT F'.z (zt' F F') = -(T' : E) := by
    simp [zt', hr_sub, hr_sum, hr_smul, h_zp_ed, F'.z_norm]
  calc S.hT (zt' F F') (zt' F F')
      = S.hT F'.z (zt' F F') - S.hT (∑ a, cz' F F' a • ed F F' a) (zt' F F') := hl_sub S _ _ _
    _ = -(T' : E) := by rw [h1, h2, sub_zero]

theorem h_v_zt (hP : (Pm F F').det ≠ 0) (a : Fin r) : S.hT (vv F F' a) (zt F F') = 0 := by
  simp [vv, hl_sub, h_e_zt, h_ed_zt F F' hP]

theorem h_v_zt' (hP : (Pm F F').det ≠ 0) (a : Fin r) : S.hT (vv F F' a) (zt' F F') = 0 := by
  simp [vv, hl_sub, h_e_zt' F F' hP, h_ed_zt']

theorem hermForm_anisotropic_orth_second (hT : (T : E) ≠ 0) : S.hT (zt F F') (zt2 F F') = 0 := by
  unfold zt2
  rw [hr_add, hr_smul, h_zt_zt]
  have h1 : beta F F' / (T : E) * -(T : E) = -beta F F' := by
    rw [mul_neg, div_mul_cancel₀ _ hT]
  rw [h1]
  simp [beta]

theorem hermForm_vector_orth_second (hP : (Pm F F').det ≠ 0) (a : Fin r) : S.hT (vv F F' a) (zt2 F F') = 0 := by
  simp [zt2, hr_add, hr_smul, h_v_zt F F' hP, h_v_zt' F F' hP]

theorem hermForm_second_anisotropic (hT : (T : E) ≠ 0) :
    S.hT (zt2 F F') (zt2 F F') = -(T' : E) + beta F F' * star (beta F F') / (T : E) := by
  have hb : S.hT (zt' F F') (zt F F') = star (beta F F') := h_swap S (zt F F') (zt' F F')
  have hb' : S.hT (zt F F') (zt' F F') = beta F F' := rfl
  unfold zt2
  rw [hl_add, hl_smul, hr_add, hr_add, hr_smul, hr_smul, h_zt'_zt', h_zt_zt, hb, hb',
    star_div₀, star_natCast]
  field_simp
  ring

theorem zp_eq : F'.z = zt' F F' + ∑ c, (∑ a, cz' F F' a * (Pm F F')⁻¹ c a) • F'.e c := by
  have hX : ∑ a, cz' F F' a • ed F F' a
      = ∑ c, (∑ a, cz' F F' a * (Pm F F')⁻¹ c a) • F'.e c := by
    simp only [ed, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  show F'.z = (F'.z - ∑ a, cz' F F' a • ed F F' a) + _
  rw [hX, sub_add_cancel]

end Flags

end PI.CntNotPosW
end
end

section
noncomputable section

namespace PI.CntNotPosW

open Matrix Formalism.BasicNotions Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {S : HSpace E} {r : ℕ} {T T' : ℕ}

theorem zhat_apply (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (a b : Fin (r + 1)) :
    Zhat F F' a b = S.hT (F.fvec a) (F'.fvec b) := rfl

theorem lead_r (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) :
    leadMinorE (Zhat F F') r = (Pm F F').det := by
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ r)]
  congr 1
  ext a b
  have hc : ∀ x : Fin r, Fin.castLE (Nat.le_succ r) x = Fin.castSucc x := fun x => Fin.ext rfl
  simp only [Matrix.submatrix_apply, hc, zhat_apply, FlagG.fvec, Fin.snoc_castSucc, Pm, Matrix.of_apply]

theorem leadingMinor_full_eq_det (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) :
    leadMinorE (Zhat F F') (r + 1) = (Zhat F F').det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  rfl

def kk (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (c : Fin r) : E :=
  ∑ a, cz' F F' a * (Pm F F')⁻¹ c a

def Um (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun c b => if b = Fin.last r then Fin.snoc (α := fun _ => E) (kk F F') 1 c
    else if c = b then 1 else 0

def gv (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : Fin (r + 1) → S.V :=
  Fin.snoc (α := fun _ => S.V) F'.e (zt' F F')

theorem fvec_eq (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (b : Fin (r + 1)) :
    F'.fvec b = ∑ c, Um F F' c b • gv F F' c := by
  induction b using Fin.lastCases with
  | last =>
    rw [Fin.sum_univ_castSucc]
    simp only [Um, Matrix.of_apply, if_pos rfl, Fin.snoc_castSucc, Fin.snoc_last, gv, FlagG.fvec,
      one_smul]
    rw [zp_eq F F', add_comm]
    simp [kk]
  | cast b =>
    simp only [Um, Matrix.of_apply, FlagG.fvec, Fin.snoc_castSucc, if_neg (Fin.castSucc_ne_last b),
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, gv]

theorem zhat_eq_mul (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) :
    Zhat F F' = (Matrix.of fun a b => S.hT (F.fvec a) (gv F F' b)) * Um F F' := by
  ext a b
  rw [zhat_apply, fvec_eq F F' b, hr_sum]
  simp only [hr_smul, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem det_Um (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : (Um F F').det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases h : i = Fin.last r
    · subst h; simp [Um]
    · simp [Um, h]
  · intro i j hij
    have hj : j ≠ Fin.last r := by
      rintro rfl
      exact absurd hij (not_lt.2 (Fin.le_last i))
    have hij' : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    simp [Um, hj, hij']

theorem det_Zt (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (hP : (Pm F F').det ≠ 0) :
    (Matrix.of fun a b => S.hT (F.fvec a) (gv F F' b)).det = beta F F' * (Pm F F').det := by
  have hsub : (Matrix.of fun a b => S.hT (F.fvec a) (gv F F' b)).submatrix (Fin.last r).succAbove
      (Fin.last r).succAbove = Pm F F' := by
    ext a b
    simp [Fin.succAbove_last, gv, FlagG.fvec, Pm]
  have hlast : S.hT (F.fvec (Fin.last r)) (gv F F' (Fin.last r)) = beta F F' := by
    simp only [FlagG.fvec, gv, Fin.snoc_last, beta, zt, hl_sub, hl_sum, hl_smul, h_e_zt' F F' hP,
      mul_zero, Finset.sum_const_zero, sub_zero]
  rw [Matrix.det_succ_column _ (Fin.last r), Fintype.sum_eq_single (Fin.last r)]
  · rw [hsub, Matrix.of_apply, hlast, Fin.val_last]
    have hpow : ((-1 : E) ^ (r + r)) = 1 := by rw [← two_mul, pow_mul]; simp
    rw [hpow, one_mul]
  · intro i hi
    obtain ⟨i0, rfl⟩ := Fin.exists_castSucc_eq.2 hi
    simp [gv, FlagG.fvec, h_e_zt' F F' hP]

theorem leadingMinor_full_eq_prod (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (hP : (Pm F F').det ≠ 0) :
    leadMinorE (Zhat F F') (r + 1) = beta F F' * (Pm F F').det := by
  rw [leadingMinor_full_eq_det, zhat_eq_mul, Matrix.det_mul, det_Um, mul_one, det_Zt F F' hP]

theorem gflag_pos (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {p' q' : ℕ}
    (hS : Formalism.UG.HasSignature (S.gram.map τ) p' q') (hq : q' = r + 1) (hG : Gflag F F' ≠ 0) :
    0 < (τ (Gflag F F')).re := by
  have hns : ∀ x : E, τ x * τ (star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
    intro x; rw [hτ, Complex.mul_conj]
  have hGf : Gflag F F' = leadMinorE (Zhat F F') (r + 1) * star (leadMinorE (Zhat F F') (r + 1)) -
      (T : E) * (T' : E) * (leadMinorE (Zhat F F') r * star (leadMinorE (Zhat F F') r)) := rfl
  set D1 := leadMinorE (Zhat F F') (r + 1) with hD1
  set D0 := leadMinorE (Zhat F F') r with hD0
  set R : ℝ := Complex.normSq (τ D1) - (T : ℝ) * T' * Complex.normSq (τ D0) with hR
  have hτG : τ (Gflag F F') = (R : ℂ) := by
    rw [hGf, map_sub, map_mul, map_mul, map_mul, map_mul, hns, hns, map_natCast, map_natCast, hR]
    push_cast
    ring
  rw [hτG, Complex.ofReal_re]
  by_contra hle
  push Not at hle
  have hne : R ≠ 0 := by
    intro h0
    apply hG
    apply τ.injective
    rw [hτG, h0, map_zero, Complex.ofReal_zero]
  have hlt : R < 0 := lt_of_le_of_ne hle hne
  by_cases hP : (Pm F F').det = 0
  · have : D0 = 0 := by rw [hD0, lead_r, hP]
    rw [hR, this, map_zero, Complex.normSq_zero, mul_zero, sub_zero] at hlt
    exact absurd hlt (not_lt.2 (Complex.normSq_nonneg _))
  · have hD1e : D1 = beta F F' * D0 := by rw [hD1, leadingMinor_full_eq_prod F F' hP, hD0, lead_r]
    have hD0ne : τ D0 ≠ 0 := by
      rw [hD0, lead_r, map_ne_zero]
      exact hP
    have hpos0 : 0 < Complex.normSq (τ D0) := Complex.normSq_pos.2 hD0ne
    set nb := Complex.normSq (τ (beta F F')) with hnb
    have hRe : R = Complex.normSq (τ D0) * (nb - (T : ℝ) * T') := by
      rw [hR, hD1e, map_mul, Complex.normSq_mul, hnb]
      ring
    have hbT : nb < (T : ℝ) * T' := by
      rw [hRe] at hlt
      by_contra h
      push Not at h
      have : 0 ≤ Complex.normSq (τ D0) * (nb - (T : ℝ) * T') :=
        mul_nonneg hpos0.le (by linarith)
      linarith
    have hnb0 : 0 ≤ nb := Complex.normSq_nonneg _
    have hTpos : (0 : ℝ) < T := by
      rcases Nat.eq_zero_or_pos T with h | h
      · rw [h] at hbT; simp at hbT; linarith
      · exact_mod_cast h
    have hTE : (T : E) ≠ 0 := by
      have : T ≠ 0 := by exact_mod_cast hTpos.ne'
      exact_mod_cast this
    let w : Fin r ⊕ Bool → S.V := Sum.elim (vv F F') (fun b => if b then zt2 F F' else zt F F')
    let d : Fin r ⊕ Bool → ℝ := Sum.elim (fun _ => -2) (fun b => if b then -(T' : ℝ) + nb / T else -(T : ℝ))
    have hoff : ∀ i j, i ≠ j → S.hT (w i) (w j) = 0 := by
      intro i j hij
      rcases i with a | bi <;> rcases j with b | bj
      · have hab : a ≠ b := fun h => hij (by rw [h])
        simp only [w, Sum.elim_inl, h_v_v F F' hP, if_neg hab]
      · cases bj
        · simp only [w, Sum.elim_inl, Sum.elim_inr]; exact h_v_zt F F' hP a
        · simp only [w, Sum.elim_inl, Sum.elim_inr]; exact hermForm_vector_orth_second F F' hP a
      · cases bi
        · simp only [w, Sum.elim_inl, Sum.elim_inr]; exact h_zero_swap S (h_v_zt F F' hP b)
        · simp only [w, Sum.elim_inl, Sum.elim_inr]; exact h_zero_swap S (hermForm_vector_orth_second F F' hP b)
      · cases bi <;> cases bj
        · exact absurd rfl hij
        · simp only [w, Sum.elim_inr]; exact hermForm_anisotropic_orth_second F F' hTE
        · simp only [w, Sum.elim_inr]; exact h_zero_swap S (hermForm_anisotropic_orth_second F F' hTE)
        · exact absurd rfl hij
    have hdiag : ∀ i, τ (S.hT (w i) (w i)) = (d i : ℂ) := by
      intro i
      rcases i with a | b
      · simp only [w, d, Sum.elim_inl, h_v_v F F' hP, ↓reduceIte, map_neg]
        rw [show (2 : E) = ((2 : ℕ) : E) by norm_num, map_natCast]
        norm_num
      · cases b
        · simp only [w, d, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]
          rw [h_zt_zt]
          simp
        · simp only [w, d, Sum.elim_inr, ↓reduceIte]
          rw [hermForm_second_anisotropic F F' hTE, map_add, map_div₀, map_mul, hns, map_neg, map_natCast, map_natCast, hnb]
          push_cast
          ring
    have hneg : ∀ i, d i < 0 := by
      intro i
      rcases i with a | b
      · simp [d]
      · cases b
        · simp only [d, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte]; linarith
        · simp only [d, Sum.elim_inr, ↓reduceIte]
          have : nb / T < T' := by
            rw [div_lt_iff₀ hTpos]; linarith
          linarith
    have hc := card_le_of_negFamily S τ hτ hS w d hoff hdiag hneg
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
    omega

end PI.CntNotPosW
end
end

section
noncomputable section

namespace PI.CntNotPosW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem totPos_of_flags (D : Formalism.BasicNotions.D7) {T T' : ℕ} (F : FlagG (VS D) D.R.rS (T : D.host.E))
    (F' : FlagG (VS D) D.R.rS (T' : D.host.E)) (hG : Gflag F F' ≠ 0) : TotPos (Gflag F F') := by
  unfold TotPos
  intro τ
  haveI := D.host.isCMField_hostE
  refine gflag_pos (p' := ((VS D).sig (embS D τ)).1) (q' := ((VS D).sig (embS D τ)).2) F F' (embS D τ)
    (fun a => NumberField.IsCMField.complexEmbedding_complexConj _ (embS D τ) a) (D.sp.Y_sig 0 (embS D τ)) ?_ hG
  rw [D.sp.baseSpace_signature_eq]
  rfl


end PI.CntNotPosW
end
end
