import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRDrTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRModelV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRealInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPConseq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPCommPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPContPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRealInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepAPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatPolyOK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvFinal

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JDBeta

open Formalism.FourierDecayAlt.P.CutMP Matrix

noncomputable section

variable {k r : ℕ}

def ptv (k r : ℕ) (t : Fin (k + 1)) (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if q.val < r then r + k + 1 + q.val else if q.val = r then r + t.val
    else if q.val - r - 1 < r + t.val then q.val - r - 1 else q.val - r, by
    have := q.isLt; have := t.isLt; split_ifs <;> omega⟩

theorem ptv_inj (t : Fin (k + 1)) : Function.Injective (ptv k r t) := by
  intro q₁ q₂ h
  have h' := congrArg Fin.val h
  simp only [ptv] at h'
  apply Fin.ext
  have := q₁.isLt; have := q₂.isLt
  split_ifs at h' <;> omega

def Pt (k r : ℕ) (t : Fin (k + 1)) : Equiv.Perm (Fin (2 * r + k + 1)) :=
  Equiv.ofBijective (ptv k r t) (Finite.injective_iff_bijective.1 (ptv_inj t))

theorem Pt_apply (t : Fin (k + 1)) (q : Fin (2 * r + k + 1)) : Pt k r t q = ptv k r t q := rfl

theorem Pt_succ (t : ℕ) (ht : t + 1 < k + 1) :
    Pt k r ⟨t + 1, ht⟩ = Pt k r ⟨t, by omega⟩ *
      Equiv.swap (⟨r, by omega⟩ : Fin (2 * r + k + 1)) ⟨2 * r + 1 + t, by omega⟩ := by
  ext q
  simp only [Equiv.Perm.mul_apply, Pt_apply, Equiv.swap_apply_def]
  have := q.isLt
  split_ifs with h1 h2
  · subst h1; simp only [ptv]; split_ifs <;> omega
  · subst h2; simp only [ptv]; split_ifs <;> omega
  · have e1 : q.val ≠ r := fun e => h1 (Fin.ext e)
    have e2 : q.val ≠ 2 * r + 1 + t := fun e => h2 (Fin.ext e)
    simp only [ptv]
    split_ifs <;> omega

theorem sign_Pt (t : ℕ) (ht : t < k + 1) :
    (Equiv.Perm.sign (Pt k r ⟨t, ht⟩) : ℤ) = (-1) ^ t * (Equiv.Perm.sign (Pt k r 0) : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Pt_succ t ht, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by simp [Fin.ext_iff]; omega), Units.val_mul,
      ih (by omega), pow_succ]
    simp only [Units.val_neg, Units.val_one]
    ring

theorem rowsR_val (t : Fin (k + 1)) (j : Fin (r + k)) :
    (rowsR k r t j).val = if j.val < r + t.val then j.val else j.val + 1 := rfl

theorem rowsR_strictMono (t : Fin (k + 1)) : StrictMono (rowsR k r t) := by
  intro j₁ j₂ h
  rw [Fin.lt_def, rowsR_val, rowsR_val]
  rw [Fin.lt_def] at h
  split_ifs <;> omega

theorem residue_rows_injective {t t' : Fin (k + 1)} (h : rowsR k r t = rowsR k r t') : t = t' := by
  by_contra hne
  rcases lt_or_gt_of_ne (fun e => hne (Fin.ext e) : t.val ≠ t'.val) with hl | hl
  · have := congrArg Fin.val (congrFun h ⟨r + t.val, by have := t'.isLt; omega⟩)
    simp only [rowsR_val, Fin.val_mk] at this
    split_ifs at this <;> omega
  · have := congrArg Fin.val (congrFun h ⟨r + t'.val, by have := t.isLt; omega⟩)
    simp only [rowsR_val, Fin.val_mk] at this
    split_ifs at this <;> omega

theorem rowsR_mem (t : Fin (k + 1)) : rowsR k r t ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert rowsR_strictMono t

section det

variable (z : Fin (2 * r + k + 1) → ℂ) (x : Q.Mx k r) (v : Fin r → ℂ)
  (h1 : ∀ a : Fin r, ginvH k r x *ᵥ bvec (eI k r a) = v a • bvec (esI k r a))
  (h2 : ∀ p : Fin (2 * r + k + 1), p.val < r → (ginvH k r x *ᵥ z) p = 0)
include h1

theorem colR_lt (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) (hq : q.val < r) :
    colR k r z x J q p = if p.val = r + k + 1 + q.val then v ⟨r - 1 - q.val, by omega⟩ else 0 := by
  unfold colR
  rw [dif_pos hq, h1]
  simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  simp only [esI, Fin.ext_iff]
  apply propext
  constructor <;> intro h <;> omega

omit h1 in
theorem colR_eq (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) (hq : q.val = r) :
    colR k r z x J q p = (ginvH k r x *ᵥ z) p := by
  unfold colR
  rw [dif_neg (by omega), dif_pos hq]

omit h1 in
theorem colR_gt (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) (hq : r < q.val) :
    colR k r z x J q p = if p = J ⟨q.val - r - 1, by have := q.isLt; omega⟩ then 1 else 0 := by
  unfold colR
  rw [dif_neg (by omega), dif_neg (by omega)]
  simp only [bvec, Pi.single_apply]

include h2

theorem claimA (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) (σ : Equiv.Perm (Fin (2 * r + k + 1)))
    (hσ : ∏ i, colR k r z x J i (σ i) ≠ 0) : ∃ t, J = rowsR k r t ∧ σ = Pt k r t := by
  classical
  have hne : ∀ i, colR k r z x J i (σ i) ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hσ i (Finset.mem_univ _)
  have hlt : ∀ q : Fin (2 * r + k + 1), q.val < r → (σ q).val = r + k + 1 + q.val := by
    intro q hq
    have := hne q
    rw [colR_lt z x v h1 J q _ hq] at this
    by_contra h
    exact this (if_neg h)
  have hgt : ∀ (q : Fin (2 * r + k + 1)) (hq : r < q.val), σ q = J ⟨q.val - r - 1, by have := q.isLt; omega⟩ := by
    intro q hq
    have := hne q
    rw [colR_gt z x J q _ hq] at this
    by_contra h
    exact this (if_neg h)
  have hr0 : r ≤ (σ ⟨r, by omega⟩).val := by
    by_contra h
    have := hne ⟨r, by omega⟩
    rw [colR_eq z x J _ _ rfl, h2 _ (by omega)] at this
    exact this rfl
  have hstar : ∀ (p : Fin (2 * r + k + 1)) (q : Fin (2 * r + k + 1)), r < q.val → r + k < (σ q).val → False := by
    intro p q hq hs
    have hq' : (σ q).val - r - k - 1 < r := by have := (σ q).isLt; omega
    have e := hlt ⟨(σ q).val - r - k - 1, by omega⟩ hq'
    have : σ ⟨(σ q).val - r - k - 1, by omega⟩ = σ q := Fin.ext (by simp only at e; omega)
    have := congrArg Fin.val (σ.injective this)
    simp only at this
    omega
  have hr1 : (σ ⟨r, by omega⟩).val ≤ r + k := by
    by_contra h
    have hq' : (σ ⟨r, by omega⟩).val - r - k - 1 < r := by have := (σ ⟨r, by omega⟩).isLt; omega
    have e := hlt ⟨(σ ⟨r, by omega⟩).val - r - k - 1, by omega⟩ hq'
    have : σ ⟨(σ ⟨r, by omega⟩).val - r - k - 1, by omega⟩ = σ ⟨r, by omega⟩ := Fin.ext (by simp only at e; omega)
    have := congrArg Fin.val (σ.injective this)
    simp only at this
    omega
  set t : Fin (k + 1) := ⟨(σ ⟨r, by omega⟩).val - r, by omega⟩ with ht
  have hJS : ∀ j : Fin (r + k), (J j).val ≤ r + k ∧ (J j).val ≠ r + t.val := by
    intro j
    have e := hgt ⟨r + 1 + j.val, by have := j.isLt; omega⟩ (by simp only; omega)
    have ej : (⟨(r + 1 + j.val) - r - 1, by have := j.isLt; omega⟩ : Fin (r + k)) = j := Fin.ext (by simp only; omega)
    rw [ej] at e
    rw [← e]
    constructor
    · by_contra h
      exact hstar 0 ⟨r + 1 + j.val, by have := j.isLt; omega⟩ (by show r < r + 1 + j.val; omega) (by omega)
    · intro h
      have : σ ⟨r + 1 + j.val, by have := j.isLt; omega⟩ = σ ⟨r, by omega⟩ := Fin.ext (by rw [h, ht]; simp only; omega)
      have := congrArg Fin.val (σ.injective this)
      simp only at this
      omega
  let S : Finset (Fin (2 * r + k + 1)) := Finset.univ.filter fun p => p.val ≤ r + k ∧ p.val ≠ r + t.val
  have hSimg : S = Finset.univ.image (rowsR k r t) := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1', h2'⟩
      refine ⟨⟨if p.val < r + t.val then p.val else p.val - 1, by have := t.isLt; split_ifs <;> omega⟩, ?_⟩
      apply Fin.ext
      rw [rowsR_val]
      simp only
      split_ifs <;> omega
    · rintro ⟨j, rfl⟩
      rw [rowsR_val]
      have := j.isLt
      split_ifs <;> omega
  have hcard : S.card = r + k := by
    rw [hSimg, Finset.card_image_of_injective _ (rowsR_strictMono t).injective, Finset.card_univ, Fintype.card_fin]
  have hJeq : J = rowsR k r t := by
    have e1 := Finset.orderEmbOfFin_unique hcard (f := J) (fun j => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hJS j) hJ
    have e2 := Finset.orderEmbOfFin_unique hcard (f := rowsR k r t) (fun j => by
      rw [hSimg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)) (rowsR_strictMono t)
    rw [e1, e2]
  refine ⟨t, hJeq, ?_⟩
  ext q
  rw [Pt_apply]
  simp only [ptv]
  rcases lt_trichotomy q.val r with hq | hq | hq
  · rw [hlt q hq, if_pos hq]
  · have htv : t.val = (σ ⟨r, by omega⟩).val - r := by rw [ht]
    have e : q = ⟨r, by omega⟩ := Fin.ext hq
    rw [if_neg (by omega), if_pos hq, e]
    omega
  · rw [hgt q hq, hJeq, rowsR_val]
    simp only [Fin.val_mk]
    split_ifs <;> omega

end det

section det2

variable (z : Fin (2 * r + k + 1) → ℂ) (x : Q.Mx k r) (v : Fin r → ℂ)
  (h1 : ∀ a : Fin r, ginvH k r x *ᵥ bvec (eI k r a) = v a • bvec (esI k r a))
  (h2 : ∀ p : Fin (2 * r + k + 1), p.val < r → (ginvH k r x *ᵥ z) p = 0)
omit h1 in
theorem prod_rev_v : (∏ i : Fin (2 * r + k + 1), (if h : i.val < r then v ⟨r - 1 - i.val, by omega⟩ else 1)) =
    ∏ a, v a := by
  let F : ℕ → ℂ := fun i => if h : i < r then v ⟨r - 1 - i, by omega⟩ else 1
  have e1 : (∏ i : Fin (2 * r + k + 1), (if h : i.val < r then v ⟨r - 1 - i.val, by omega⟩ else 1)) =
      ∏ i ∈ Finset.range (2 * r + k + 1), F i := Fin.prod_univ_eq_prod_range F _
  rw [e1, ← Finset.prod_range_mul_prod_Ico F (show r ≤ 2 * r + k + 1 by omega)]
  rw [Finset.prod_eq_one (s := Finset.Ico r (2 * r + k + 1)) (fun i hi => by
    simp only [F]; rw [dif_neg (by simp [Finset.mem_Ico] at hi; omega)]), mul_one]
  rw [← Fin.prod_univ_eq_prod_range F r]
  rw [← Equiv.prod_comp Fin.revPerm v]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [F, dif_pos a.isLt, Fin.revPerm_apply]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev]
  omega

include h1 in
theorem claimB (t : Fin (k + 1)) :
    ∏ i, colR k r z x (rowsR k r t) i (Pt k r t i) = (∏ a, v a) * (ginvH k r x *ᵥ z) (wI k r t) := by
  have hf : ∀ i, colR k r z x (rowsR k r t) i (Pt k r t i) =
      (if h : i.val < r then v ⟨r - 1 - i.val, by omega⟩ else 1) *
        (if i = ⟨r, by omega⟩ then (ginvH k r x *ᵥ z) (wI k r t) else 1) := by
    intro i
    rcases lt_trichotomy i.val r with hi | hi | hi
    · rw [colR_lt z x v h1 _ i _ hi, if_pos (by rw [Pt_apply]; simp only [ptv]; rw [if_pos hi]), dif_pos hi,
        if_neg (fun e => by rw [e] at hi; simp at hi), mul_one]
    · have e : i = ⟨r, by omega⟩ := Fin.ext hi
      rw [colR_eq z x _ i _ hi, dif_neg (by omega), if_pos e, one_mul]
      congr 1
      apply Fin.ext
      rw [Pt_apply]
      simp only [ptv, wI]
      rw [if_neg (by omega), if_pos hi]
    · have hP : Pt k r t i = rowsR k r t ⟨i.val - r - 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        rw [Pt_apply, rowsR_val]
        simp only [ptv, Fin.val_mk]
        split_ifs <;> omega
      have hne : i ≠ ⟨r, by omega⟩ := fun e => by rw [e] at hi; simp at hi
      rw [colR_gt z x _ i _ hi, if_pos hP, dif_neg (by omega), if_neg hne, mul_one]
  rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib, prod_rev_v (k := k) v,
    Finset.prod_eq_single (⟨r, by omega⟩ : Fin (2 * r + k + 1)) (fun b _ hb => if_neg hb) (by simp), if_pos rfl]

include h1 h2 in
theorem det_formula (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) :
    beJ k r z x J = ∑ t : Fin (k + 1), if J = rowsR k r t then
      ((Equiv.Perm.sign (Pt k r t) : ℤ) : ℂ) * (∏ a, v a) * (ginvH k r x *ᵥ z) (wI k r t) else 0 := by
  unfold beJ
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply]
  by_cases hex : ∃ t, J = rowsR k r t
  · obtain ⟨t₀, rfl⟩ := hex
    rw [Finset.sum_eq_single t₀ (fun t _ ht => if_neg (fun e => ht (residue_rows_injective e).symm)) (by simp), if_pos rfl]
    rw [Finset.sum_eq_single (Pt k r t₀) (fun σ _ hσ => ?_) (by simp)]
    · rw [claimB z x v h1 t₀, Units.smul_def, zsmul_eq_mul]
      ring
    · by_contra hne
      have hp : ∏ i, colR k r z x (rowsR k r t₀) i (σ i) ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
      obtain ⟨t, ht, hσt⟩ := claimA z x v h1 h2 _ (rowsR_strictMono t₀) σ hp
      exact hσ (by rw [hσt, ← residue_rows_injective ht])
  · rw [Finset.sum_eq_zero (fun t _ => if_neg (fun e => hex ⟨t, e⟩))]
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_contra hne
    have hp : ∏ i, colR k r z x J i (σ i) ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
    obtain ⟨t, ht, -⟩ := claimA z x v h1 h2 J hJ σ hp
    exact hex ⟨t, ht⟩

end det2

section pt

theorem hpk_mulVec_eI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (eI k r a) = w (esI k r a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (esI k r a)]
  · have : Hpk k r (eI k r a) (esI k r a) = 1 := by
      have := a.isLt
      unfold Hpk
      simp only [eI, esI]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp_all [Fin.ext_iff] <;> omega)
    rw [this, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * r + k - a.val := fun e => hj (Fin.ext (by simp only [esI]; omega))
    have : Hpk k r (eI k r a) j = 0 := by
      have := a.isLt; have := j.isLt
      unfold Hpk
      simp only [eI]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp_all [Fin.ext_iff] <;> omega)
    rw [this, zero_mul]
  · simp

variable {c : Fin r → ℂ} {g : Q.Mx k r}

theorem x_glev0 (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) :
    Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)

theorem ginvH_mul (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) :
    ginvH k r (Q.wCell k r (Fin.last r) c * g) * (Q.wCell k r (Fin.last r) c * g) = 1 := by
  have hU := (x_glev0 hc hg).1
  unfold UH at hU
  simp only [Set.mem_setOf_eq] at hU
  unfold ginvH
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Hpk k r), hU, GBasic.Hpk_sq]

theorem x_esI (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) :
    (Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (esI k r a) = (star (c a))⁻¹ • bvec (eI k r a) := by
  rw [← Matrix.mulVec_mulVec, (hg.2 a (by simp)).2, Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  funext i
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
  unfold bigCell
  have ha := a.isLt
  rw [dif_neg (by simp [esI]; omega), dif_neg (by simp [esI]; omega)]
  by_cases hi : i = eI k r a
  · subst hi
    rw [if_pos (by simp [eI, esI]; omega), if_pos rfl]
    congr 2
    exact congrArg c (Fin.ext (by simp only [esI]; omega))
  · rw [if_neg (fun e => hi (Fin.ext (by simp [eI, esI] at e ⊢; omega))), if_neg hi]

theorem ginvH_wCell_last_mul_mulVec_bvec_eI (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) :
    ginvH k r (Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (eI k r a) = star (c a) • bvec (esI k r a) := by
  have hca : star (c a) ≠ 0 := star_ne_zero.2 (hc a)
  have e : bvec (eI k r a) = (Q.wCell k r (Fin.last r) c * g) *ᵥ (star (c a) • bvec (esI k r a)) := by
    rw [Matrix.mulVec_smul, x_esI hg a, smul_smul, mul_inv_cancel₀ hca, one_smul]
  rw [e, Matrix.mulVec_mulVec, ginvH_mul hc hg, Matrix.one_mulVec]

theorem ginvH_wCell_mul_apply_eq_zero (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hg : g ∈ Q.Glev k r (Fin.last r))
    (p : Fin (2 * r + k + 1)) (hp : p.val < r) :
    (ginvH k r (Q.wCell k r (Fin.last r) c * g) *ᵥ z) p = 0 := by
  have ep : p = eI k r ⟨p.val, hp⟩ := Fin.ext rfl
  rw [ep]
  unfold ginvH
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hpk_mulVec_eI]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  have hcol : ∀ j, (Q.wCell k r (Fin.last r) c * g) j (esI k r ⟨p.val, hp⟩) =
      ((star (c ⟨p.val, hp⟩))⁻¹ • bvec (eI k r ⟨p.val, hp⟩)) j := by
    intro j
    rw [← x_esI hg]
    simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  simp only [hcol, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have := hpk_mulVec_eI (k := k) ⟨p.val, hp⟩ z
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Finset.sum_eq_single (eI k r ⟨p.val, hp⟩) (fun b _ hb => by rw [if_neg hb, star_zero, zero_mul]) (by simp),
    if_pos rfl, this, hz (esI k r ⟨p.val, hp⟩) (Or.inr (by simp only [esI]; omega)), mul_zero]

end pt

theorem qm_cast {m m' : ℕ} (h : m = m') (a b : Fin m → Fin (2 * r + k + 1)) (u : ℂ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) :
    qminorOp (Q.EH k r) a b u f = qminorOp (Q.EH k r) (a ∘ Fin.cast h.symm) (b ∘ Fin.cast h.symm) u f := by
  subst h
  rfl

theorem qm_rowsN (i t : Fin (k + 1)) (u : ℂ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Q.Mx k r → E) :
    qminorOp (Q.EH k r) (rowsR k r i) (rowsR k r t) u f = qminorOp (Q.EH k r) (rowsN k r 0 i) (rowsN k r 0 t) u f := by
  have h : r + k = r - (0 : Fin (r + 1)).val + k := by simp
  have e : ∀ s : Fin (k + 1), rowsN k r 0 s = rowsR k r s ∘ Fin.cast h.symm := by
    intro s
    funext j
    apply Fin.ext
    simp only [rowsN, Function.comp_apply, rowsR_val]
    simp
    rfl
  rw [qm_cast h, e i, e t]

theorem residue_beta_holds : JDRBeta := by
  intro k r
  refine ⟨((Equiv.Perm.sign (Pt k r 0) : ℤ) : ℂ), by simp, ?_⟩
  intro E _ _ z z' Y f hz c hc g hg
  have h1 := ginvH_wCell_last_mul_mulVec_bvec_eI hc hg
  have h2 := ginvH_wCell_mul_apply_eq_zero (c := c) z hz hg
  have hinv : (Q.wCell k r (Fin.last r) c * g)⁻¹ = ginvH k r (Q.wCell k r (Fin.last r) c * g) :=
    Matrix.inv_eq_left_inv (ginvH_mul hc hg)
  unfold rhatOp NL
  rw [hinv, Finset.smul_sum]
  have hL : ∀ i : Fin (k + 1), (∑ J ∈ jSetR k r,
      (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z (Q.wCell k r (Fin.last r) c * g) J) •
        qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) f (Q.wCell k r (Fin.last r) c * g)) =
      ∑ t : Fin (k + 1), (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' *
        (((Equiv.Perm.sign (Pt k r t) : ℤ) : ℂ) * (∏ a, star (c a)) *
          (ginvH k r (Q.wCell k r (Fin.last r) c * g) *ᵥ z) (wI k r t))) •
        qminorOp (Q.EH k r) (rowsR k r i) (rowsR k r t) (Q.uC k r 0 Y) f (Q.wCell k r (Fin.last r) c * g) := by
    intro i
    classical
    rw [Finset.sum_congr rfl (fun J hJ => by
      rw [det_formula z _ (fun a => star (c a)) h1 h2 J (by
        simp only [jSetR, Finset.mem_filter] at hJ; convert hJ.2)])]
    simp only [Finset.mul_sum, Finset.sum_smul, mul_ite, mul_zero, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq' (jSetR k r) (rowsR k r t), if_pos (rowsR_mem t)]
  rw [Finset.sum_congr rfl fun i _ => hL i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_smul]
  have hs := sign_Pt (k := k) (r := r) t.val t.isLt
  simp only [Fin.eta] at hs
  have hp : (∏ a, star (c a)) = starRingEnd ℂ (∏ a, c a) := by
    rw [map_prod]; rfl
  rw [qm_rowsN]
  congr 1
  rw [hs, hp]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.JDBeta
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section pbop

variable {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem vcq_pbOp_loc (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (hev : f₁ =ᶠ[nhds c] f₂) :
    pbOp l f₁ c = pbOp l f₂ c := by
  simp only [pbOp, wirtBar, hev.fderiv_eq]

theorem vcq_pbOp_neg (l : Fin r) {f : (Fin r → ℂ) → X} {c : Fin r → ℂ} : pbOp l (fun c' => -f c') c = -pbOp l f c := by
  have e : (fun c' => -f c') = -f := rfl
  simp only [pbOp, wirtBar]
  split_ifs
  · rw [e, fderiv_neg]
    simp only [neg_apply]
    module
  · simp

theorem vcq_pbOp_neg_add (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h₁ : DifferentiableAt ℝ f₁ c)
    (h₂ : DifferentiableAt ℝ f₂ c) :
    pbOp l (fun c' => -(f₁ c' + f₂ c')) c = -(pbOp l f₁ c + pbOp l f₂ c) := by
  have e : (fun c' => -(f₁ c' + f₂ c')) = -(f₁ + f₂) := rfl
  simp only [pbOp, wirtBar]
  split_ifs
  · rw [e, fderiv_neg, fderiv_add h₁ h₂]
    simp only [neg_apply, ContinuousLinearMap.add_apply]
    module
  · simp

end pbop

theorem jDRvConseq_of (hC : JDRvCont) : JDRvConseq := by
  intro hT hA hS Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ
  have hP := crd_pbOp_QL_last_comm
  set Dc : (Fin r → ℂ) → Set (Q.Mx k r) := fun c => {g | Q.wCell k r (Fin.last r) c * g ∈ D} with hDc
  set Φ := Q.resG k r (Fin.last r) J with hΦdef
  have hO : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} := cq_open hD
  have hFam : Q.FamFF k r z z' π π' (Fin.last r) Dc Φ :=
    Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ (Fin.last r)
  set Ψ : ℕ → Fin 2 → Q.Fn k r (Wq →L[ℂ] Wp) := fun m b => Q.crd (tdUv r Y m b) Φ with hΨdef
  have eΨ00 : Ψ 0 0 = Φ := by funext c g; simp [hΨdef, tdUv, Q.crd]
  have eΨ01 : Ψ 0 1 = (0 : ℂ) • Φ := by funext c g; simp [hΨdef, tdUv, Q.crd]
  have eΨ10 : ∀ h : 1 ≤ r, Ψ 1 0 = Y • Φ - Q.crd (pbOp ⟨r - 1, by omega⟩) Φ := by
    intro h; funext c g; simp [hΨdef, tdUv, Q.crd, h]
  have eΨ11 : ∀ h : 1 ≤ r, Ψ 1 1 = Q.crd (cbiOp ⟨r - 1, by omega⟩) Φ := by
    intro h; funext c g; simp [hΨdef, tdUv, Q.crd, h]
  have eΨ2 : ∀ (m : ℕ) (h : m + 2 ≤ r) (b : Fin 2), Ψ (m + 2) b =
      Y • Ψ (m + 1) b - Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) b) -
        Q.crd (cbOp ⟨r - (m + 1), by omega⟩) (Q.crd (cbiOp ⟨r - (m + 2), by omega⟩) (Ψ m b)) := by
    intro m h b; funext c g; simp only [hΨdef, tdUv, dif_pos h, Q.crd, Pi.sub_apply, Pi.smul_apply]
  have famΨ : ∀ m, m ≤ r → ∀ b, Q.FamFF k r z z' π π' (Fin.last r) Dc (Ψ m b) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm b
    rcases m with _ | _ | m
    · fin_cases b
      · simpa [eΨ00] using hFam
      · simpa [eΨ01] using cq_smul hFam 0
    · fin_cases b
      · show Q.FamFF k r z z' π π' (Fin.last r) Dc (Ψ 1 0)
        rw [eΨ10 hm]
        exact cq_sub (cq_smul hFam Y) (cq_opL hz hz' hO hFam _ 3)
      · show Q.FamFF k r z z' π π' (Fin.last r) Dc (Ψ 1 1)
        rw [eΨ11 hm]
        exact cq_opL hz hz' hO hFam _ 5
    · rw [eΨ2 m hm b]
      exact cq_sub (cq_sub (cq_smul (ih (m + 1) (by omega) (by omega) b) Y)
        (cq_opL hz hz' hO (ih (m + 1) (by omega) (by omega) b) _ 3))
        (cq_opL hz hz' hO (cq_opL hz hz' hO (ih m (by omega) (by omega) b) _ 5) _ 4)
  have hQLfam : ∀ F : Q.Fn k r (Wq →L[ℂ] Wp), Q.FamFF k r z z' π π' (Fin.last r) Dc F → ∀ a b : Fin 2,
      Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.QL k r z z' (Fin.last r) Y a b F) := fun F hF a b =>
    ⟨Formalism.FourierDecayAlt.P.transfer_joint_smooth (Wq →L[ℂ] Wp) k r z z' (Fin.last r) _ F Y a b hO hF.1,
      fun c hc => Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms Wp Wq k r z z' π π' (Fin.last r) (Dc c) Y a b hz hz'
        (cq_isDom hD hc) _ (hF.2 c hc)⟩
  have hlin : ∀ (a b : Fin 2) (c : Fin r → ℂ), c ∈ OmX r → ∀ (f f₂ : Q.Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ),
      Q.SmoothLev k r (Fin.last r) (Dc c) f → Q.SmoothLev k r (Fin.last r) (Dc c) f₂ →
      ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
        Q.tL k r z z' (Fin.last r) Y a b (fun x => f x + s • f₂ x) g =
          Q.tL k r z z' (Fin.last r) Y a b f g + s • Q.tL k r z z' (Fin.last r) Y a b f₂ g :=
    fun a b c hc f f₂ s hf hf₂ g hg hgD =>
      (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) (Dc c) Y a b f f₂ s
        (cq_isDom hD hc).1 hf hf₂ g ⟨hg, hgD⟩).1
  have hsm : ∀ (a b : Fin 2) (f : Q.Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (g : Q.Mx k r),
      Q.tL k r z z' (Fin.last r) Y a b (fun x => s • f x) g = s • Q.tL k r z z' (Fin.last r) Y a b f g := by
    intro a b f s g
    have := Formalism.FourierDecayAlt.P5.tL_smulC (E := Wq →L[ℂ] Wp) z z' (Fin.last r) Y a b s f
    exact congrFun this g
  have hnb : ∀ c ∈ OmX r, ∀ g : Q.Mx k r, g ∈ Dc c → {c' | c' ∈ OmX r ∧ g ∈ Dc c'} ∈ nhds c := by
    intro c hc g hgD
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := continuous_id.prodMk continuous_const
    exact (hO.preimage hcont).mem_nhds ⟨hc, hgD⟩
  have hdiff : ∀ F : Q.Fn k r (Wq →L[ℂ] Wp), Q.FamFF k r z z' π π' (Fin.last r) Dc F →
      ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c → DifferentiableAt ℝ (fun c' => F c' g) c :=
    fun F hF c hc g hg hgD => (cq_contDiffAt hF.1 ⟨hc, hgD⟩ hg).differentiableAt (by simp)
  have key : ∀ m, m ≤ r → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨r - m, by omega⟩ c g =
        -(Q.QL k r z z' (Fin.last r) Y 0 1 (Ψ m 0) c g + Q.QL k r z z' (Fin.last r) Y 1 1 (Ψ m 1) c g) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm c hc g hg hcg
    rcases m with _ | _ | m
    · have h := hT Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
      have e : (⟨r - 0, by omega⟩ : Fin (r + 1)) = Fin.last r := Fin.ext (by simp)
      rw [e, h, eΨ00, eΨ01]
      have h0 : Q.QL k r z z' (Fin.last r) Y 1 1 ((0 : ℂ) • Φ) c g = 0 := by
        show Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => (0 : ℂ) • Φ c x) g = 0
        rw [hsm, zero_smul]
      rw [h0, add_zero]
    · have h := hA Wp Wq k r hm z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
      have e : (⟨r - (0 + 1), by omega⟩ : Fin (r + 1)) = ⟨r - 1, by omega⟩ := rfl
      rw [e, h]
      simp only [Pi.sub_apply, Pi.smul_apply, Q.crd]
      have hTop : ∀ c' ∈ OmX r, g ∈ Dc c' →
          FNv k r z z' Y J (Fin.last r) c' g = -Q.QL k r z z' (Fin.last r) Y 0 1 Φ c' g :=
        fun c' hc' hgD' => hT Wp Wq k r z z' π π' D Y hz hz' hD J hJ c' hc' g hg hgD'
      have hev : (fun c' => FNv k r z z' Y J (Fin.last r) c' g) =ᶠ[nhds c]
          (fun c' => -Q.QL k r z z' (Fin.last r) Y 0 1 Φ c' g) := by
        filter_upwards [hnb c hc g hcg] with c' hc'
        exact hTop c' hc'.1 hc'.2
      rw [vcq_pbOp_loc _ hev, vcq_pbOp_neg, hTop c hc hcg]
      have hpc := hP Wp Wq k r z z' π π' Dc Φ hz hz' hO hFam ⟨r - 1, by omega⟩ Y 0 1 c hc g hg hcg
      simp only [Q.crd] at hpc
      rw [hpc, eΨ10 hm, eΨ11 hm]
      have e2 : Q.QL k r z z' (Fin.last r) Y 0 1 (Y • Φ - Q.crd (pbOp ⟨r - 1, by omega⟩) Φ) c g =
          Y • Q.QL k r z z' (Fin.last r) Y 0 1 Φ c g +
            (-1 : ℂ) • Q.QL k r z z' (Fin.last r) Y 0 1 (Q.crd (pbOp ⟨r - 1, by omega⟩) Φ) c g := by
        show Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => Y • Φ c x - Q.crd (pbOp ⟨r - 1, by omega⟩) Φ c x) g = _
        have e3 : (fun x => Y • Φ c x - Q.crd (pbOp ⟨r - 1, by omega⟩) Φ c x) =
            (fun x => Y • Φ c x + (-1 : ℂ) • Q.crd (pbOp ⟨r - 1, by omega⟩) Φ c x) := by
          funext x; rw [neg_one_smul, sub_eq_add_neg]
        rw [e3, hlin 0 1 c hc (fun x => Y • Φ c x) (Q.crd (pbOp ⟨r - 1, by omega⟩) Φ c) (-1)
          ((cq_smul hFam Y).2 c hc).1 ((cq_opL hz hz' hO hFam _ 3).2 c hc).1 g hg hcg, hsm]
        rfl
      have e4 : Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (cbiOp ⟨r - 1, by omega⟩) Φ) c g =
          (star (c ⟨r - 1, by omega⟩))⁻¹ • Q.QL k r z z' (Fin.last r) Y 1 1 Φ c g := by
        show Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => (star (c ⟨r - 1, by omega⟩))⁻¹ • Φ c x) g = _
        rw [hsm]
        rfl
      rw [e2, e4]
      simp only [cbiOp]
      module
    · have hm' : m + 2 ≤ r := hm
      have h := hS Wp Wq k r z z' π π' D Y hz hz' hD J hJ (r - (m + 2)) (by omega) c hc g hg hcg
      have e1 : (⟨r - (m + 2) + 1, by omega⟩ : Fin (r + 1)) = ⟨r - (m + 1), by omega⟩ := Fin.ext (by simp; omega)
      have e2 : (⟨r - (m + 2) + 2, by omega⟩ : Fin (r + 1)) = ⟨r - m, by omega⟩ := Fin.ext (by simp; omega)
      have e1' : (⟨r - (m + 2) + 1, by omega⟩ : Fin r) = ⟨r - (m + 1), by omega⟩ := Fin.ext (by simp; omega)
      rw [e1, e2, e1'] at h
      have e0 : (⟨r - (m + 1 + 1), by omega⟩ : Fin (r + 1)) = ⟨r - (m + 2), by omega⟩ := rfl
      rw [e0, h]
      simp only [Pi.sub_apply, Pi.smul_apply, Q.crd, cbOp, cbiOp]
      have ih1 := ih (m + 1) (by omega) (by omega)
      have ih0 := ih m (by omega) (by omega)
      have hF0 := famΨ (m + 1) (by omega) 0
      have hF1 := famΨ (m + 1) (by omega) 1
      have hev : (fun c' => FNv k r z z' Y J ⟨r - (m + 1), by omega⟩ c' g) =ᶠ[nhds c]
          (fun c' => -(Q.QL k r z z' (Fin.last r) Y 0 1 (Ψ (m + 1) 0) c' g +
            Q.QL k r z z' (Fin.last r) Y 1 1 (Ψ (m + 1) 1) c' g)) := by
        filter_upwards [hnb c hc g hcg] with c' hc'
        exact ih1 c' hc'.1 g hg hc'.2
      rw [vcq_pbOp_loc _ hev, vcq_pbOp_neg_add _ (hdiff _ (hQLfam _ hF0 0 1) c hc g hg hcg)
        (hdiff _ (hQLfam _ hF1 1 1) c hc g hg hcg)]
      have hp0 := hP Wp Wq k r z z' π π' Dc (Ψ (m + 1) 0) hz hz' hO hF0 ⟨r - (m + 2), by omega⟩ Y 0 1 c hc g hg hcg
      have hp1 := hP Wp Wq k r z z' π π' Dc (Ψ (m + 1) 1) hz hz' hO hF1 ⟨r - (m + 2), by omega⟩ Y 1 1 c hc g hg hcg
      simp only [Q.crd] at hp0 hp1
      rw [hp0, hp1, ih1 c hc g hg hcg, ih0 c hc g hg hcg]
      have hR : ∀ a : Fin 2, Q.QL k r z z' (Fin.last r) Y a 1 (Ψ (m + 2) a) c g =
          (Y • Q.QL k r z z' (Fin.last r) Y a 1 (Ψ (m + 1) a) c g +
            (-1 : ℂ) • Q.QL k r z z' (Fin.last r) Y a 1 (Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) a)) c g) +
          (-(star (c ⟨r - (m + 1), by omega⟩) * (star (c ⟨r - (m + 2), by omega⟩))⁻¹)) •
            Q.QL k r z z' (Fin.last r) Y a 1 (Ψ m a) c g := by
        intro a
        have hA' := famΨ (m + 1) (by omega) a
        have hB' := famΨ m (by omega) a
        have hPA := cq_opL hz hz' hO hA' ⟨r - (m + 2), by omega⟩ 3
        show Q.tL k r z z' (Fin.last r) Y a 1 (Ψ (m + 2) a c) g = _
        have e5 : Ψ (m + 2) a c = fun x => (Y • Ψ (m + 1) a c x +
            (-1 : ℂ) • Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) a) c x) +
            (-(star (c ⟨r - (m + 1), by omega⟩) * (star (c ⟨r - (m + 2), by omega⟩))⁻¹)) • Ψ m a c x := by
          rw [eΨ2 m hm' a]
          funext x
          simp only [Pi.sub_apply, Pi.smul_apply, Q.crd, cbOp, cbiOp]
          module
        rw [e5, hlin a 1 c hc (fun x => Y • Ψ (m + 1) a c x +
            (-1 : ℂ) • Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) a) c x)
          (Ψ m a c) _ ((cq_add (cq_smul hA' Y) (cq_smul hPA (-1))).2 c hc).1 (hB'.2 c hc).1 g hg hcg,
          hlin a 1 c hc (fun x => Y • Ψ (m + 1) a c x) (Q.crd (pbOp ⟨r - (m + 2), by omega⟩) (Ψ (m + 1) a) c) (-1)
            ((cq_smul hA' Y).2 c hc).1 (hPA.2 c hc).1 g hg hcg, hsm]
        rfl
      rw [hR 0, hR 1]
      module

  have famV : ∀ i, i ≤ r → ∀ F : Q.Fn k r (Wq →L[ℂ] Wp), Q.FamFF k r z z' π π' (Fin.last r) Dc F →
      Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.vABs r Y i).1 F) ∧
        Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.vABs r Y i).2 F) := by
    intro i
    induction i with
    | zero =>
      intro _ F hF
      refine ⟨?_, ?_⟩
      · have e : Q.crd (Q.vABs r Y 0).1 F = F := by funext c g; rfl
        rw [e]; exact hF
      · have e : Q.crd (Q.vABs r Y 0).2 F = (0 : ℂ) • F := by funext c g; simp [Q.vABs, Q.crd]
        rw [e]; exact cq_smul hF 0
    | succ i ih =>
      intro hi F hF
      have hlt : i < r := by omega
      refine ⟨?_, ?_⟩
      · have e : Q.crd (Q.vABs r Y (i + 1)).1 F = Q.crd (Q.vABs r Y i).1 (Y • F - Q.crd (pbOp ⟨i, hlt⟩) F) -
            Q.crd (Q.vABs r Y i).2 (Q.crd (cbOp ⟨i, hlt⟩) F) := by
          funext c g; simp only [Q.vABs, dif_pos hlt, Q.crd, Pi.sub_apply]; rfl
        rw [e]
        exact cq_sub (ih (by omega) _ (cq_sub (cq_smul hF Y) (cq_opL hz hz' hO hF _ 3))).1
          (ih (by omega) _ (cq_opL hz hz' hO hF _ 4)).2
      · have e : Q.crd (Q.vABs r Y (i + 1)).2 F = Q.crd (Q.vABs r Y i).1 (Q.crd (cbiOp ⟨i, hlt⟩) F) := by
          funext c g; simp only [Q.vABs, dif_pos hlt, Q.crd]
        rw [e]
        exact (ih (by omega) _ (cq_opL hz hz' hO hF _ 5)).1
  have famVb : ∀ a : Fin 2, Q.FamFF k r z z' π π' (Fin.last r) Dc (Q.crd (Q.cmp (Q.vABs r Y r) a) Φ) := by
    intro a
    fin_cases a
    · exact (famV r le_rfl Φ hFam).1
    · exact (famV r le_rfl Φ hFam).2
  intro c hc g hg hcg
  have hk := key r le_rfl c hc g hg hcg
  have e : (⟨r - r, by omega⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
  rw [e] at hk
  rw [hk]
  have hsw : ∀ a : Fin 2, Q.QL k r z z' (Fin.last r) Y a 1 (Ψ r a) c g =
      Q.QL k r z z' (Fin.last r) Y a 1 (Q.crd (Q.cmp (Q.vABs r Y r) a) Φ) c g := by
    intro a
    refine (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) (Dc c) Y a 1 (Ψ r a c)
      (Q.crd (Q.cmp (Q.vABs r Y r) a) Φ c) 0 (cq_isDom hD hc).1 ((famΨ r le_rfl a).2 c hc).1
      ((famVb a).2 c hc).1 g ⟨hg, hcg⟩).2 ?_
    intro x hx
    have hOx : IsOpen {c' : Fin r → ℂ | c' ∈ OmX r ∧ x ∈ Dc c'} :=
      hO.preimage (continuous_id.prodMk continuous_const)
    have hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c' => Φ c' x) {c' | c' ∈ OmX r ∧ x ∈ Dc c'} :=
      fun c' hc' => (cq_contDiffAt hFam.1 hc' hx.1).contDiffWithinAt
    exact hC (Wq →L[ℂ] Wp) r Y _ hOx (fun c' hc' => hc'.1) (fun c' => Φ c' x) hsmooth c ⟨hc, hx.2⟩ a
  simp only [Pi.add_apply]
  rw [hsw 0, hsw 1]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

namespace ContPfM

section ring

variable {R : Type*} [Ring R] (a c d : ℕ → R)

def Mi (i : ℕ) : Matrix (Fin 2) (Fin 2) R := !![a i, d i; -c i, 0]

def prodM (lo n : ℕ) : Matrix (Fin 2) (Fin 2) R := ((List.range n).map fun j => Mi a c d (lo + j)).prod

def bus : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => ((bus i).1 * a i - (bus i).2 * c i, (bus i).1 * d i)

def tds (r : ℕ) : ℕ → Fin 2 → R
  | 0, b => if b = 0 then 1 else 0
  | 1, b => if 1 ≤ r then (if b = 0 then a (r - 1) else d (r - 1)) else 0
  | m + 2, b => if m + 2 ≤ r then a (r - (m + 2)) * tds r (m + 1) b - c (r - (m + 1)) * d (r - (m + 2)) * tds r m b else 0

variable {a c d}

theorem prodM_succ_left (lo n : ℕ) : prodM a c d lo (n + 1) = Mi a c d lo * prodM a c d (lo + 1) n := by
  unfold prodM
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 2
  exact List.map_congr_left (fun j _ => by
    show Mi a c d (lo + (j + 1)) = Mi a c d (lo + 1 + j)
    congr 1
    omega)

theorem prodM_succ_right (lo n : ℕ) : prodM a c d lo (n + 1) = prodM a c d lo n * Mi a c d (lo + n) := by
  unfold prodM
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

theorem bus_eq : ∀ i, (bus a c d i).1 = prodM a c d 0 i 0 0 ∧ (bus a c d i).2 = prodM a c d 0 i 0 1
  | 0 => by simp [bus, prodM]
  | i + 1 => by
    obtain ⟨h1, h2⟩ := bus_eq i
    rw [prodM_succ_right]
    simp only [bus, h1, h2, Matrix.mul_apply, Fin.sum_univ_two, Mi, zero_add]
    simp [sub_eq_add_neg]

theorem tds_eq (hcd : ∀ i, Commute (c (i + 1)) (d i)) (r : ℕ) :
    ∀ m, m ≤ r → ∀ b, tds a c d r m b = prodM a c d (r - m) m 0 b
  | 0, _, b => by fin_cases b <;> simp [tds, prodM]
  | 1, hm, b => by
    rw [prodM_succ_left]
    fin_cases b <;> simp [tds, hm, prodM, Mi]
  | m + 2, hm, b => by
    have ih1 := tds_eq hcd r (m + 1) (by omega) b
    have ih0 := tds_eq hcd r m (by omega) b
    have e1 : r - (m + 2) + 1 = r - (m + 1) := by omega
    have e2 : r - (m + 1) + 1 = r - m := by omega
    show (if m + 2 ≤ r then a (r - (m + 2)) * tds a c d r (m + 1) b -
        c (r - (m + 1)) * d (r - (m + 2)) * tds a c d r m b else 0) = _
    have hL : prodM a c d (r - (m + 1)) (m + 1) = Mi a c d (r - (m + 1)) * prodM a c d (r - m) m := by
      rw [prodM_succ_left, e2]
    have hR : prodM a c d (r - (m + 2)) (m + 2) =
        Mi a c d (r - (m + 2)) * (Mi a c d (r - (m + 1)) * prodM a c d (r - m) m) := by
      rw [prodM_succ_left, e1, hL]
    rw [if_pos hm, ih1, ih0, hL, hR]
    have hc := (hcd (r - (m + 2))).eq
    rw [e1] at hc
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Mi]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, zero_mul, add_zero, neg_mul]
    simp only [hc, mul_neg, mul_assoc, sub_eq_add_neg]

theorem tds_bus (hcd : ∀ i, Commute (c (i + 1)) (d i)) (r : ℕ) :
    tds a c d r r 0 = (bus a c d r).1 ∧ tds a c d r r 1 = (bus a c d r).2 := by
  rw [tds_eq hcd r r le_rfl, tds_eq hcd r r le_rfl, (bus_eq r).1, (bus_eq r).2, Nat.sub_self]
  exact ⟨rfl, rfl⟩

end ring

section ops

open ContPf

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

variable (X) in

def aSv (Y : ℂ) (i : ℕ) : Module.End ℂ (WSm r X) := algebraMap ℂ _ Y - eS X i 3

theorem cp_vABs (Y : ℂ) : ∀ i, i ≤ r → ∀ f : WSm r X,
    (Q.vABs r Y i).1 (f : (Fin r → ℂ) → X) = (((bus (aSv X Y) (eS X · 4) (eS X · 5) i).1 f : WSm r X) : (Fin r → ℂ) → X) ∧
      (Q.vABs r Y i).2 (f : (Fin r → ℂ) → X) = (((bus (aSv X Y) (eS X · 4) (eS X · 5) i).2 f : WSm r X) : (Fin r → ℂ) → X)
  | 0, _, f => ⟨rfl, rfl⟩
  | i + 1, hi, f => by
    have hir : i < r := by omega
    have ih := cp_vABs Y i (by omega)
    simp only [Q.vABs, dif_pos hir, bus]
    refine ⟨?_, ?_⟩
    · have e1 : Y • (f : (Fin r → ℂ) → X) - pbOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) =
          ((aSv X Y i f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [aSv, eS, dif_pos hir]
        rfl
      have e2 : cbOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) = ((eS X i 4 f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [eS, dif_pos hir]
        rfl
      rw [e1, e2, (ih _).1, (ih _).2]
      rfl
    · have e3 : cbiOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) = ((eS X i 5 f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [eS, dif_pos hir]
        rfl
      rw [e3, (ih _).1]
      rfl

theorem cp_tdUv (Y : ℂ) (b : Fin 2) : ∀ m, ∀ f : WSm r X,
    tdUv r Y m b (f : (Fin r → ℂ) → X) = ((tds (aSv X Y) (eS X · 4) (eS X · 5) r m b f : WSm r X) : (Fin r → ℂ) → X)
  | 0, f => by
    fin_cases b <;> simp [tdUv, tds]
  | 1, f => by
    by_cases h1 : 1 ≤ r
    · have hr : r - 1 < r := by omega
      fin_cases b
      · simp only [tdUv, tds, dif_pos h1, if_pos h1, Fin.zero_eta, if_true, aSv, eS, dif_pos hr]
        rfl
      · simp only [tdUv, tds, dif_pos h1, if_pos h1, Fin.mk_one, one_ne_zero, if_false, eS, dif_pos hr]
        rfl
    · simp only [tdUv, tds, dif_neg h1, if_neg h1]
      rfl
  | m + 2, f => by
    by_cases h2 : m + 2 ≤ r
    · have ih1 := cp_tdUv Y b (m + 1) f
      have ih0 := cp_tdUv Y b m f
      have hr2 : r - (m + 2) < r := by omega
      have hr1 : r - (m + 1) < r := by omega
      simp only [tdUv, tds, dif_pos h2, if_pos h2]
      rw [ih1, ih0]
      simp only [aSv, eS, dif_pos hr2, dif_pos hr1]
      rfl
    · simp only [tdUv, tds, dif_neg h2, if_neg h2]
      rfl

end ops

section loc

open ContPf

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem loc_pbOp (l : Fin r) : Loc (X := X) (pbOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [pbOp, wirtBar, hy.fderiv_eq]

theorem loc_cbOp (l : Fin r) : Loc (X := X) (cbOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cbOp, hy]

theorem loc_cbiOp (l : Fin r) : Loc (X := X) (cbiOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cbiOp, hy]

theorem loc_tdUv (Y : ℂ) (b : Fin 2) : ∀ m, Loc (tdUv (X := X) r Y m b)
  | 0 => by
    unfold tdUv
    split_ifs
    · exact loc_id
    · exact loc_zero
  | 1 => by
    unfold tdUv
    split_ifs
    · exact loc_sub (loc_smul Y loc_id) (loc_pbOp _)
    · exact loc_cbiOp _
    · exact loc_zero
  | m + 2 => by
    have ih1 := loc_tdUv Y b (m + 1)
    have ih0 := loc_tdUv Y b m
    unfold tdUv
    split_ifs
    · exact loc_sub (loc_sub (loc_smul Y ih1) (loc_comp (loc_pbOp _) ih1))
        (loc_comp (loc_cbOp _) (loc_comp (loc_cbiOp _) ih0))
    · exact loc_zero

theorem loc_vABs (Y : ℂ) : ∀ i, Loc (X := X) (Q.vABs r Y i).1 ∧ Loc (X := X) (Q.vABs r Y i).2
  | 0 => ⟨loc_id, loc_zero⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := loc_vABs Y i
    by_cases hi : i < r
    · simp only [Q.vABs, dif_pos hi]
      exact ⟨loc_sub (loc_comp h1 (loc_sub (loc_smul Y loc_id) (loc_pbOp _))) (loc_comp h2 (loc_cbOp _)),
        loc_comp h1 (loc_cbiOp _)⟩
    · simp only [Q.vABs, dif_neg hi]
      exact ⟨h1, h2⟩

end loc

end ContPfM

open ContPf ContPfM in
theorem mirror_residue_continuity : JDRvCont := by
  intro X _ _ r Y O hO hOm f hf c hc b
  obtain ⟨f', hf'm, hf'e⟩ := cp_cutoff O hO hOm f hf c hc
  have e1 : tdUv r Y r b f c = tdUv r Y r b f' c := ((loc_tdUv Y b r) f f' c hf'e.symm).eq_of_nhds
  have ev := loc_vABs (X := X) (r := r) Y r
  have h3 := cp_tdUv Y b r ⟨f', hf'm⟩
  have h4 := cp_vABs Y r le_rfl ⟨f', hf'm⟩
  have h5 := tds_bus (a := aSv (r := r) X Y) (c := (eS X · 4)) (d := (eS X · 5))
    (fun i => eS_comm (i + 1) i (by omega) 4 5) r
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · have e2 : (Q.vABs r Y r).1 f c = (Q.vABs r Y r).1 f' c := (ev.1 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, if_true]
    rw [e1, e2]
    change tdUv r Y r 0 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vABs r Y r).1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.1, h5.1]
  · have e2 : (Q.vABs r Y r).2 f c = (Q.vABs r Y r).2 f' c := (ev.2 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, show ¬ ((1 : Fin 2) = 0) by decide, if_false]
    rw [e1, e2]
    change tdUv r Y r 1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vABs r Y r).2 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.2, h5.2]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

namespace RvB

variable {k r : ℕ}

theorem eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  simp only [eI, esI, ne_eq, Fin.ext_iff]; have := a.isLt; have := b.isLt; omega

theorem eI_inj {a b : Fin r} (h : eI k r a = eI k r b) : a = b := by
  simp only [eI, Fin.ext_iff] at h; exact Fin.ext h

theorem esI_inj {a b : Fin r} (h : esI k r a = esI k r b) : a = b := by
  simp only [esI, Fin.ext_iff] at h; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)

theorem w1_mulVec_bvec_eI (a : Fin r) (c : ℂ) : Q.w1 k r a c *ᵥ bvec (eI k r a) = c • bvec (esI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_e, Formalism.FourierDecayAlt.P.Qx3.dd_e]
  split_ifs <;> simp

theorem w1_mulVec_bvec_esI (a : Fin r) (c : ℂ) : Q.w1 k r a c *ᵥ bvec (esI k r a) = (star c)⁻¹ • bvec (eI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_es, Formalism.FourierDecayAlt.P.Qx3.dd_es]
  split_ifs <;> simp

theorem w1_mulVec_eq_self_of_eI_esI_eq_zero (b : Fin r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) (h1 : v (eI k r b) = 0)
    (h2 : v (esI k r b) = 0) : Q.w1 k r b c *ᵥ v = v := by
  funext p
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Formalism.FourierDecayAlt.P.Qx3.sw k b p)]
  · rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, if_pos (Formalism.FourierDecayAlt.P.Qx3.sw_sw b p).symm]
    rcases Formalism.FourierDecayAlt.P.Qx3.tri b p with h | h | ⟨h1', h2'⟩
    · subst h; rw [Formalism.FourierDecayAlt.P.Qx3.sw_e, h2, h1, mul_zero]
    · subst h; rw [Formalism.FourierDecayAlt.P.Qx3.sw_es, h1, h2, mul_zero]
    · rw [Formalism.FourierDecayAlt.P.Qx3.sw_o b h1' h2', Formalism.FourierDecayAlt.P.Qx3.dd_o b c h1' h2', one_mul]
  · intro q _ hq
    have : p ≠ Formalism.FourierDecayAlt.P.Qx3.sw k b q := fun h => hq (by rw [h, Formalism.FourierDecayAlt.P.Qx3.sw_sw])
    rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, if_neg this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem wl_fixv (c : Fin r → ℂ) (L : List (Fin r)) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b, v (eI k r b) = 0 ∧ v (esI k r b) = 0) : (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ v = v := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, w1_mulVec_eq_self_of_eI_esI_eq_zero b _ v (hv b).1 (hv b).2]


theorem wl_es (c : Fin r → ℂ) (L : List (Fin r)) (hL : L.Nodup) (a : Fin r) :
    (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ bvec (esI k r a) =
      if a ∈ L then (star (c a))⁻¹ • bvec (eI k r a) else bvec (esI k r a) := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hL.2]
    by_cases hab : a = b
    · subst hab
      rw [if_neg hL.1, w1_mulVec_bvec_esI, if_pos List.mem_cons_self]
    · have hmem : (a ∈ b :: L) ↔ a ∈ L := by simp [hab]
      by_cases h1 : a ∈ L
      · rw [if_pos h1, if_pos (hmem.2 h1), Matrix.mulVec_smul, Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => hab (eI_inj h)) (fun h => eI_ne_esI a b h)]
      · rw [if_neg h1, if_neg (fun h => h1 (hmem.1 h)), Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => eI_ne_esI b a h.symm) (fun h => hab (esI_inj h))]

theorem wc_list (c : Fin r → ℂ) : Q.wCell k r (Fin.last r) c =
    (((List.finRange r).filter fun a => a.val < (Fin.last r).val).map fun a => Q.w1 k r a (c a)).prod := rfl

theorem wc_nodup : ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val).Nodup :=
  (List.nodup_finRange r).filter _

theorem wc_mem (a : Fin r) : a ∈ ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val) := by
  rw [List.mem_filter]; exact ⟨List.mem_finRange a, by simp [a.isLt]⟩


theorem W_es (c : Fin r → ℂ) (a : Fin r) :
    Q.wCell k r (Fin.last r) c *ᵥ bvec (esI k r a) = (star (c a))⁻¹ • bvec (eI k r a) := by
  rw [wc_list, wl_es c _ wc_nodup, if_pos (wc_mem a)]

theorem W_fix (c : Fin r → ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ b, v (eI k r b) = 0 ∧ v (esI k r b) = 0) :
    Q.wCell k r (Fin.last r) c *ᵥ v = v := by
  rw [wc_list, wl_fixv c _ v hv]

theorem herm_uh {W : Q.Mx k r} (hW : W ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (W *ᵥ x) (W *ᵥ y) = herm (Hpk k r) x y := by
  have hW' : Wᴴ * Hpk k r * W = Hpk k r := hW
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW']

theorem herm_smul_right (x w : Fin (2 * r + k + 1) → ℂ) (s : ℂ) :
    herm (Hpk k r) x (s • w) = star s * herm (Hpk k r) x w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_bvec (p q : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec q) (bvec p) = Hpk k r p q := by
  unfold herm bvec
  rw [Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

section what₂

variable {c : Fin r → ℂ} {g : Q.Mx k r}

theorem row_e (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec q) (bvec (eI k r a)) =
      if q = eI k r a then c a else 0 := by
  have hW : Q.wCell k r (Fin.last r) c ∈ UH (Hpk k r) :=
    (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val)).1
  have hca : star (c a) ≠ 0 := star_ne_zero.2 (hc a)
  have he : bvec (eI k r a) = Q.wCell k r (Fin.last r) c *ᵥ (star (c a) • bvec (esI k r a)) := by
    rw [Matrix.mulVec_smul, W_es, smul_smul, mul_inv_cancel₀ hca, one_smul]
  have hges : g *ᵥ bvec (esI k r a) = bvec (esI k r a) := (hg.2 a (by simp [a.isLt])).2
  rw [← Matrix.mulVec_mulVec, he, herm_uh hW, herm_smul_right, star_star, ← hges, herm_uh hg.1, herm_bvec,
    Formalism.FourierDecayAlt.P.Qx3.hpk_row_es]
  split_ifs <;> simp

theorem herm_wCell_last_mul_mulVec_eq_of_inWb (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ v) z = herm (Hpk k r) (g *ᵥ v) z := by
  have hW : Q.wCell k r (Fin.last r) c ∈ UH (Hpk k r) :=
    (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val)).1
  have hzf : Q.wCell k r (Fin.last r) c *ᵥ z = z := W_fix c z fun b =>
    ⟨hz _ (Or.inl (by simp [eI])), hz _ (Or.inr (by simp [esI]; have := b.isLt; omega))⟩
  conv_lhs => rw [← hzf]
  rw [← Matrix.mulVec_mulVec, herm_uh hW]

theorem row_z_e (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin r) :
    herm (Hpk k r) (g *ᵥ bvec (eI k r a)) z = 0 ∧ herm (Hpk k r) (g *ᵥ bvec (esI k r a)) z = 0 := by
  obtain ⟨h1, h2⟩ := hg.2 a (by simp [a.isLt])
  have hz1 : z (esI k r a) = 0 := hz _ (Or.inr (by simp [esI]; have := a.isLt; omega))
  have hz2 : z (eI k r a) = 0 := hz _ (Or.inl (by simp [eI]))
  rw [h1, h2]
  constructor
  · simp only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Matrix.col_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Formalism.FourierDecayAlt.P.Qx3.hpk_col_e]
    split_ifs with h
    · subst h; simp [hz1]
    · simp
  · simp only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Matrix.col_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Formalism.FourierDecayAlt.P.Qx3.hpk_col_es]
    split_ifs with h
    · subst h; simp [hz2]
    · simp

end what₂

section dets

def Arow (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (t : Fin (k + 1)) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.of fun p q =>
    if h : p.val < r then (if q = eI k r ⟨p.val, h⟩ then c ⟨p.val, h⟩ else 0)
    else if h2 : p.val = r then (if q = wI k r t then 1 else 0)
    else if q = J ⟨p.val - r - 1, by have := p.isLt; omega⟩ then 1 else 0

theorem det_prop {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} {p p' : Fin m} (h : p ≠ p') (l : ℂ) (hA : A p = l • A p') :
    A.det = 0 := by
  have e : A = A.updateRow p (l • A p') := by rw [← hA, Matrix.updateRow_eq_self]
  rw [e, Matrix.det_updateRow_smul,
    Matrix.det_zero_of_row_eq h (by rw [Matrix.updateRow_self, Matrix.updateRow_ne h.symm]), mul_zero]

theorem det_updateRow_sum' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (v : ι → Fin m → ℂ) :
    (A.updateRow i (∑ t ∈ s, a t • v t)).det = ∑ t ∈ s, a t * (A.updateRow i (v t)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih]

theorem colsV_strictMono (t : Fin (k + 1)) : StrictMono (colsV k r t) := by
  intro i j h
  simp only [colsV, Fin.lt_def] at h ⊢
  split_ifs <;> omega

theorem colsV_mem_jSet (t : Fin (k + 1)) : colsV k r t ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert colsV_strictMono (k := k) (r := r) t

theorem prod_d (c : Fin r → ℂ) :
    ∏ p : Fin (2 * r + k + 1), (if h : p.val < r then c ⟨p.val, h⟩ else 1) = ∏ a : Fin r, c a := by
  let f : ℕ → ℂ := fun i => if h : i < r then c ⟨i, h⟩ else 1
  have h1 : ∏ p : Fin (2 * r + k + 1), (if h : p.val < r then c ⟨p.val, h⟩ else 1) =
      ∏ i ∈ Finset.range (2 * r + k + 1), f i := Fin.prod_univ_eq_prod_range f _
  have h2 : ∏ a : Fin r, c a = ∏ i ∈ Finset.range r, f i := by
    rw [← Fin.prod_univ_eq_prod_range f r]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [f, a.isLt]
  rw [h1, h2, ← Finset.prod_range_mul_prod_Ico f (show r ≤ 2 * r + k + 1 by omega)]
  rw [Finset.prod_eq_one (s := Finset.Ico r (2 * r + k + 1)) (fun i hi => by
    simp only [Finset.mem_Ico] at hi; simp [f, show ¬ i < r by omega]), mul_one]

theorem arow_zero (c : Fin r → ℂ) (h0 : 0 < k + 1) :
    Arow c (colsV k r ⟨0, h0⟩) ⟨0, h0⟩ = Matrix.diagonal fun p => if h : p.val < r then c ⟨p.val, h⟩ else 1 := by
  ext p q
  simp only [Arow, Matrix.of_apply, Matrix.diagonal_apply, colsV, eI, wI, Fin.ext_iff, Nat.not_lt_zero,
    if_false]
  split_ifs <;> first | rfl | omega

end dets

section dets2

theorem arow_succ (c : Fin r → ℂ) (t : ℕ) (ht : t + 1 < k + 1) :
    Arow c (colsV k r ⟨t + 1, ht⟩) ⟨t + 1, ht⟩ =
      (Arow c (colsV k r ⟨t, by omega⟩) ⟨t, by omega⟩).submatrix
        (Equiv.swap (⟨r, by omega⟩ : Fin (2 * r + k + 1)) ⟨r + 1 + t, by omega⟩) id := by
  ext p q
  simp only [Matrix.submatrix_apply, id, Equiv.swap_apply_def]
  by_cases h1 : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
  · subst h1
    simp only [if_true]
    simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  · by_cases h2 : p = (⟨r + 1 + t, by omega⟩ : Fin (2 * r + k + 1))
    · subst h2
      simp only [if_neg h1, if_true]
      simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    · simp only [if_neg h1, if_neg h2]
      have h1' : p.val ≠ r := fun h => h1 (Fin.ext h)
      have h2' : p.val ≠ r + 1 + t := fun h => h2 (Fin.ext h)
      simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

theorem det_arow_colsV (c : Fin r → ℂ) :
    ∀ (t : ℕ) (ht : t < k + 1), (Arow c (colsV k r ⟨t, ht⟩) ⟨t, ht⟩).det = (-1) ^ t * ∏ a, c a
  | 0, ht => by rw [arow_zero c ht, Matrix.det_diagonal, prod_d, pow_zero, one_mul]
  | t + 1, ht => by
    rw [arow_succ c t ht, Matrix.det_permute, Equiv.Perm.sign_swap (by simp only [ne_eq, Fin.ext_iff]; omega),
      det_arow_colsV c t (by omega), pow_succ]
    push_cast
    ring

end dets2

section dets3

theorem det_arow_ne (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) (t : Fin (k + 1))
    (hne : J ≠ colsV k r t) : (Arow c J t).det = 0 := by
  by_cases hA : ∃ j : Fin (r + k), (J j).val < r
  · obtain ⟨j, hj⟩ := hA
    have hJj : ∀ h, J ⟨r + 1 + j.val - r - 1, h⟩ = J j := fun h => congrArg J (Fin.ext (by show r + 1 + j.val - r - 1 = j.val; omega))
    refine det_prop (p := ⟨(J j).val, by omega⟩) (p' := ⟨r + 1 + j.val, by omega⟩)
      (by simp only [ne_eq, Fin.ext_iff]; omega) (c ⟨(J j).val, hj⟩) ?_
    funext q
    simp only [Arow, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, dif_pos hj,
      dif_neg (show ¬ (r + 1 + j.val < r) by omega), dif_neg (show ¬ (r + 1 + j.val = r) by omega), hJj]
    have : eI k r ⟨(J j).val, hj⟩ = J j := Fin.ext rfl
    rw [this]
    split_ifs <;> simp
  · push Not at hA
    by_cases hB : ∃ j, J j = wI k r t
    · obtain ⟨j, hj⟩ := hB
      have hJj : ∀ h, J ⟨r + 1 + j.val - r - 1, h⟩ = J j := fun h => congrArg J (Fin.ext (by show r + 1 + j.val - r - 1 = j.val; omega))
      refine Matrix.det_zero_of_row_eq (i := ⟨r, by omega⟩) (j := ⟨r + 1 + j.val, by omega⟩)
        (by simp only [ne_eq, Fin.ext_iff]; omega) ?_
      funext q
      simp only [Arow, Matrix.of_apply, dif_neg (show ¬ (r < r) by omega),
        dif_neg (show ¬ (r + 1 + j.val < r) by omega), dif_neg (show ¬ (r + 1 + j.val = r) by omega), hJj, hj]
      exact dif_pos trivial
    · push Not at hB
      exfalso
      apply hne
      have hsub : Finset.image J Finset.univ ⊆ Finset.image (colsV k r t) Finset.univ := by
        intro q hq
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
        have h1 := hA j
        have h2 : (J j).val ≠ r + t.val := fun h => hB j (Fin.ext (by simp [wI, h]))
        have hlt := (J j).isLt
        refine Finset.mem_image.2 ⟨⟨if (J j).val < r + t.val then (J j).val - r else (J j).val - r - 1, by
          have := t.isLt; split_ifs <;> omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        simp only [colsV]
        split_ifs <;> omega
      have hcard : (Finset.image (colsV k r t) Finset.univ).card ≤ (Finset.image J Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hJ.injective,
          Finset.card_image_of_injective _ (colsV_strictMono t).injective]
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      have hrange : Set.range J = Set.range (colsV k r t) := by
        have := congrArg (fun s : Finset (Fin (2 * r + k + 1)) => (s : Set (Fin (2 * r + k + 1)))) heq
        simpa [Finset.coe_image] using this
      exact (hJ.range_inj (colsV_strictMono t)).1 hrange

end dets3

section cell

variable {c : Fin r → ℂ} {g : Q.Mx k r}

theorem arow_update (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (t : Fin (k + 1)) :
    (Arow c J ⟨0, by omega⟩).updateRow ⟨r, by omega⟩ (bvec (wI k r t)) = Arow c J t := by
  ext p q
  rw [Matrix.updateRow_apply]
  by_cases hp : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
  · rw [if_pos hp]
    subst hp
    simp only [Arow, Matrix.of_apply, dif_neg (lt_irrefl r), bvec, Pi.single_apply]
    rw [dif_pos trivial]
  · rw [if_neg hp]
    have hp' : p.val ≠ r := fun h => hp (Fin.ext h)
    simp only [Arow, Matrix.of_apply, dif_neg hp']

theorem yrow_sum (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (fun q => herm (Hpk k r) (g *ᵥ bvec q) z) =
      ∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z • bvec (wI k r t) := by
  funext q
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hq : r ≤ q.val ∧ q.val ≤ r + k
  · obtain ⟨t0, rfl⟩ : ∃ t0 : Fin (k + 1), q = wI k r t0 :=
      ⟨⟨q.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩
    rw [Finset.sum_eq_single t0 (fun t _ ht => if_neg (fun h => ht (by
      simp only [wI, Fin.ext_iff] at h; exact Fin.ext (by omega)))) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  · rw [Finset.sum_eq_zero (fun t _ => if_neg (fun h => hq (by
      rw [h]; simp only [wI]; have := t.isLt; omega)))]
    by_cases h1 : q.val < r
    · have : q = eI k r ⟨q.val, h1⟩ := Fin.ext rfl
      rw [this]; exact (row_z_e hg hz _).1
    · have hq2 : r + k < q.val := by omega
      have : q = esI k r ⟨2 * r + k - q.val, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp only [esI]; have := q.isLt; omega)
      rw [this]; exact (row_z_e hg hz _).2

theorem alJ_cell (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    alJ k r z (Q.wCell k r (Fin.last r) c * g) J =
      ∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z * (Arow c J t).det := by
  have hM : (Matrix.of fun p q => rowV k r z (Q.wCell k r (Fin.last r) c * g) J p q) =
      (Arow c J ⟨0, by omega⟩).updateRow ⟨r, by omega⟩
        (∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z • bvec (wI k r t)) := by
    rw [← yrow_sum hg hz]
    ext p q
    rw [Matrix.updateRow_apply]
    by_cases hp : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
    · rw [if_pos hp]
      subst hp
      simp only [Matrix.of_apply, rowV, dif_neg (lt_irrefl r)]
      rw [dif_pos trivial]
      exact herm_wCell_last_mul_mulVec_eq_of_inWb hc hz (bvec q)
    · rw [if_neg hp]
      have hp' : p.val ≠ r := fun h => hp (Fin.ext h)
      simp only [Matrix.of_apply, rowV, Arow]
      by_cases h1 : p.val < r
      · rw [dif_pos h1, dif_pos h1, row_e hc hg]
      · rw [dif_neg h1, dif_neg h1, dif_neg hp', dif_neg hp']
  unfold alJ
  rw [hM, det_updateRow_sum' _ _ Finset.univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [arow_update]

theorem alJ_val (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) :
    alJ k r z (Q.wCell k r (Fin.last r) c * g) J =
      ∑ s : Fin (k + 1), (herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * ((-1) ^ (s : ℕ) * ∏ a, c a)) *
        (if J = colsV k r s then 1 else 0) := by
  rw [alJ_cell hc hg hz]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : J = colsV k r s
  · subst h
    have hd : (Arow c (colsV k r s) s).det = (-1) ^ (s : ℕ) * ∏ a, c a := det_arow_colsV c s.val s.isLt
    rw [hd, if_pos rfl, mul_one]
  · rw [det_arow_ne c J hJ s h, if_neg h, mul_zero, mul_zero]

end cell

end RvB

theorem mirror_residue_beta_holds : JDRvBeta := by
  intro k r
  refine ⟨1, one_ne_zero, ?_⟩
  intro E _ _ z z' Y f hz c hc g hg
  have hsm : ∀ J ∈ jSetR k r, StrictMono J := fun J hJ => by
    classical
    simpa [jSetR] using hJ
  have hL : rvhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
      ∑ t : Fin (k + 1), ∑ s : Fin (k + 1),
        (((-1 : ℂ) ^ (t : ℕ) * z' (wI k r t)) *
            (herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * ((-1) ^ (s : ℕ) * ∏ a, c a))) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g) := by
    unfold rvhatOp
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl fun J hJ => by rw [RvB.alJ_val hc hg hz J (hsm J hJ)]]
    simp_rw [Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single (colsV k r s)]
    · rw [if_pos rfl, mul_one]
    · intro J _ hJ
      rw [if_neg hJ, mul_zero, mul_zero, zero_smul]
    · intro h
      exact absurd (RvB.colsV_mem_jSet s) h
  have hR : NLv k r z z' 0 (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c * g) =
      ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
        (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g) := by
    show (∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
        (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) *
            herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g)) = _
    simp only [RvB.herm_wCell_last_mul_mulVec_eq_of_inWb hc hz]
  rw [hL, hR, Finset.smul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_smul]
  congr 1
  rw [pow_add]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDRRadP_of_steps (hA : JDRStepA) (hB : JDRStepB) : JDRRadP :=
  jDRRadP_of_parts JDBeta.residue_beta_holds residue_top_holds hA hB (jDRConseq_of residue_projection_commutation residue_continuity_holds)

theorem jDRGrpP_of_invFn (hA : JDRStepA) (hB : JDRStepB) (hI : JDRInvFn) : JDRGrpP :=
  jDRGrpP_of_parts (jDRRadP_of_steps hA hB) (jDRRealInvP_of_inv hI)

theorem jDRGrpM_of_vBeta_invFnM (hvB : JDRvBeta) (hvA : JDRvStepA) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDRGrpM :=
  jDRGrpM_of_parts (jDRRadM_of_parts hvB mirror_residue_top_holds hvA hvS (jDRvConseq_of mirror_residue_continuity))
    (jDRRealInvM_of_inv hIM)

theorem jDCapR_of_halves (hP : JDRGrpP) (hM : JDRGrpM) : JDCapR :=
  jDCapR_of_parts (jDRGrp_of_halves hP hM) residue_derivative_transition mirror_residue_model_holds

theorem jDOpR_of_poly_grp (hPoly : JDPolyOK) (hP : JDRGrpP) (hM : JDRGrpM) : JDOpR :=
  jDOpR_of_parts hPoly (jDCapR_of_halves hP hM)

theorem jDOpR_of_leaves (hPoly : JDPolyOK) (hA : JDRStepA) (hI : JDRInvFn) (hvB : JDRvBeta)
    (hvA : JDRvStepA) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDOpR :=
  jDOpR_of_poly_grp hPoly (jDRGrpP_of_invFn hA residue_second_move_holds hI) (jDRGrpM_of_vBeta_invFnM hvB hvA hvS hIM)

theorem jDOpR_of_invFn (hI : JDRInvFn) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDOpR :=
  jDOpR_of_leaves polynomial_decay_admissible residue_first_move_holds hI mirror_residue_beta_holds GrpMA.mirror_residue_first_move hvS hIM

theorem jDOpR_of_vStepB (hvS : JDRvStepB) : JDOpR :=
  jDOpR_of_invFn inverse_function_positive_holds hvS inverse_function_minus_holds

end Formalism.FourierDecayAlt.P.CutMP
end
