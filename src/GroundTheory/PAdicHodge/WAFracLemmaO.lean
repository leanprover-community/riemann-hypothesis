import Mathlib
import GroundTheory.PAdicHodge.WABridgeGerm
import GroundTheory.PAdicHodge.WAFracOrbit
import GroundTheory.PAdicHodge.BCrisRegularFinal
import GroundTheory.PAdicHodge.AnnNormAcrisToAnnPosBig
import GroundTheory.PAdicHodge.WAFracAnnPt
import GroundTheory.PAdicHodge.FundamentalSeqSurj

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma Laurent

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

theorem lt_rootRadius (τ : Set.Ioo (0 : ℝ) 1) : (τ : ℝ) < (frob ℂ_[p] p).rootRadius τ := by
  rw [rootRadius_coe]
  have h := Real.rpow_lt_rpow_of_exponent_gt τ.2.1 τ.2.2 (inv_p_lt_one (p := p))
  rwa [Real.rpow_one] at h

variable (p) in

def radTwo : Set.Ioo (0 : ℝ) 1 := (frob ℂ_[p] p).rootRadius (rhoMid p)

variable (p) in

def radC : Set.Ioo (0 : ℝ) 1 := (frob ℂ_[p] p).rootRadius (radTwo p)

theorem inv_p_lt_radTwo : (p : ℝ)⁻¹ < radTwo p :=
  inv_p_lt_rhoMid.trans_le (le_rootRadius (rhoMid p))

theorem radA_lt_inv_p : radA p < (p : ℝ)⁻¹ := by
  have h := pow_lt_pow_right_of_lt_one₀ (inv_p_pos (p := p)) inv_p_lt_one hp.out.one_lt
  rw [pow_one] at h
  exact h

theorem radA_lt_radTwo : radA p < radTwo p := radA_lt_inv_p.trans inv_p_lt_radTwo

theorem radTwo_lt_radC : (radTwo p : ℝ) < radC p := lt_rootRadius (radTwo p)

theorem radC_le_iterate (k : ℕ) :
    (radC p : ℝ) ≤ ((frob ℂ_[p] p).rootRadius^[k] (radC p) : Set.Ioo (0 : ℝ) 1) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (le_rootRadius _)

theorem pow_iterate_rootRadius (c : Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    (((frob ℂ_[p] p).rootRadius^[k] c : Set.Ioo (0 : ℝ) 1) : ℝ) ^ (p ^ k) = c := by
  rw [← coe_iterate_powRadius, iterate_powRadius_rootRadius]

theorem exists_approx {x : (𝓣).RobbaTilde} (hx : x ∈ allRad p) {M : ℝ} (hM : 1 ≤ M)
    (hdec : ∀ k : ℕ, tn hx ((frob ℂ_[p] p).rootRadius^[k] (radC p)) ^ (p ^ k) ≤
      (radC p : ℝ) ^ k * M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : 𝔸, (∀ r : Set.Ioc (0 : ℝ) (radTwo p), radA p ≤ r →
        (𝓣).extNorm (radTwo p) r (rep hx (radTwo p) - awayToExt p (radTwo p) s) ≤ ε) ∧
      gn ℂ_[p] p (radA p) s ≤ max (tn hx ⟨radA p, radA_pos, radA_lt_one⟩) 1 := by
  set c : ℝ := ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) with hc
  have hc0 : 0 < c := (radC p).2.1
  have hc1 : c < 1 := (radC p).2.2
  set q : ℝ := ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) / c with hq
  have hq0 : 0 < q := div_pos (radTwo p).2.1 hc0
  have hq1 : q < 1 := (div_lt_one hc0).2 radTwo_lt_radC
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hM0) hc1
  obtain ⟨k₂, hk₂⟩ := exists_pow_lt_of_lt_one (mul_pos hε (pow_pos hq0 L)) hq1
  set k := max L k₂ with hk
  set b : Set.Ioo (0 : ℝ) 1 := (frob ℂ_[p] p).rootRadius^[k] (radC p) with hb
  have hb0 : (0 : ℝ) < b := b.2.1
  have hb1 : (b : ℝ) < 1 := b.2.2
  have hcb : c ≤ b := radC_le_iterate k
  have hbk : (b : ℝ) ^ (p ^ k) = c := pow_iterate_rootRadius _ k
  have hckM : c ^ k * M < 1 := by
    have h1 : c ^ k ≤ c ^ L := pow_le_pow_of_le_one hc0.le hc1.le (le_max_left _ _)
    have h2 : c ^ k < M⁻¹ := h1.trans_lt hL
    calc c ^ k * M < M⁻¹ * M := mul_lt_mul_of_pos_right h2 hM0
      _ = 1 := inv_mul_cancel₀ hM0.ne'
  have hck1 : c ^ k ≤ 1 := pow_le_one₀ hc0.le hc1.le
  set δ : ℝ := min ε (c ^ k) with hδ
  have hδ0 : 0 < δ := lt_min hε (pow_pos hc0 k)
  have hradA_b : radA p ≤ b :=
    (radA_lt_radTwo.trans radTwo_lt_radC).le.trans hcb
  obtain ⟨d, hd, hdapp⟩ := (𝓣).exists_approx_convAll (rep hx b) ⟨radA p, radA_pos, hradA_b⟩ hδ0
  have hdb : ConvergesAt ((𝓣).coeffB d) b := hd b hb0 hb1
  set β : ℝ := gaussNorm ((𝓣).coeffB d) b with hβdef
  have hβ0 : 0 ≤ β := gaussNorm_nonneg hb0
  have hβ : β ≤ max (tn hx b) δ := by
    have e1 : β = (𝓣).extNorm b (topRad b) ((𝓣).ofAll d hd b) := ((𝓣).extNorm_ofAll hd (topRad b)).symm
    have e2 : (𝓣).ofAll d hd b = rep hx b + -(rep hx b - (𝓣).ofAll d hd b) := by ring
    rw [e1, e2]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le_max le_rfl ?_)
    rw [(𝓣).extNorm_neg]
    exact hdapp (topRad b) hradA_b
  have hβk : β ^ (p ^ k) ≤ c ^ k * M := by
    have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
    refine (pow_le_pow_left₀ hβ0 hβ _).trans ?_
    rcases le_total (tn hx b) δ with h | h
    · rw [max_eq_right h]
      calc δ ^ (p ^ k) ≤ (c ^ k) ^ (p ^ k) := pow_le_pow_left₀ hδ0.le (min_le_right _ _) _
        _ ≤ c ^ k := pow_le_of_le_one (pow_nonneg hc0.le _) hck1 hpk
        _ ≤ c ^ k * M := le_mul_of_one_le_right (pow_nonneg hc0.le _) hM
    · rw [max_eq_left h]
      exact hdec k
  have hβ1 : β < 1 := by
    by_contra hcon
    have := one_le_pow₀ (n := p ^ k) (not_lt.1 hcon)
    linarith

  set S := (𝓣).smallPart 1 d with hSdef
  set G := (𝓣).bigPart 1 d with hGdef
  have hSG : S + G = d := (𝓣).smallPart_add_bigPart 1 d
  have hS : (𝓣).ConvAll S := fun ρ h0 h1 =>
    (convergesAt_of_norm_le h0 ((𝓣).norm_coeffB_smallPart_le zero_lt_one d) (hd ρ h0 h1)).1
  have hG : (𝓣).ConvAll G := fun ρ h0 h1 =>
    (convergesAt_of_norm_le h0 ((𝓣).norm_coeffB_bigPart_le 1 d) (hd ρ h0 h1)).1

  have hGdig : ∀ n : ℤ, (𝓣).coeffB G n ≠ 0 →
      ‖(𝓣).coeffB G n‖ * (b : ℝ) ^ n ≤ β ∧ 0 ≤ n ∧ (k : ℤ) - L ≤ n := by
    intro n hn
    have h1 : 1 ≤ ‖(𝓣).coeffB G n‖ := ((𝓣).coeffB_bigPart_eq_zero_or 1 d n).resolve_left hn
    have e : (𝓣).coeffB G n = (𝓣).coeffB d n := by
      rw [hGdef, (𝓣).coeffB_bigPart]
      split_ifs with h
      · exact absurd (by rw [hGdef, (𝓣).coeffB_bigPart, if_pos h]) hn
      · rfl
    have h2 : ‖(𝓣).coeffB G n‖ * (b : ℝ) ^ n ≤ β := by rw [e]; exact hdb.le_gaussNorm n
    have h3 : (b : ℝ) ^ n ≤ β :=
      (le_mul_of_one_le_left (zpow_nonneg hb0.le n) h1).trans h2
    refine ⟨h2, ?_, ?_⟩
    · by_contra hneg
      have := one_le_zpow_of_nonpos₀ hb0 hb1.le (not_le.1 hneg).le
      linarith
    · have h4 : ((b : ℝ) ^ n) ^ (p ^ k) ≤ c ^ k * M :=
        (pow_le_pow_left₀ (zpow_nonneg hb0.le n) h3 _).trans hβk
      have h5 : ((b : ℝ) ^ n) ^ (p ^ k) = c ^ n := by
        rw [← hbk, ← zpow_natCast, ← zpow_natCast ((b : ℝ)) (p ^ k), ← zpow_mul, ← zpow_mul,
          mul_comm]
      have h6 : M ≤ (c ^ L)⁻¹ := by
        rw [le_inv_comm₀ hM0 (pow_pos hc0 L)]; exact hL.le
      have h7 : c ^ n ≤ c ^ ((k : ℤ) - L) := by
        rw [zpow_sub₀ hc0.ne', zpow_natCast, zpow_natCast, div_eq_mul_inv]
        rw [← h5]
        exact h4.trans (mul_le_mul_of_nonneg_left h6 (pow_nonneg hc0.le _))
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hc0 hc1).1 h7
  have hGnorm : ∀ r : ℝ, 0 < r → r ≤ radTwo p → gaussNorm ((𝓣).coeffB G) r ≤ ε := by
    intro r hr0 hr
    refine gaussNorm_le fun n => ?_
    by_cases hn : (𝓣).coeffB G n = 0
    · rw [hn, norm_zero, zero_mul]; exact hε.le
    obtain ⟨h2, hn0, hnk⟩ := hGdig n hn
    have hrb : r / b ≤ q := by
      rw [hq]
      exact div_le_div₀ (radTwo p).2.1.le hr hc0 hcb
    have e : ‖(𝓣).coeffB G n‖ * r ^ n = (‖(𝓣).coeffB G n‖ * (b : ℝ) ^ n) * (r / b) ^ n := by
      rw [div_zpow, mul_assoc, mul_div_cancel₀ _ (zpow_ne_zero _ hb0.ne')]
    rw [e]
    calc (‖(𝓣).coeffB G n‖ * (b : ℝ) ^ n) * (r / b) ^ n ≤ 1 * q ^ n :=
          mul_le_mul (h2.trans hβ1.le) (zpow_le_zpow_left₀ hn0 (div_nonneg hr0.le hb0.le) hrb)
            (zpow_nonneg (div_nonneg hr0.le hb0.le) _) zero_le_one
      _ = q ^ n := one_mul _
      _ ≤ q ^ ((k : ℤ) - L) := zpow_le_zpow_right_of_le_one₀ hq0 hq1.le hnk
      _ ≤ ε := by
        rw [zpow_sub₀ hq0.ne', zpow_natCast, zpow_natCast, div_le_iff₀ (pow_pos hq0 L)]
        exact ((pow_le_pow_of_le_one hq0.le hq1.le (le_max_right _ _)).trans hk₂.le)

  have hSdig : ∀ n, ‖(𝓣).coeffB S n‖ ≤ 1 := fun n =>
    ((𝓣).norm_coeffB_smallPart_lt zero_lt_one d n).le
  obtain ⟨s, hs⟩ := exists_toB_eq_of_norm_coeffB_le_one hSdig
  have hSd : (𝓣).ofAll d hd b = (𝓣).ofAll S hS b + (𝓣).ofAll G hG b := by
    rw [← (𝓣).ofAll_add hS hG]; exact (𝓣).ofAll_congr _ _ hSG.symm b
  have hb2 : (radTwo p : ℝ) ≤ b := radTwo_lt_radC.le.trans hcb
  refine ⟨s, fun r hr => ?_, ?_⟩
  · have e1 : rep hx (radTwo p) - awayToExt p (radTwo p) s =
        (𝓣).res hb2 (rep hx b - (𝓣).ofAll S hS b) := by
      rw [map_sub, res_rep, (𝓣).res_ofAll, awayToExt_eq_ofAll]
      congr 1
      exact (𝓣).ofAll_congr _ _ hs _
    rw [e1, (𝓣).extNorm_res]
    have e2 : rep hx b - (𝓣).ofAll S hS b = (rep hx b - (𝓣).ofAll d hd b) + (𝓣).ofAll G hG b := by
      rw [hSd]; ring
    rw [e2]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (hdapp _ hr).trans (min_le_left _ _)
    · rw [(𝓣).extNorm_ofAll]
      exact hGnorm r r.2.1 r.2.2
  · have hradA : (0 : ℝ) < radA p := radA_pos
    have e1 : gn ℂ_[p] p (radA p) s = gaussNorm ((𝓣).coeffB S) (radA p) := by
      rw [gn, hs]
    rw [e1]
    refine (convergesAt_of_norm_le hradA ((𝓣).norm_coeffB_smallPart_le zero_lt_one d)
      (hd _ hradA radA_lt_one)).2.trans ?_
    have e2 : gaussNorm ((𝓣).coeffB d) (radA p) =
        (𝓣).extNorm b ⟨radA p, radA_pos, hradA_b⟩ ((𝓣).ofAll d hd b) :=
      ((𝓣).extNorm_ofAll hd (σ := b) ⟨radA p, radA_pos, hradA_b⟩).symm
    rw [e2]
    have e3 : (𝓣).ofAll d hd b = rep hx b + -(rep hx b - (𝓣).ofAll d hd b) := by ring
    rw [e3]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le_max ?_ ?_)
    · rw [extNorm_rep]
    · rw [(𝓣).extNorm_neg]
      exact (hdapp _ le_rfl).trans ((min_le_right _ _).trans hck1)

end WABridge

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma Laurent ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

variable (p) in

def ainfToBCrisPlus : AInf ℂ_[p] p →+* BCrisPlus ℂ_[p] p :=
  (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)).comp (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p))

theorem iotaPlus_ainfToBCrisPlus (a : AInf ℂ_[p] p) :
    iotaPlus ℂ_[p] p (ainfToBCrisPlus p a) =
      toBDeRhamPlus (normInteger ℂ_[p]) p (algebraMap _ 𝔸 a) := by
  rw [ainfToBCrisPlus, RingHom.comp_apply, iotaPlus_algebraMap, iota_algebraMap]
  rfl

variable (p) in

abbrev pInv : BCrisPlus ℂ_[p] p := IsLocalization.Away.invSelf (p : ACris ℂ_[p] p)

theorem natCast_mul_pInv : (p : BCrisPlus ℂ_[p] p) * pInv p = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)
  rwa [map_natCast] at h

theorem iotaPlus_pInv_mul : iotaPlus ℂ_[p] p (pInv p) * (p : 𝔹) = 1 := by
  rw [← map_natCast (iotaPlus ℂ_[p] p), ← map_mul, mul_comm, natCast_mul_pInv, map_one]

set_option maxHeartbeats 1000000 in
theorem phiPlus_pInv : phiPlus ℂ_[p] p (pInv p) = pInv p := by
  have h0 : algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) * pInv p = 1 :=
    IsLocalization.Away.mul_invSelf (p : ACris ℂ_[p] p)
  have hφP : phiPlus ℂ_[p] p (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)) =
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) := by
    rw [phiPlus_algebraMap, phi_natCast_p]
  have h1 : phiPlus ℂ_[p] p (pInv p) *
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) = 1 := by
    conv_lhs => rw [← hφP]
    rw [← map_mul, mul_comm, h0, map_one]
  calc phiPlus ℂ_[p] p (pInv p) = phiPlus ℂ_[p] p (pInv p) *
        (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p) * pInv p) := by
        rw [h0, mul_one]
    _ = pInv p := by rw [← mul_assoc, h1, one_mul]

theorem iotaPlus_div_eq {c : ACris ℂ_[p] p} {j : ℕ} {x : 𝔹}
    (h : (p : 𝔹) ^ j * x = ACris.iota ℂ_[p] p c) :
    iotaPlus ℂ_[p] p (algebraMap _ (BCrisPlus ℂ_[p] p) c * pInv p ^ j) = x := by
  rw [map_mul, map_pow, iotaPlus_algebraMap, ← h, mul_comm ((p : 𝔹) ^ j) x, mul_assoc, ← mul_pow,
    mul_comm (p : 𝔹), iotaPlus_pInv_mul, one_pow, mul_one]

theorem pow_mul_pUnit_neg (j : ℕ) :
    (p : 𝔸) ^ j * ((pUnit p ^ (-(j : ℤ)) : 𝔸ˣ) : 𝔸) = 1 := by
  have e : (p : 𝔸) ^ j = ((pUnit p ^ (j : ℤ) : 𝔸ˣ) : 𝔸) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit, map_natCast]
  rw [e, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]

theorem pow_mul_mem_acrisZero {z : 𝔸} {j : ℕ}
    (hz : gn ℂ_[p] p (radA p) z ≤ radA p ^ (-(j : ℤ))) : (p : 𝔸) ^ j * z ∈ ACrisZero ℂ_[p] p := by
  obtain ⟨c, hc, rfl⟩ := exists_eq_zpow_mul_of_gn_le hz
  rw [← mul_assoc, pow_mul_pUnit_neg, one_mul]
  exact hc

theorem exists_pow_mul_eq {z : 𝔸} {j N : ℕ} (hz : gn ℂ_[p] p (radA p) z ≤ radA p ^ N) :
    ∃ d ∈ ACrisZero ℂ_[p] p, (p : 𝔸) ^ j * z = (p : 𝔸) ^ N * d := by
  have h : gn ℂ_[p] p (radA p) ((p : 𝔸) ^ j * z) ≤ radA p ^ (N : ℤ) := by
    rw [gn_mul (K := ℂ_[p]) (p := p) radA_pos radA_lt_one, gn_pow (K := ℂ_[p]) (p := p) radA_pos
      radA_lt_one, gn_radA_natCast_p, zpow_natCast]
    exact (mul_le_of_le_one_left (gn_nonneg (K := ℂ_[p]) (p := p) radA_pos _)
      (pow_le_one₀ radA_pos.le radA_lt_one.le)).trans hz
  obtain ⟨d, hd, he⟩ := exists_eq_zpow_mul_of_gn_le h
  refine ⟨d, hd, ?_⟩
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit, map_natCast]

theorem radA_pow_le (N : ℕ) : radA p ^ N ≤ (p : ℝ) ^ (-(N : ℤ)) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ radA_pos.le radA_lt_inv_p.le N

set_option maxHeartbeats 4000000 in

theorem exists_bCrisPlus {m : ℕ} (C : Matrix (Fin m) (Fin m) (AInf ℂ_[p] p))
    (y : Fin m → (𝓣).RobbaTilde)
    (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) =
      ∑ j, (p : (𝓣).RobbaTilde) * ainfTilde p (C i j) * y j) :
    (∀ (i : Fin m) (ρ : Set.Ioo (0 : ℝ) 1), ∃ z : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ z = y i) ∧
    ∃ b : Fin m → BCrisPlus ℂ_[p] p,
      (∀ (i : Fin m) (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (z : (𝓣).RobbaExt ρ),
        (𝓣).ofRad ρ z = y i → iotaPlus ℂ_[p] p (b i) = iota p hρ z) ∧
      ∀ i, phiPlus ℂ_[p] p (b i) = ∑ j, (p : BCrisPlus ℂ_[p] p) * ainfToBCrisPlus p (C i j) * b j := by
  have ha : ∀ i, y i ∈ allRad p :=
    mem_allRad_of_tildeFrob_eq (fun i j => (p : (𝓣).RobbaTilde) * ainfTilde p (C i j))
      (fun i j => Subring.mul_mem _ (natCast_mem _ p) (ainfTilde_mem_allRad _)) y hy
  refine ⟨fun i ρ => mem_allRad.1 (ha i) ρ, ?_⟩

  set M : ℝ := 1 + ∑ j, tn (ha j) (radC p) with hMdef
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => tn_nonneg _ _)
  have hdec : ∀ i (k : ℕ), tn (ha i) ((frob ℂ_[p] p).rootRadius^[k] (radC p)) ^ (p ^ k) ≤
      ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) ^ k * M := by
    intro i k
    obtain ⟨j, hj⟩ := exists_tn_pow_pow_le C hy ha k i ((frob ℂ_[p] p).rootRadius^[k] (radC p))
    rw [iterate_powRadius_rootRadius] at hj
    have e : (((frob ℂ_[p] p).rootRadius^[k] (radC p) : Set.Ioo (0 : ℝ) 1) : ℝ) ^ (k * p ^ k) =
        ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) ^ k := by
      rw [mul_comm, pow_mul, pow_iterate_rootRadius]
    rw [e] at hj
    refine hj.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (radC p).2.1.le _))
    exact (Finset.single_le_sum (f := fun j => tn (ha j) (radC p)) (fun j _ => tn_nonneg _ _)
      (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

  choose s hs1 hs2 using fun i (N : ℕ) => exists_approx (ha i) hM (hdec i) (pow_pos (radA_pos (p := p)) N)
  have hY : ∀ i, ∃ j₀ : ℕ, max (tn (ha i) ⟨radA p, radA_pos, radA_lt_one⟩) 1 ≤
      radA p ^ (-(j₀ : ℤ)) := by
    intro i
    set Y := max (tn (ha i) ⟨radA p, radA_pos (p := p), radA_lt_one (p := p)⟩) 1
    have hY0 : 0 < Y := zero_lt_one.trans_le (le_max_right _ _)
    obtain ⟨j₀, hj₀⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hY0) (radA_lt_one (p := p))
    refine ⟨j₀, ?_⟩
    rw [zpow_neg, zpow_natCast]
    exact (le_inv_comm₀ (pow_pos radA_pos j₀) hY0).1 hj₀.le
  choose j₀ hj₀ using hY
  have hmem : ∀ i N, (p : 𝔸) ^ j₀ i * s i N ∈ ACrisZero ℂ_[p] p :=
    fun i N => pow_mul_mem_acrisZero ((hs2 i N).trans (hj₀ i))
  have hrA : radA p ≤ ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) := radA_lt_radTwo.le
  have hdiff : ∀ i (N N' : ℕ), N ≤ N' → gn ℂ_[p] p (radA p) (s i N - s i N') ≤ radA p ^ N := by
    intro i N N' hNN'
    have e1 := extNorm_awayToExt (radTwo p) ⟨radA p, radA_pos, hrA⟩ (s i N - s i N')
    have e2 : awayToExt p (radTwo p) (s i N - s i N') =
        (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N')) -
          (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N)) := by
      rw [map_sub]; ring
    rw [← e1, e2, sub_eq_add_neg]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (hs1 i N' _ le_rfl).trans (pow_le_pow_of_le_one radA_pos.le radA_lt_one.le hNN')
    · rw [(𝓣).extNorm_neg]; exact hs1 i N _ le_rfl

  have hlim : ∀ i, ∃ c : ACris ℂ_[p] p, ∀ N, ∃ d : ACris ℂ_[p] p,
      c - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem i N⟩ =
        (p : ACris ℂ_[p] p) ^ N * d := by
    intro i
    refine exists_limit (fun N => ⟨_, hmem i N⟩) fun N N' hNN' => ?_
    obtain ⟨d, hd, he⟩ := exists_pow_mul_eq (j := j₀ i) (hdiff i N N' hNN')
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow]
    rw [← mul_sub, he]
    simp
  choose c hc using hlim

  have hρ₂ : (p : ℝ)⁻¹ < ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) := inv_p_lt_radTwo
  have hR0 : ∀ N i, (𝓣).extNorm (radTwo p) (inversePRadius p hρ₂)
      (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N)) ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    fun N i => (hs1 i N _ radA_lt_inv_p.le).trans (radA_pow_le N)
  have hι : ∀ i, (p : 𝔹) ^ j₀ i * iota p hρ₂ (rep (ha i) (radTwo p)) = ACris.iota ℂ_[p] p (c i) :=
    fun i => pow_mul_iota_eq hρ₂ (j₀ i) (s i) (fun N => hR0 N i) (hmem i) (hc i)

  set σ := (frob ℂ_[p] p).powRadius (radTwo p) with hσ
  have hσρ : ((σ : Set.Ioo (0 : ℝ) 1) : ℝ) = rhoMid p :=
    congrArg Subtype.val ((frob ℂ_[p] p).powRadius_rootRadius (rhoMid p))
  have hρσ : (p : ℝ)⁻¹ < ((σ : Set.Ioo (0 : ℝ) 1) : ℝ) := by rw [hσρ]; exact inv_p_lt_rhoMid
  set r' : Set.Ioc (0 : ℝ) (radTwo p) := ⟨((p : ℝ)⁻¹) ^ ((p : ℝ)⁻¹),
    Real.rpow_pos_of_pos inv_p_pos _, by
      show ((p : ℝ)⁻¹) ^ ((p : ℝ)⁻¹) ≤ (((frob ℂ_[p] p).rootRadius (rhoMid p) :
        Set.Ioo (0 : ℝ) 1) : ℝ)
      rw [rootRadius_coe]
      exact Real.rpow_le_rpow inv_p_pos.le inv_p_lt_rhoMid.le (inv_pos.2 (Nat.cast_pos.2
        hp.out.pos)).le⟩ with hr'
  have hr'A : radA p ≤ (r' : ℝ) :=
    radA_lt_inv_p.le.trans (Real.self_le_rpow_of_le_one inv_p_pos.le inv_p_lt_one.le
      inv_p_lt_one.le)
  have hpowRad : (frob ℂ_[p] p).powRad r' = inversePRadius p hρσ := by
    apply Subtype.ext
    rw [TeichLift.TeichFrob.coe_powRad, frob_a, pow_one]
    exact Real.rpow_inv_natCast_pow inv_p_pos.le hp.out.ne_zero
  have hphiS : ∀ N i, awayToExt p σ (phiAway ℂ_[p] p (s i N)) =
      (frob ℂ_[p] p).extFrob (radTwo p) (awayToExt p (radTwo p) (s i N)) := by
    intro N i
    rw [awayToExt_eq_ofAll, awayToExt_eq_ofAll, TeichLift.TeichFrob.extFrob_ofAll]
    exact (𝓣).ofAll_congr _ _ (toB_phiAway _) _
  have hR0' : ∀ N i, (𝓣).extNorm σ (inversePRadius p hρσ)
      ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p)) -
        awayToExt p σ (phiAway ℂ_[p] p (s i N))) ≤ (p : ℝ) ^ (-(N : ℤ)) := by
    intro N i
    rw [hphiS, ← map_sub, ← hpowRad, TeichLift.TeichFrob.extNorm_extFrob, frob_a, pow_one]
    have h1 := hs1 i N r' hr'A
    have h2 : radA p ^ N ≤ 1 := pow_le_one₀ radA_pos.le radA_lt_one.le
    refine (pow_le_pow_left₀ ((𝓣).extNorm_nonneg _ _) h1 p).trans ?_
    refine (pow_le_of_le_one (pow_nonneg radA_pos.le _) h2 hp.out.ne_zero).trans ?_
    exact radA_pow_le N
  have hmem' : ∀ i N, (p : 𝔸) ^ j₀ i * phiAway ℂ_[p] p (s i N) ∈ ACrisZero ℂ_[p] p := by
    intro i N
    have e : (p : 𝔸) ^ j₀ i * phiAway ℂ_[p] p (s i N) = phiAway ℂ_[p] p ((p : 𝔸) ^ j₀ i * s i N) := by
      rw [map_mul, map_pow, map_natCast]
    rw [e]
    exact phiAway_mem (hmem i N)
  have hc' : ∀ i N, ∃ d : ACris ℂ_[p] p,
      ACris.phi ℂ_[p] p (c i) - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem' i N⟩ =
        (p : ACris ℂ_[p] p) ^ N * d := by
    intro i N
    obtain ⟨d, hd⟩ := hc i N
    refine ⟨ACris.phi ℂ_[p] p d, ?_⟩
    have e : algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem' i N⟩ =
        ACris.phi ℂ_[p] p (algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem i N⟩) := by
      rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, RingHom.id_apply, phi_of]
      congr 1
      apply Subtype.ext
      rw [coe_phiZero, map_mul, map_pow, map_natCast]
    rw [e, ← map_sub, hd, map_mul, map_pow, map_natCast]
  have hιφ : ∀ i, (p : 𝔹) ^ j₀ i *
      iota p hρσ ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p))) =
        ACris.iota ℂ_[p] p (ACris.phi ℂ_[p] p (c i)) :=
    fun i => pow_mul_iota_eq hρσ (j₀ i) (fun N => phiAway ℂ_[p] p (s i N))
      (fun N => hR0' N i) (hmem' i) (hc' i)

  refine ⟨fun i => algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i, ?_, ?_⟩
  · intro i ρ hρ z hz
    rw [iotaPlus_div_eq (hι i)]
    exact iota_eq_of_ofRad_eq hρ₂ hρ (by rw [ofRad_rep, hz])
  · intro i
    apply iotaPlus_injective
    have e1 : phiPlus ℂ_[p] p (algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i) =
        algebraMap _ (BCrisPlus ℂ_[p] p) (ACris.phi ℂ_[p] p (c i)) * pInv p ^ j₀ i := by
      rw [map_mul, map_pow, phiPlus_algebraMap, phiPlus_pInv]
    rw [e1, iotaPlus_div_eq (hιφ i), extFrob_rep C hy ha i (radTwo p), map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_natCast, iota_awayToExt, map_mul, map_mul, map_natCast,
      iotaPlus_ainfToBCrisPlus, iotaPlus_div_eq (hι j)]
    congr 1
    exact iota_eq_of_ofRad_eq hρσ hρ₂ (by rw [ofRad_rep, ofRad_rep])


end WABridge

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WABridge

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma Laurent ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

set_option maxHeartbeats 4000000 in

theorem exists_bCrisPlus_approx {m : ℕ} (C : Matrix (Fin m) (Fin m) (AInf ℂ_[p] p))
    (y : Fin m → (𝓣).RobbaTilde)
    (hy : ∀ i, (frob ℂ_[p] p).tildeFrob (y i) =
      ∑ j, (p : (𝓣).RobbaTilde) * ainfTilde p (C i j) * y j) :
    (∀ (i : Fin m) (ρ : Set.Ioo (0 : ℝ) 1), ∃ z : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ z = y i) ∧
    ∃ (b : Fin m → BCrisPlus ℂ_[p] p) (j₀ : Fin m → ℕ) (s : Fin m → ℕ → 𝔸)
      (c : Fin m → ACris ℂ_[p] p) (t : Fin m → ℕ → ACrisZero ℂ_[p] p),
      (∀ (i : Fin m) (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (z : (𝓣).RobbaExt ρ),
        (𝓣).ofRad ρ z = y i → iotaPlus ℂ_[p] p (b i) = iota p hρ z) ∧
      (∀ i, phiPlus ℂ_[p] p (b i) = ∑ j, (p : BCrisPlus ℂ_[p] p) * ainfToBCrisPlus p (C i j) * b j) ∧
      (∀ i N, ((t i N : ACrisZero ℂ_[p] p) : 𝔸) = (p : 𝔸) ^ j₀ i * s i N) ∧
      (∀ i N, ∃ d : ACris ℂ_[p] p,
        c i - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) (t i N) = (p : ACris ℂ_[p] p) ^ N * d) ∧
      (∀ i, b i = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i) ∧
      (∀ i N (ρ' : Set.Ioo (0 : ℝ) 1) (hρ' : ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ')
        (z : (𝓣).RobbaExt ρ'), (𝓣).ofRad ρ' z = y i →
        ∀ r : Set.Ioc (0 : ℝ) (radTwo p), radA p ≤ r →
          (𝓣).extNorm (radTwo p) r ((𝓣).res hρ' z - awayToExt p (radTwo p) (s i N)) ≤
            radA p ^ N) := by
  have ha : ∀ i, y i ∈ allRad p :=
    mem_allRad_of_tildeFrob_eq (fun i j => (p : (𝓣).RobbaTilde) * ainfTilde p (C i j))
      (fun i j => Subring.mul_mem _ (natCast_mem _ p) (ainfTilde_mem_allRad _)) y hy
  refine ⟨fun i ρ => mem_allRad.1 (ha i) ρ, ?_⟩

  set M : ℝ := 1 + ∑ j, tn (ha j) (radC p) with hMdef
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => tn_nonneg _ _)
  have hdec : ∀ i (k : ℕ), tn (ha i) ((frob ℂ_[p] p).rootRadius^[k] (radC p)) ^ (p ^ k) ≤
      ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) ^ k * M := by
    intro i k
    obtain ⟨j, hj⟩ := exists_tn_pow_pow_le C hy ha k i ((frob ℂ_[p] p).rootRadius^[k] (radC p))
    rw [iterate_powRadius_rootRadius] at hj
    have e : (((frob ℂ_[p] p).rootRadius^[k] (radC p) : Set.Ioo (0 : ℝ) 1) : ℝ) ^ (k * p ^ k) =
        ((radC p : Set.Ioo (0 : ℝ) 1) : ℝ) ^ k := by
      rw [mul_comm, pow_mul, pow_iterate_rootRadius]
    rw [e] at hj
    refine hj.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (radC p).2.1.le _))
    exact (Finset.single_le_sum (f := fun j => tn (ha j) (radC p)) (fun j _ => tn_nonneg _ _)
      (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

  choose s hs1 hs2 using fun i (N : ℕ) => exists_approx (ha i) hM (hdec i) (pow_pos (radA_pos (p := p)) N)
  have hY : ∀ i, ∃ j₀ : ℕ, max (tn (ha i) ⟨radA p, radA_pos, radA_lt_one⟩) 1 ≤
      radA p ^ (-(j₀ : ℤ)) := by
    intro i
    set Y := max (tn (ha i) ⟨radA p, radA_pos (p := p), radA_lt_one (p := p)⟩) 1
    have hY0 : 0 < Y := zero_lt_one.trans_le (le_max_right _ _)
    obtain ⟨j₀, hj₀⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hY0) (radA_lt_one (p := p))
    refine ⟨j₀, ?_⟩
    rw [zpow_neg, zpow_natCast]
    exact (le_inv_comm₀ (pow_pos radA_pos j₀) hY0).1 hj₀.le
  choose j₀ hj₀ using hY
  have hmem : ∀ i N, (p : 𝔸) ^ j₀ i * s i N ∈ ACrisZero ℂ_[p] p :=
    fun i N => pow_mul_mem_acrisZero ((hs2 i N).trans (hj₀ i))
  have hrA : radA p ≤ ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) := radA_lt_radTwo.le
  have hdiff : ∀ i (N N' : ℕ), N ≤ N' → gn ℂ_[p] p (radA p) (s i N - s i N') ≤ radA p ^ N := by
    intro i N N' hNN'
    have e1 := extNorm_awayToExt (radTwo p) ⟨radA p, radA_pos, hrA⟩ (s i N - s i N')
    have e2 : awayToExt p (radTwo p) (s i N - s i N') =
        (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N')) -
          (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N)) := by
      rw [map_sub]; ring
    rw [← e1, e2, sub_eq_add_neg]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (hs1 i N' _ le_rfl).trans (pow_le_pow_of_le_one radA_pos.le radA_lt_one.le hNN')
    · rw [(𝓣).extNorm_neg]; exact hs1 i N _ le_rfl

  have hlim : ∀ i, ∃ c : ACris ℂ_[p] p, ∀ N, ∃ d : ACris ℂ_[p] p,
      c - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem i N⟩ =
        (p : ACris ℂ_[p] p) ^ N * d := by
    intro i
    refine exists_limit (fun N => ⟨_, hmem i N⟩) fun N N' hNN' => ?_
    obtain ⟨d, hd, he⟩ := exists_pow_mul_eq (j := j₀ i) (hdiff i N N' hNN')
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow]
    rw [← mul_sub, he]
    simp
  choose c hc using hlim

  have hρ₂ : (p : ℝ)⁻¹ < ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) := inv_p_lt_radTwo
  have hR0 : ∀ N i, (𝓣).extNorm (radTwo p) (inversePRadius p hρ₂)
      (rep (ha i) (radTwo p) - awayToExt p (radTwo p) (s i N)) ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    fun N i => (hs1 i N _ radA_lt_inv_p.le).trans (radA_pow_le N)
  have hι : ∀ i, (p : 𝔹) ^ j₀ i * iota p hρ₂ (rep (ha i) (radTwo p)) = ACris.iota ℂ_[p] p (c i) :=
    fun i => pow_mul_iota_eq hρ₂ (j₀ i) (s i) (fun N => hR0 N i) (hmem i) (hc i)

  set σ := (frob ℂ_[p] p).powRadius (radTwo p) with hσ
  have hσρ : ((σ : Set.Ioo (0 : ℝ) 1) : ℝ) = rhoMid p :=
    congrArg Subtype.val ((frob ℂ_[p] p).powRadius_rootRadius (rhoMid p))
  have hρσ : (p : ℝ)⁻¹ < ((σ : Set.Ioo (0 : ℝ) 1) : ℝ) := by rw [hσρ]; exact inv_p_lt_rhoMid
  set r' : Set.Ioc (0 : ℝ) (radTwo p) := ⟨((p : ℝ)⁻¹) ^ ((p : ℝ)⁻¹),
    Real.rpow_pos_of_pos inv_p_pos _, by
      show ((p : ℝ)⁻¹) ^ ((p : ℝ)⁻¹) ≤ (((frob ℂ_[p] p).rootRadius (rhoMid p) :
        Set.Ioo (0 : ℝ) 1) : ℝ)
      rw [rootRadius_coe]
      exact Real.rpow_le_rpow inv_p_pos.le inv_p_lt_rhoMid.le (inv_pos.2 (Nat.cast_pos.2
        hp.out.pos)).le⟩ with hr'
  have hr'A : radA p ≤ (r' : ℝ) :=
    radA_lt_inv_p.le.trans (Real.self_le_rpow_of_le_one inv_p_pos.le inv_p_lt_one.le
      inv_p_lt_one.le)
  have hpowRad : (frob ℂ_[p] p).powRad r' = inversePRadius p hρσ := by
    apply Subtype.ext
    rw [TeichLift.TeichFrob.coe_powRad, frob_a, pow_one]
    exact Real.rpow_inv_natCast_pow inv_p_pos.le hp.out.ne_zero
  have hphiS : ∀ N i, awayToExt p σ (phiAway ℂ_[p] p (s i N)) =
      (frob ℂ_[p] p).extFrob (radTwo p) (awayToExt p (radTwo p) (s i N)) := by
    intro N i
    rw [awayToExt_eq_ofAll, awayToExt_eq_ofAll, TeichLift.TeichFrob.extFrob_ofAll]
    exact (𝓣).ofAll_congr _ _ (toB_phiAway _) _
  have hR0' : ∀ N i, (𝓣).extNorm σ (inversePRadius p hρσ)
      ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p)) -
        awayToExt p σ (phiAway ℂ_[p] p (s i N))) ≤ (p : ℝ) ^ (-(N : ℤ)) := by
    intro N i
    rw [hphiS, ← map_sub, ← hpowRad, TeichLift.TeichFrob.extNorm_extFrob, frob_a, pow_one]
    have h1 := hs1 i N r' hr'A
    have h2 : radA p ^ N ≤ 1 := pow_le_one₀ radA_pos.le radA_lt_one.le
    refine (pow_le_pow_left₀ ((𝓣).extNorm_nonneg _ _) h1 p).trans ?_
    refine (pow_le_of_le_one (pow_nonneg radA_pos.le _) h2 hp.out.ne_zero).trans ?_
    exact radA_pow_le N
  have hmem' : ∀ i N, (p : 𝔸) ^ j₀ i * phiAway ℂ_[p] p (s i N) ∈ ACrisZero ℂ_[p] p := by
    intro i N
    have e : (p : 𝔸) ^ j₀ i * phiAway ℂ_[p] p (s i N) = phiAway ℂ_[p] p ((p : 𝔸) ^ j₀ i * s i N) := by
      rw [map_mul, map_pow, map_natCast]
    rw [e]
    exact phiAway_mem (hmem i N)
  have hc' : ∀ i N, ∃ d : ACris ℂ_[p] p,
      ACris.phi ℂ_[p] p (c i) - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem' i N⟩ =
        (p : ACris ℂ_[p] p) ^ N * d := by
    intro i N
    obtain ⟨d, hd⟩ := hc i N
    refine ⟨ACris.phi ℂ_[p] p d, ?_⟩
    have e : algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem' i N⟩ =
        ACris.phi ℂ_[p] p (algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) ⟨_, hmem i N⟩) := by
      rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, RingHom.id_apply, phi_of]
      congr 1
      apply Subtype.ext
      rw [coe_phiZero, map_mul, map_pow, map_natCast]
    rw [e, ← map_sub, hd, map_mul, map_pow, map_natCast]
  have hιφ : ∀ i, (p : 𝔹) ^ j₀ i *
      iota p hρσ ((frob ℂ_[p] p).extFrob (radTwo p) (rep (ha i) (radTwo p))) =
        ACris.iota ℂ_[p] p (ACris.phi ℂ_[p] p (c i)) :=
    fun i => pow_mul_iota_eq hρσ (j₀ i) (fun N => phiAway ℂ_[p] p (s i N))
      (fun N => hR0' N i) (hmem' i) (hc' i)

  refine ⟨fun i => algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i, j₀, s, c,
    fun i N => ⟨_, hmem i N⟩, ?_, ?_, fun i N => rfl, hc, fun i => rfl, ?_⟩
  · intro i ρ hρ z hz
    rw [iotaPlus_div_eq (hι i)]
    exact iota_eq_of_ofRad_eq hρ₂ hρ (by rw [ofRad_rep, hz])
  · intro i
    apply iotaPlus_injective
    have e1 : phiPlus ℂ_[p] p (algebraMap _ (BCrisPlus ℂ_[p] p) (c i) * pInv p ^ j₀ i) =
        algebraMap _ (BCrisPlus ℂ_[p] p) (ACris.phi ℂ_[p] p (c i)) * pInv p ^ j₀ i := by
      rw [map_mul, map_pow, phiPlus_algebraMap, phiPlus_pInv]
    rw [e1, iotaPlus_div_eq (hιφ i), extFrob_rep C hy ha i (radTwo p), map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_natCast, iota_awayToExt, map_mul, map_mul, map_natCast,
      iotaPlus_ainfToBCrisPlus, iotaPlus_div_eq (hι j)]
    congr 1
    exact iota_eq_of_ofRad_eq hρσ hρ₂ (by rw [ofRad_rep, ofRad_rep])
  · intro i N ρ' hρ' z hz r hr
    have e : (𝓣).res hρ' z = rep (ha i) (radTwo p) :=
      (𝓣).ofRad_injective (radTwo p) (by rw [(𝓣).ofRad_res, hz, ofRad_rep])
    rw [e]
    exact hs1 i N r hr

set_option maxHeartbeats 1000000 in

theorem exists_bCrisPlus_approx_single (k : ℕ) (y : (𝓣).RobbaTilde)
    (hy : (frob ℂ_[p] p).tildeFrob y = (p : (𝓣).RobbaTilde) ^ (k + 1) * y) :
    (∀ ρ : Set.Ioo (0 : ℝ) 1, ∃ z : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ z = y) ∧
    ∃ (b : BCrisPlus ℂ_[p] p) (j₀ : ℕ) (s : ℕ → 𝔸) (c : ACris ℂ_[p] p) (t : ℕ → ACrisZero ℂ_[p] p),
      (∀ (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (z : (𝓣).RobbaExt ρ),
        (𝓣).ofRad ρ z = y → iotaPlus ℂ_[p] p b = iota p hρ z) ∧
      phiPlus ℂ_[p] p b = (p : BCrisPlus ℂ_[p] p) ^ (k + 1) * b ∧
      (∀ N, ((t N : ACrisZero ℂ_[p] p) : 𝔸) = (p : 𝔸) ^ j₀ * s N) ∧
      (∀ N, ∃ d : ACris ℂ_[p] p,
        c - algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p) (t N) = (p : ACris ℂ_[p] p) ^ N * d) ∧
      b = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) c * pInv p ^ j₀ ∧
      (∀ N (ρ' : Set.Ioo (0 : ℝ) 1) (hρ' : ((radTwo p : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ')
        (z : (𝓣).RobbaExt ρ'), (𝓣).ofRad ρ' z = y →
        ∀ r : Set.Ioc (0 : ℝ) (radTwo p), radA p ≤ r →
          (𝓣).extNorm (radTwo p) r ((𝓣).res hρ' z - awayToExt p (radTwo p) (s N)) ≤ radA p ^ N) := by
  have hy' : ∀ i : Fin 1, (frob ℂ_[p] p).tildeFrob ((fun _ => y) i) =
      ∑ j, (p : (𝓣).RobbaTilde) * ainfTilde p ((fun _ _ => (p : AInf ℂ_[p] p) ^ k :
        Matrix (Fin 1) (Fin 1) (AInf ℂ_[p] p)) i j) * (fun _ => y) j := by
    intro i
    rw [Fin.sum_univ_one, map_pow, map_natCast, hy]
    ring
  obtain ⟨hext, b, j₀, s, c, t, hι, hφ, ht, hc, hb, happ⟩ := exists_bCrisPlus_approx _ _ hy'
  refine ⟨hext 0, b 0, j₀ 0, s 0, c 0, t 0, hι 0, ?_, ht 0, hc 0, hb 0, happ 0⟩
  rw [hφ 0, Fin.sum_univ_one, map_pow, map_natCast]
  ring

end WABridge

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

section Abstract

variable {G R F : Type*} [Group G] [CommRing R] [IsDomain R] [CommRing F]

theorem isUnit_of_eigen_of_finiteIndex (A : G → R →+* R) (hA1 : A 1 = RingHom.id R)
    (hAmul : ∀ g h, A (g * h) = (A g).comp (A h)) (s : F →+* R) (hAs : ∀ g c, A g (s c) = s c)
    (hunit : ∀ x : R, x ≠ 0 → (∀ g, ∃ c, A g x = s c * x) → IsUnit x)
    (H : Subgroup G) [H.FiniteIndex] {b : R} (hb0 : b ≠ 0) (hb : ∀ σ ∈ H, ∃ c, A σ b = s c * b) :
    IsUnit b := by
  classical
  have hinj : ∀ σ, Function.Injective (A σ) := fun σ x y h => by
    have e : ∀ z, A σ⁻¹ (A σ z) = z := fun z => by
      rw [← RingHom.comp_apply, ← hAmul, inv_mul_cancel, hA1, RingHom.id_apply]
    rw [← e x, ← e y, h]
  set N := H.normalCore with hNdef
  let _ : Fintype (G ⧸ N) := Fintype.ofFinite _
  choose! lam hlam using hb
  have hN : ∀ n ∈ N, A n b = s (lam n) * b := fun n hn => hlam n (H.normalCore_le hn)
  set f : G ⧸ N → R := fun q => A q.out b with hf
  set P : R := ∏ q, f q with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ h =>
    hb0 (hinj _ (by rw [map_zero]; exact h))
  have key : ∀ (g : G) (q : G ⧸ N),
      A g (f q) = s (lam (((g : G ⧸ N) * q).out⁻¹ * (g * q.out))) * f ((g : G ⧸ N) * q) := by
    intro g q
    set q' := (g : G ⧸ N) * q
    have hmem : q'.out⁻¹ * (g * q.out) ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have e : g * q.out = q'.out * (q'.out⁻¹ * (g * q.out)) := by group
    simp only [hf]
    rw [← RingHom.comp_apply, ← hAmul, e, hAmul, RingHom.comp_apply, hN _ hmem, map_mul, hAs,
      mul_inv_cancel_left]
  have hPeig : ∀ g : G, ∃ c, A g P = s c * P := by
    intro g
    refine ⟨∏ q : G ⧸ N, lam (((g : G ⧸ N) * q).out⁻¹ * (g * q.out)), ?_⟩
    rw [hP, map_prod]
    simp only [key]
    rw [Finset.prod_mul_distrib, map_prod]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft (g : G ⧸ N)) _ _ fun q => rfl
  have hPu : IsUnit P := hunit P hP0 hPeig
  have h1 : (1 : G ⧸ N).out ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  have hdvd : b ∣ P := by
    have h2 : f 1 ∣ P := Finset.dvd_prod_of_mem f (Finset.mem_univ 1)
    have h3 : f 1 = s (lam (1 : G ⧸ N).out) * b := hN _ h1
    rw [h3] at h2
    exact (Dvd.intro_left _ rfl).trans h2
  exact isUnit_of_dvd_unit hdvd hPu

end Abstract

variable {p : ℕ} [hp : Fact p.Prime]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

include hζ in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isUnit_of_galB_eigen_of_finiteIndex [FiniteDimensional ℚ_[p] K]
    (H : Subgroup Gal(PadicAlgCl p/K)) [H.FiniteIndex] {b : BCris hε} (hb0 : b ≠ 0)
    (hb : ∀ σ ∈ H, ∃ q : ℚ_[p], galB hε σ b = algebraMap ℚ_[p] (BCris hε) q * b) : IsUnit b :=
  letI := isDomain_bCris hε hζ
  isUnit_of_eigen_of_finiteIndex (galB hε) (galB_one hε) (galB_mul hε) (algebraMap ℚ_[p] (BCris hε))
    (galB_algebraMap_padic hε) (fun _ hx h => isUnit_of_galB_eigen hε hζ hx h) H hb0 hb

end ACris

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WABridge WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

theorem radA_le_inv_p : radA p ≤ (p : ℝ)⁻¹ := radA_lt_inv_p.le

theorem bcrisToAnn_pInv_mul {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0} (hσ : (p : ℝ)⁻¹ ≤ σ0) :
    bcrisToAnn hσ (pInv p) * (p : (𝓣).Ann ρ0 σ0) = 1 := by
  have h := congrArg (bcrisToAnn hσ) (natCast_mul_pInv (p := p))
  rw [map_mul, map_natCast, map_one] at h
  rw [mul_comm]; exact h

set_option maxHeartbeats 3200000 in

theorem exists_bCrisPlus_ann (k : ℕ) (y : (𝓣).RobbaTilde)
    (hy : (frob ℂ_[p] p).tildeFrob y = (p : (𝓣).RobbaTilde) ^ (k + 1) * y) :
    (∀ ρ : Set.Ioo (0 : ℝ) 1, ∃ z : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ z = y) ∧
    ∃ b : BCrisPlus ℂ_[p] p, phiPlus ℂ_[p] p b = (p : BCrisPlus ℂ_[p] p) ^ (k + 1) * b ∧
      (∀ (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (z : (𝓣).RobbaExt ρ),
        (𝓣).ofRad ρ z = y → iotaPlus ℂ_[p] p b = iota p hρ z) ∧
      ∀ (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0) (hσ : (p : ℝ)⁻¹ ≤ σ0)
        (_ : (ρ0 : ℝ) ≤ radTwo p) (ρ' : Set.Ioo (0 : ℝ) 1) (hρ' : (ρ0 : ℝ) ≤ ρ') (z : (𝓣).RobbaExt ρ'),
        (𝓣).ofRad ρ' z = y → bcrisToAnn hσ b = (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' z) := by
  obtain ⟨hext, b, j₀, s, c, t, hι, hφ, ht, hc, hb, happ⟩ := exists_bCrisPlus_approx_single k y hy
  refine ⟨hext, b, hφ, hι, fun ρ0 σ0 hσ h0 ρ' hρ' z hz => ?_⟩
  obtain ⟨z₂, hz₂⟩ := hext (radTwo p)
  have hres : (𝓣).res hρ' z = (𝓣).res h0 z₂ :=
    (𝓣).ofRad_injective ρ0 (by rw [(𝓣).ofRad_res, (𝓣).ofRad_res, hz, hz₂])
  set Z : (𝓣).Ann ρ0 σ0 := (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' z) with hZ

  have hcZ : (p : (𝓣).Ann ρ0 σ0) ^ j₀ * Z = acrisToAnn hσ c := by
    refine eq_acrisToAnn hσ fun N => ⟨t N, ?_, fun r => ?_⟩
    · obtain ⟨d, hd⟩ := hc N
      rw [hd]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rw [ht N, map_mul, map_pow, map_natCast, ← mul_sub, (𝓣).annNorm_mul, (𝓣).annNorm_pow,
        annNorm_awayToAnn_natCast_p]
      have hr0 : (0 : ℝ) ≤ r := (rad_pos' r).le
      have hr1 : (r : ℝ) ^ j₀ ≤ 1 := pow_le_one₀ hr0 (rad_lt_one' r).le
      refine (mul_le_of_le_one_left ((𝓣).annNorm_nonneg _ _) hr1).trans ?_
      rw [hZ, awayToAnn_eq_toAnn, ← map_sub, (𝓣).annNorm_toAnn, hres]
      have hrT : (r : ℝ) ≤ radTwo p := r.2.2.trans h0
      have hrA : radA p ≤ (r : ℝ) := radA_le_inv_p.trans (hσ.trans r.2.1)
      have e1 : (𝓣).res h0 z₂ - awayToExt p ρ0 (s N) =
          (𝓣).res h0 ((𝓣).res (le_refl _) z₂ - awayToExt p (radTwo p) (s N)) := by
        rw [map_sub, (𝓣).res_res, res_awayToExt]
      rw [e1, (𝓣).extNorm_res]
      refine (happ N (radTwo p) le_rfl z₂ hz₂ ⟨r, (rad_pos' r), hrT⟩ hrA).trans ?_
      exact pow_le_pow_left₀ (radA_pos (p := p)).le (radA_le_inv_p.trans (hσ.trans σ0.2.2)) N
  rw [hb, map_mul, map_pow, bcrisToAnn_algebraMap, ← hcZ]
  calc (p : (𝓣).Ann ρ0 σ0) ^ j₀ * Z * bcrisToAnn hσ (pInv p) ^ j₀
      = Z * (bcrisToAnn hσ (pInv p) * (p : (𝓣).Ann ρ0 σ0)) ^ j₀ := by ring
    _ = Z := by rw [bcrisToAnn_pInv_mul, one_pow, mul_one]

section T

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hε hζ in
set_option maxHeartbeats 1600000 in

theorem bcrisToAnn_periodTPlus {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0} (hσ : (p : ℝ)⁻¹ ≤ σ0)
    (h0 : (ρ0 : ℝ) ≤ radTwo p) {ρ' : Set.Ioo (0 : ℝ) 1} (hρ' : (ρ0 : ℝ) ≤ ρ') (w : (𝓣).RobbaExt ρ')
    (hw : (𝓣).ofRad ρ' w = tTilde p ε) :
    bcrisToAnn hσ (periodTPlus hε) = (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' w) := by
  have hy : (frob ℂ_[p] p).tildeFrob (tTilde p ε) = (p : (𝓣).RobbaTilde) ^ (0 + 1) * tTilde p ε := by
    rw [zero_add, pow_one]; exact tildeFrob_tTilde hε hζ
  obtain ⟨-, b, -, hι, hann⟩ := exists_bCrisPlus_ann 0 (tTilde p ε) hy
  have hbt : b = periodTPlus hε := by
    apply iotaPlus_injective (K := ℂ_[p]) (p := p)
    rw [hι (rhoMid p) inv_p_lt_rhoMid (tTildeExt p ε (rhoMid p)) (ofRad_tTildeExt hε hζ (rhoMid p)),
      iotaPlus_periodTPlus, ← iotaTildeFun_ofRad inv_p_lt_rhoMid, ofRad_tTildeExt hε hζ,
      iotaTildeFun_tTilde hε hζ]
  rw [← hbt]
  exact hann ρ0 σ0 hσ h0 ρ' hρ' w hw

end T

theorem exists_mul_eq_pow_of_isUnit {R S : Type*} [CommRing R] [CommRing S] {t : R} [Algebra R S]
    [IsLocalization.Away t S] (hinj : Function.Injective (algebraMap R S)) {b : R}
    (hb : IsUnit (algebraMap R S b)) : ∃ (δ : R) (M : ℕ), b * δ = t ^ M := by
  obtain ⟨u, hu⟩ := hb.exists_right_inv
  obtain ⟨⟨δ, s⟩, hδ⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) u
  obtain ⟨M, hM⟩ := s.2
  simp only at hδ
  refine ⟨δ, M, hinj ?_⟩
  have hspec := IsLocalization.mk'_spec S δ s
  rw [map_mul, ← hspec, ← mul_assoc, hδ, hu, one_mul, ← (show t ^ M = (s : R) from hM)]

set_option maxHeartbeats 1600000 in
theorem galB_algebraMap_eq_of_smul_eq {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/K)) {b : BCrisPlus ℂ_[p] p}
    {q : ℚ_[p]} (h : σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b) :
    galB hε σ (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) b) =
      algebraMap ℚ_[p] (BCris hε) q * algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) b :=
  (galB_algebraMap hε σ b).trans ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) h).trans
    (map_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) _ b))

section LemmaO

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)
  {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

set_option maxHeartbeats 1600000 in

theorem galPlus_eq_of_tildeMap {z : (𝓣).RobbaTilde} {b : BCrisPlus ℂ_[p] p}
    (hι : ∀ (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (p : ℝ)⁻¹ < ρ) (w : (𝓣).RobbaExt ρ),
      (𝓣).ofRad ρ w = z → iotaPlus ℂ_[p] p b = iota p hρ w)
    (hz : ∃ w : (𝓣).RobbaExt (rhoMid p), (𝓣).ofRad (rhoMid p) w = z)
    (σ : Gal(PadicAlgCl p/K)) {q : ℚ_[p]} (hq : (galIso σ).tildeMap z = padicToTilde p q * z) :
    σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b := by
  obtain ⟨w, hw⟩ := hz
  apply iotaPlus_injective (K := ℂ_[p]) (p := p)
  rw [iotaPlus_gal_smul, map_mul, iotaPlus_algebraMap_padic, hι (rhoMid p) inv_p_lt_rhoMid w hw,
    ← iota_extMap inv_p_lt_rhoMid σ w]
  have e : (galIso σ).extMap (rhoMid p) w =
      awayToExt p (rhoMid p) (wittFpbarToAway p (padicToWFrac p q)) * w := by
    apply (𝓣).ofRad_injective (rhoMid p)
    rw [← TeichLift.TeichIso.tildeMap_ofRad, hw, hq, map_mul, ← padicToTilde_eq_ofRad, hw]
  rw [e, map_mul, iota_awayToExt_padic]

include hζ in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_mul_eq_periodTPlus_pow [FiniteDimensional ℚ_[p] K] (H : Subgroup Gal(PadicAlgCl p/K))
    [H.FiniteIndex] {b : BCrisPlus ℂ_[p] p} (hb0 : b ≠ 0)
    (hbH : ∀ σ ∈ H, ∃ q : ℚ_[p], σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b) :
    ∃ (δ : BCrisPlus ℂ_[p] p) (M : ℕ), b * δ = periodTPlus hε ^ M := by
  have hinj : Function.Injective (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) :=
    algebraMap_bCrisPlus_bCris_injective hε hζ
  have hbu := isUnit_of_galB_eigen_of_finiteIndex hε hζ H
    (fun h => hb0 (hinj (by rw [h, map_zero])))
    (fun σ hσ => (hbH σ hσ).imp fun q hq => galB_algebraMap_eq_of_smul_eq hε σ hq)
  exact exists_mul_eq_pow_of_isUnit (R := BCrisPlus ℂ_[p] p) (S := BCris hε) (t := periodTPlus hε) hinj hbu

include hζ in
set_option maxHeartbeats 1600000 in

theorem ptEval_tTilde_eq_zero_of_dvd {ξ' : (𝓣).int} (hξ' : (𝓣).IsPrimOne ξ')
    (hr0 : (p : ℝ)⁻¹ ≤ (𝓣).ptRad ξ') (hr1 : (𝓣).ptRad ξ' ≤ radTwo p)
    {b δ : BCrisPlus ℂ_[p] p} {M : ℕ} (hδ : b * δ = periodTPlus hε ^ M)
    (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (𝓣).ptRad ξ' < ρ) {zρ : (𝓣).RobbaExt ρ}
    (hbz : ∀ (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0) (hσ : (p : ℝ)⁻¹ ≤ σ0),
      (ρ0 : ℝ) ≤ radTwo p → ∀ (hρ' : (ρ0 : ℝ) ≤ ρ), bcrisToAnn hσ b = (𝓣).toAnn ρ0 σ0 ((𝓣).res hρ' zρ))
    (hzvan : (𝓣).ptEval hξ' hρ.le zρ = 0) (w : (𝓣).RobbaExt ρ) (hw : (𝓣).ofRad ρ w = tTilde p ε) :
    (𝓣).ptEval hξ' hρ.le w = 0 := by
  have hr0' : 0 < (𝓣).ptRad ξ' := (𝓣).ptRad_pos' hξ'
  let ρA : Set.Ioo (0 : ℝ) 1 := ⟨(𝓣).ptRad ξ', hr0', (𝓣).ptRad_lt_one' hξ'⟩
  let σA : Set.Ioc (0 : ℝ) ρA := ⟨(𝓣).ptRad ξ', hr0', le_rfl⟩
  have hσA : (p : ℝ)⁻¹ ≤ σA := hr0
  have hA : (ρA : ℝ) ≤ radTwo p := hr1
  have hmem : (𝓣).ptRad ξ' ∈ Set.Icc (σA : ℝ) ρA := ⟨le_rfl, le_rfl⟩
  have hρA : (ρA : ℝ) ≤ ρ := hρ.le
  have hev : ∀ x : (𝓣).RobbaExt ρ, (𝓣).annEval hξ' hmem ((𝓣).toAnn ρA σA ((𝓣).res hρA x)) =
      (𝓣).ptEval hξ' hρ.le x := fun x => by
    rw [(𝓣).annEval_toAnn, (𝓣).ptEval_res]
  have hb_ev : (𝓣).annEval hξ' hmem (bcrisToAnn hσA b) = 0 := by
    rw [hbz ρA σA hσA hA hρA, hev, hzvan]
  have h1 := congrArg (fun x => (𝓣).annEval hξ' hmem (bcrisToAnn hσA x)) hδ
  simp only [map_mul, map_pow, hb_ev, zero_mul] at h1
  have h2 : (𝓣).annEval hξ' hmem (bcrisToAnn hσA (periodTPlus hε)) = 0 :=
    (pow_eq_zero_iff'.1 h1.symm).1
  rw [bcrisToAnn_periodTPlus hε hζ hσA hA hρA w hw, hev] at h2
  exact h2

include hε hζ in
set_option maxHeartbeats 1600000 in

theorem ptEval_tTilde_eq_zero_of_fixed [FiniteDimensional ℚ_[p] K] (H : Subgroup Gal(PadicAlgCl p/K))
    [H.FiniteIndex] {ξ' : (𝓣).int} (hξ' : (𝓣).IsPrimOne ξ') (hr0 : (p : ℝ)⁻¹ ≤ (𝓣).ptRad ξ')
    (hr1 : (𝓣).ptRad ξ' ≤ radTwo p)
    (hfix : ∀ σ ∈ H, ∃ u : (𝓣).int, IsUnit u ∧ ((galIso σ).ψ ξ' : WC p) = u * ξ')
    (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (𝓣).ptRad ξ' < ρ) (w : (𝓣).RobbaExt ρ)
    (hw : (𝓣).ofRad ρ w = tTilde p ε) :
    (𝓣).ptEval hξ' hρ.le w = 0 := by
  obtain ⟨k, z, hz0, hφz, hHz, hzall, hzvan⟩ := exists_eigen_vanishing hε hζ H hξ' hfix
  obtain ⟨-, b, -, hι, hann⟩ := exists_bCrisPlus_ann k z hφz
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨w₀, hw₀⟩ := hzall (rhoMid p)
    have h := hι (rhoMid p) inv_p_lt_rhoMid w₀ hw₀
    rw [map_zero] at h
    have : w₀ = 0 := iota_injective inv_p_lt_rhoMid (by rw [← h, map_zero])
    rw [this, map_zero] at hw₀
    exact hz0 hw₀.symm
  have hbH : ∀ σ ∈ H, ∃ q : ℚ_[p], σ • b = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * b := fun σ hσ =>
    (hHz σ hσ).imp fun q hq => galPlus_eq_of_tildeMap hι (hzall (rhoMid p)) σ hq.2
  obtain ⟨δ, M, hδ⟩ := exists_mul_eq_periodTPlus_pow hε hζ H hb0 hbH
  obtain ⟨zρ, hzρ⟩ := hzall ρ
  exact ptEval_tTilde_eq_zero_of_dvd hε hζ hξ' hr0 hr1 hδ ρ hρ
    (fun ρ0 σ0 hσ h0 hρ' => hann ρ0 σ0 hσ h0 ρ hρ' zρ hzρ) (hzvan ρ hρ zρ hzρ) w hw

end LemmaO

end WAFrac

end GroundTheory.PAdicHodge
end
end
