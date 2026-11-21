import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.Columns.TiedValLat
import Formalism.LocalToGlobal.Columns.TiedVal
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.TiedAtT
import Formalism.LocalToGlobal.Columns.TiedValBwG
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P Formalism.L2.Forms
open Formalism.L2.DIV (Pl kP St redAt redFn resS)

section Law

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {n : ℕ} [NeZero n] (ST SG : Finset (Pl E))

theorem vdil_decoRaw_mul (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hk : k ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (c : DiaG E ST)
    (hrow : ∀ (P : ST) (j : Fin n), ((redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P.1 ⟨k, hk⟩ : GL (Fin n) (kP P.1)) :
      Matrix (Fin n) (Fin n) (kP P.1)) (lastIdx n) j = if j = lastIdx n then (c P).1 else 0)
    (hSG : ∀ w : SG, redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ⟨k, hk⟩ = 1) :
    decoRaw ST SG (x * k⁻¹) = (decoRaw ST SG x).dia c := by
  obtain ⟨y, hyk, hyr⟩ := St_one_int hk
  have hN := globLat_mul_St n x hk
  have hval : ∀ (P : Pl E) (v : Fin n → E), v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) → ∀ i,
      redA P (pullV (x * k⁻¹) v i) = ∑ j, resS F P (y i j) * redA P (pullV x v j) := by
    intro P v hv i
    obtain ⟨s, hs, hsu⟩ := pullV_den hv
    rw [pullV_mul_inv, mulVec_int_apply hyk]
    exact redA_sum P hs _ hsu _
  ext1
  · exact hN
  · funext P v
    show (open Classical in if v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat (x * k⁻¹) (stdLat E n))
      then redA P.1 (pullV (x * k⁻¹) v (lastIdx n)) else 0) =
      (c P).1 * (open Classical in if v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then redA P.1 (pullV x v (lastIdx n)) else 0)
    rw [hN]
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
    · rw [if_pos hv, if_pos hv, hval P.1 v hv]
      have hr : ∀ j, resS F P.1 (y (lastIdx n) j) = if j = lastIdx n then (c P).1 else 0 := by
        intro j; rw [← hyr P.1]; exact hrow P j
      simp only [hr, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [if_neg hv, if_neg hv, mul_zero]
  · funext w v
    show (open Classical in if v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat (x * k⁻¹) (stdLat E n))
      then fun i => redA w.1 (pullV (x * k⁻¹) v i) else 0) =
      (open Classical in if v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then fun i => redA w.1 (pullV x v i) else 0)
    rw [hN]
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
    · rw [if_pos hv, if_pos hv]
      funext i
      rw [hval w.1 v hv i]
      have hr : ∀ j, resS F w.1 (y i j) = if j = i then 1 else 0 := by
        intro j
        rw [← hyr w.1, hSG w]
        show (1 : Matrix (Fin n) (Fin n) (kP w.1)) i j = _
        rw [Matrix.one_apply]
        by_cases h : i = j
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (Ne.symm h)]
      simp only [hr, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [if_neg hv, if_neg hv]

theorem vdil_eq_put (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : ∀ v', v' ≠ v → bc (prV (E := E) v') x = 1) : x = rll_put n v (bc (prV (E := E) v) x) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [← sub_eq_zero]
  apply afsplit_inj
  intro w
  rw [map_sub, sub_eq_zero]
  have e : bc (prV (E := E) w) x = bc (prV (E := E) w) (rll_put n v (bc (prV (E := E) v) x)) := by
    by_cases hw : w = v
    · subst hw; rw [rll_put_self]
    · rw [h w hw, rll_put_ne n v w hw]
  exact congrArg (fun g : GL (Fin n) (E ⊗[F] w.adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] w.adicCompletion F)) i j) e

end Law

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

variable (h : BasePi ST π)
include h

theorem vdil_int {g : GL (Fin n) Rv}
    (H1 : ∀ z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹), (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹))
    (H2 : ∀ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE))) :
    ∀ i j, (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v := by
  intro i j
  by_cases hi : i = lastIdx n
  · subst hi
    have hz : (Pi.single j (ιv pE) : Fin n → Rv) ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
      rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)]
      refine ⟨fun i _ => ?_, ?_⟩
      · by_cases hi : i = j
        · subst hi; rw [Pi.single_eq_same]; exact rll_incl_int v π
        · rw [Pi.single_eq_of_ne hi]; exact zero_mem _
      · by_cases hj : lastIdx n = j
        · subst hj
          rw [Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ h.coe_ne_zero, map_one]; exact one_mem _
        · rw [Pi.single_eq_of_ne hj, mul_zero]; exact zero_mem _
    have h1 := H1 _ hz
    rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at h1
    have h2 := h1.2
    rwa [rll_mulVec_single, mul_comm _ (ιv pE), rll_pinv_mul v h] at h2
  · have h1 := H2 _ (rll_single_mem_Sh n v h j)
    rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at h1
    have h2 := h1.1 i hi
    rwa [rll_mulVec_single, mul_one] at h2

theorem vdil_row {g : GL (Fin n) Rv} (hint : ∀ i j, (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v) (k : ℤ)
    (H3 : ∀ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z - k • z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE))) :
    ∀ j, ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (k : Rv) * (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j =
      ιv pE * s := by
  intro j
  obtain ⟨a, b, hab⟩ := h.cop
  have hab' : ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE) = 1 := by
    rw [← algebraMap_cO, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, hab, map_one, map_one]
  have h1 := H3 _ (rll_single_mem_Sh n v h j)
  rw [rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)] at h1
  have h2 := h1.2
  rw [Pi.sub_apply, rll_mulVec_single, mul_one, Pi.smul_apply, zsmul_eq_mul] at h2
  have e0 : (Pi.single j 1 : Fin n → Rv) (lastIdx n) = (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j := by
    rw [Matrix.one_apply, Pi.single_apply]
  rw [e0] at h2
  set d := (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (k : Rv) * (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j with hd
  have hdi : d ∈ 𝒪v := sub_mem (hint _ _) (mul_mem (intCast_mem _ k) (afsplit_one_mem _ _ _))
  have e1 : ιv (star pE) * d = ιv pE * (ιv (star pE / pE) * d) := by
    rw [mul_left_comm, rll_cp_mul v h]
  refine ⟨ιv (algebraMap (𝓞 E) E a) * d + ιv (algebraMap (𝓞 E) E b) * (ιv (star pE / pE) * d),
    add_mem (mul_mem (rll_incl_int v a) hdi) (mul_mem (rll_incl_int v b) h2), ?_⟩
  calc d = (ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE)) * d := by rw [hab', one_mul]
    _ = ιv (algebraMap (𝓞 E) E a) * ιv pE * d + ιv (algebraMap (𝓞 E) E b) * (ιv (star pE) * d) := by ring
    _ = _ := by rw [e1]; ring

omit h in
theorem vdil_res_one {P : Pl E} (hov : IsOver v P) (j : Fin n)
    (hm : afsplitIE v ((1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j) ∈ Formalism.L2.Herm.intAf F E) :
    resS F P ⟨afsplitIE v ((1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j), hm⟩ = if j = lastIdx n then 1 else 0 := by
  by_cases hj : j = lastIdx n
  · subst hj
    rw [if_pos rfl]
    have h1 := rll_rho_one (E := E) v hov
    have e : (⟨afsplitIE v ((1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) (lastIdx n)), hm⟩ : Formalism.L2.Herm.intAf F E) =
        ⟨afsplitIE v ((1 : 𝒪v) : Rv), afsplit_IE_int v _ (1 : 𝒪v).2⟩ := by
      apply Subtype.ext
      show afsplitIE v ((1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) (lastIdx n)) = afsplitIE v ((1 : 𝒪v) : Rv)
      rw [Matrix.one_apply_eq]
      rfl
    rw [e]
    exact h1
  · rw [if_neg hj]
    have e : (⟨afsplitIE v ((1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j), hm⟩ : Formalism.L2.Herm.intAf F E) = 0 := by
      apply Subtype.ext
      show afsplitIE v ((1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j) = 0
      rw [Matrix.one_apply_ne (Ne.symm hj), map_zero]
    rw [e, map_zero]

theorem vdil_put {g : GL (Fin n) Rv} (hi : ∀ i j, (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v)
    (hi' : ∀ i j, ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v) (k : ℤ)
    (hrow : ∀ j, ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j -
      (k : Rv) * (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j = ιv pE * s) :
    ∃ hS : rll_put n v g ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), ∀ P ∈ ST, IsOver v P → ∀ j,
      ((redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) P ⟨rll_put n v g, hS⟩ : GL (Fin n) (kP P)) :
        Matrix (Fin n) (Fin n) (kP P)) (lastIdx n) j = if j = lastIdx n then ((k : ℤ) : kP P) else 0 := by
  have hgS : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [rll_locL_std]; exact (afsplit_stab_iff _ g).2 ⟨hi, hi'⟩
  have hS := rll_put_mem_St n v hgS
  refine ⟨hS, fun P hP hov j => ?_⟩
  obtain ⟨y, hy, hr⟩ := St_one_int hS
  rw [hr P]
  obtain ⟨s, hs, e⟩ := hrow j
  have e1 := rll_put_entry n v g (lastIdx n) j
  have e2 : (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j =
      ιv (algebraMap (𝓞 E) E ((k - 1 : ℤ) : 𝓞 E)) * (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j + ιv pE * s := by
    rw [← e, map_intCast, map_intCast]
    push_cast
    ring
  have h1m : (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j ∈ 𝒪v := afsplit_one_mem _ _ _
  rw [e2, map_add, rll_IE_incl_mul, rll_IE_incl_mul, hy] at e1
  have e3 : y (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) (lastIdx n) j =
      Formalism.L2.DIV.oToS F E ((k - 1 : ℤ) : 𝓞 E) *
        (⟨afsplitIE v ((1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j), afsplit_IE_int v _ h1m⟩ : Formalism.L2.Herm.intAf F E) +
      Formalism.L2.DIV.oToS F E π * (⟨afsplitIE v s, afsplit_IE_int v _ hs⟩ : Formalism.L2.Herm.intAf F E) := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, Formalism.L2.DIV.lc_one_coe]
    exact e1
  have e4 := congrArg (resS F P) e3
  rw [map_sub, map_add, map_mul, map_mul, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_oToS,
    Ideal.Quotient.eq_zero_iff_mem.2 (h.mem hP), zero_mul, add_zero, rll_resS_one, vdil_res_one n v hov, map_intCast] at e4
  by_cases hj : j = lastIdx n
  · rw [if_pos hj] at e4 ⊢
    rw [mul_one, sub_eq_iff_eq_add] at e4
    rw [e4]
    push_cast
    ring
  · rw [if_neg hj] at e4 ⊢
    rw [mul_zero, sub_zero] at e4
    exact e4

end Loc

section Dia

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) {π : 𝓞 E} (h : BasePi ST π)
  (v : HeightOneSpectrum (𝓞 F))

include h in

theorem decoOf_mul_dia (P : ST) (hov : IsOver v P.1) (hG : v ∉ plUnder F SG) (k : ℤ) (c : DiaG E ST)
    (hcP : ((c P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) = (k : 𝓞 E ⧸ P.1.asIdeal)) (hcne : ∀ P' : ST, P' ≠ P → c P' = 1)
    (x δ : UAd hc n)
    (h1 : ∀ v', v' ≠ v → bc (prV (E := E) v') (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hL : bc (prV (E := E) v) (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)))
    (hD : bc (prV (E := E) v) (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (baseDualV hc n ST v))
    (hf : ∀ z : baseDualV hc n ST v, k • fLoc hc n ST v
      ⟨(bc (prV (E := E) v) (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).1 *ᵥ z.1, (hD z.1).1 z.2⟩ = fLoc hc n ST v z) :
    decoOf ST SG ((x * δ : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      (decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).dia c := by
  set g := bc (prV (E := E) v) (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hg
  have hLi : g⁻¹ ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) := Subgroup.inv_mem _ hL
  have hDi : g⁻¹ ∈ stabGL (baseDualV hc n ST v) := Subgroup.inv_mem _ hD
  have hi := vdil_int n v h (g := g) (by rw [← rll_baseLb_eq n h]; exact fun z hz => (hL z).1 hz)
    (by rw [← rll_dualV_eq hc n v h]; exact fun z hz => (hD z).1 hz)
  have hi' := vdil_int n v h (g := g⁻¹) (by rw [← rll_baseLb_eq n h]; exact fun z hz => (hLi z).1 hz)
    (by rw [← rll_dualV_eq hc n v h]; exact fun z hz => (hDi z).1 hz)
  have hrow := vdil_row n v h (g := g⁻¹) hi' k (by
    rw [← rll_dualV_eq hc n v h, ← rll_baseKer_eq n h]
    intro z hz
    have h2 := hf ⟨(g⁻¹).1 *ᵥ z, (hDi z).1 hz⟩
    have e : (⟨g.1 *ᵥ ((g⁻¹).1 *ᵥ z), (hD _).1 ((hDi z).1 hz)⟩ : baseDualV hc n ST v) = ⟨z, hz⟩ := by
      apply Subtype.ext
      show g.1 *ᵥ ((g⁻¹).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, ← map_zsmul, eq_comm, ← sub_eq_zero, ← map_sub, rll_fLoc_eq_zero] at h2
    exact h2)
  obtain ⟨hS, hred⟩ := vdil_put n v h (g := g⁻¹) hi' (by rw [inv_inv]; exact hi) k hrow
  have hδ : (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = rll_put n v g⁻¹ := by
    have := vdil_eq_put v (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ (fun v' hv' => by rw [map_inv, h1 v' hv', inv_one])
    rwa [map_inv] at this
  have key := vdil_decoRaw_mul ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) hS c
    (by
      intro P' j
      by_cases hP' : IsOver v P'.1
      · have e : P' = P := Subtype.ext (h.over_unique hc P.2 hov P'.1 P'.2 hP')
        subst e
        rw [hred P'.1 P'.2 hP' j, hcP]
      · rw [rll_put_red n v _ hS P'.1 hP', hcne P' (fun e => hP' (e ▸ hov))]
        show (1 : Matrix (Fin n) (Fin n) (kP P'.1)) (lastIdx n) j = _
        rw [Matrix.one_apply]
        by_cases hj : j = lastIdx n
        · rw [if_pos hj.symm, if_pos hj]; rfl
        · rw [if_neg (Ne.symm hj), if_neg hj])
    (fun w => rll_put_red n v _ hS w.1 (fun hw => hG ⟨w.1, w.2, hw⟩))
  rw [← hδ, inv_inv] at key
  apply Subtype.ext
  rw [rlc_decoOf_val hc n ST SG (x * δ).2]
  show _ = (decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).1.dia c
  rw [rlc_decoOf_val hc n ST SG x.2]
  exact key

variable (H : Subgroup (GLG E n SG))

theorem vdil_dia_comm (c c' : DiaG E ST) (d : DecoSet E n ST SG) : (d.dia c).dia c' = (d.dia c').dia c := by
  rw [← DecoSet.dia_mul, ← DecoSet.dia_mul, mul_comm]

include h in

theorem vdil_move (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) (P : ST) (hov : IsOver v P.1) (hG : v ∉ plUnder F SG) (k : ℤ)
    (c : DiaG E ST) (hcP : ((c P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) = (k : 𝓞 E ⧸ P.1.asIdeal))
    (hcne : ∀ P' : ST, P' ≠ P → c P' = 1) (d d' : DecoSet E n ST SG) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d.dia c) (δ : UAd hc n)
    (h1 : ∀ v', v' ≠ v → bc (prV (E := E) v') (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hL : bc (prV (E := E) v) (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)))
    (hD : bc (prV (E := E) v) (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (baseDualV hc n ST v))
    (hf : ∀ z : baseDualV hc n ST v, k • fLoc hc n ST v
      ⟨(bc (prV (E := E) v) (δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).1 *ᵥ z.1, (hD z.1).1 z.2⟩ = fLoc hc n ST v z) :
    ∃ (γ : URat hc n) (κ : levU hc n ST SG H), ratHom hc n γ = g₀.1 ∧ levRed hc n ST SG H κ = g₀.2 ∧
      ((ptOfD hc n ST SG c₀ d * δ : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        bc (iA F E) (γ : GL (Fin n) E) * (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
  apply rlc_rel_of_orbit hc n ST SG H g₀
  rw [decoOf_mul_dia hc n ST SG h v P hov hG k c hcP hcne _ δ h1 hL hD hf]
  unfold ptOfD
  rw [decoOf_ptOf hc n ST SG hS, decoOf_ptOf hc n ST SG hS, vdil_dia_comm, ← hg₀]
  exact rla_dia_smulH n ST SG H c₀⁻¹ g₀ d'

end Dia

theorem vdil_ufGL_ratHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (n : ℕ) (γ : URat hc n) : ufGL E n (ratHom hc n γ) = (γ : GL (Fin n) E) := by
  show (toGLm E n) (glEquiv (γ : GL (Fin n) E)) = _
  unfold toGLm glEquiv
  simp

theorem vdil_isTr {X : Fields} {n : ℕ} (σ₀ : X.K →+* ℂ) (γ : GL (Fin n) X.E) (z : FrS X σ₀ n) :
    IsTr (atInf (embAt σ₀ X.emb) γ.1) (frMul σ₀ γ⁻¹ z) z := by
  intro τ
  have := congrArg (fun w : FrS X σ₀ n => w.1 τ) (frMul_mul σ₀ γ γ⁻¹ z)
  simp only [mul_inv_cancel, frMul_one] at this
  exact this

theorem vdil_typ_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : CMData F E} {n : ℕ} [NeZero n] {ST SG : Finset (Pl E)} {H : Subgroup (GLG E n SG)} {M : Type} [CommGroup M]
    (lam : H →* M) (κ : levU hc n ST SG H) : levTyp lam κ⁻¹ = lam (levRed hc n ST SG H κ) := by
  unfold levTyp levChr
  rw [MonoidHom.inv_apply, map_inv, inv_inv]
  rfl

section Clauses

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ) (c₀ : DiaG X.E (Pr.vT u)) (hS : DecoPtSurj hc (R.N i) (Pr.vT u) Pr.vGs)
  (eV : {P // P ∈ Pr.vT u} ≃ {v : HeightOneSpectrum (𝓞 X.F) // ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal})
  (heV : ∀ P, IsOver (eV P).1 P.1)

include heV in

theorem Val.dil (Q : ValCrd W Λ σ₀ u i) : Val.Dil W Λ hc hX hPr σ₀ u i c₀ hS eV Q := by
  classical
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro v a k hk c δ hδ
  obtain ⟨h1, hLv, hD, hf⟩ := hδ
  have hmv := (stepGSD W Λ u i).outSec.mv_smul ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).dia1 v a)
  unfold DecoSet.dia1 at hmv
  obtain ⟨γ, κ, -, -, e⟩ := vdil_move hc (R.N i) (Pr.vT u) Pr.vGs (basePi_of_ok hX hPr u) (eV v).1 (Λ i).grp hS c₀ v (heV v)
    (rls_T_notUnder hPr u (eV v).1 (eV v).2) k _ (by rw [Pi.mulSingle_eq_same]; exact hk.symm)
    (by intro P' h; exact Pi.mulSingle_eq_of_ne h _) _ _ _ hmv δ h1 hLv.2 hD hf
  exact rlc_mk_eq hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp γ κ e

include heV in

theorem Val.dilT (Q : ValCrd W Λ σ₀ u i) : Val.DilT W Λ hc hX hPr σ₀ hσ u i c₀ hS eV Q := by
  classical
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro v a k hk c δ hδ g hg
  obtain ⟨h1, hLv, hD, hf⟩ := hδ
  have hmv := (stepGSD W Λ u i).outSec.mv_smul ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).dia1 v a)
  unfold DecoSet.dia1 at hmv
  obtain ⟨γ, κ, hγ, hκ, e⟩ := vdil_move hc (R.N i) (Pr.vT u) Pr.vGs (basePi_of_ok hX hPr u) (eV v).1 (Λ i).grp hS c₀ v (heV v)
    (rls_T_notUnder hPr u (eV v).1 (eV v).2) k _ (by rw [Pi.mulSingle_eq_same]; exact hk.symm)
    (by intro P' h; exact Pi.mulSingle_eq_of_ne h _) _ _ _ hmv δ h1 hLv.2 hD hf
  funext z
  have h2 := hg γ.1 γ.2 _ _ (κ⁻¹ : levU hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp) e z (frMul σ₀ γ.1⁻¹ z) (vdil_isTr σ₀ γ.1 z)
  refine Eq.trans ?_ h2.symm
  have h3 : ((levTyp ((Units.map σ₀.toMonoidHom).comp (Λ i).chr) (κ⁻¹ : levU hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp) : ℂˣ) : ℂ) =
      σ₀ (((Λ i).chr (levRed hc (R.N i) (Pr.vT u) Pr.vGs (Λ i).grp κ) : X.Kˣ) : X.K) := by
    rw [vdil_typ_inv]; rfl
  refine Eq.trans ?_ (congrArg (· * _) h3.symm)
  rw [hκ, ← vdil_ufGL_ratHom hc (R.N i) γ, hγ]
  rfl

end Clauses

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m) (eV : ((d.colRec a).mem u).A.vT ≃ CF.PlT (d.colRec a) u) (heV : ∀ P, IsOver (eV P).1 P.1)

include heV in

theorem valDil_rec :
    Val.Dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i) eV
      (valCrd a hS hH u i hi) :=
  Val.dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i _ (hP u i) eV heV _

include heV in

theorem valDilT_rec :
    Val.DilT (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i) eV
      (valCrd a hS hH u i hi) :=
  Val.dilT (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i _ (hP u i) eV heV _

end Rec

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ)

def Val.Bw (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K)) (Q : ValCrd W Λ σ₀ u i)
    (Pv : {P // P ∈ Pr.vT u} → Ideal (𝓞 X.E)) : Prop :=
  ∀ w, Pl.resChar w = Pr.T u → seenC Pr u (pw w) →
    ∀ (v : {P // P ∈ Pr.vT u}) (x : (stepGSD W Λ u i).EqFun),
      x ∈ Submodule.span (intW Pl w) (stepBv W Λ u i v : Set (stepGSD W Λ u i).EqFun) ↔
    ∀ (c : StCl W Λ u i) (B B' : GL (Fin (R.N i)) X.E),
      IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) : Set _) B →
      IsLocBasis (Pr.T u) ((Q.lat c ⊔ Pv v • dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set _) B' →
      ∃ P ∈ IntSpanG σ₀ Pl w (W.lamN u i), ∀ z, (stepEv W Λ σ₀ hσ u i).emb x c z =
        fnOf _ (shiftOf Q.lt)
          (fun τ => @ite _ (τ = tauOfR hX hPr u (pw w) v) (Classical.propDecidable _)
            (atInf Q.emb (B'⁻¹ : GL (Fin (R.N i)) X.E).1 τ) (atInf Q.emb (B⁻¹ : GL (Fin (R.N i)) X.E).1 τ)) P
          (valEY W Λ σ₀ u i Q z)

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m)

theorem bwTie_of (Wv : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV i hi (classAgreement a hS hH hP u i hi))
    (hY : Wv.eY = valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi))
    (hBw : Val.Bw (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i d.what₂.places d.plEq (valCrd a hS hH u i hi)
      (atTTied a hH u).Pv) :
    CF.BwTie (atTTied a hH u) Wv := by
  intro w hw hs v x
  rw [hY]
  exact hBw w hw (@of_decide_eq_true _ (Classical.propDecidable _) hs) v x

end Rec

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {d : Deco E n ST SG} {a : 𝓞 E}

theorem vb_sup_le_LshKer (hd : d.Ok) (ha : SepElt ST a) (P : ST) : d.L ⊔ P.1.asIdeal • d.Lsh ≤ d.LshKer P := by
  refine sup_le (fun x hx => (hd.mem_LshKer ha P x).2 ⟨hd.L_le_Lsh hx, ((hd.mem_L x).1 hx).2 P⟩) ?_
  refine Submodule.smul_le.2 fun p hp x hx => (hd.mem_LshKer ha P _).2 ⟨Submodule.smul_mem _ p hx, ?_⟩
  rw [hd.f_smul P p x (hd.Lsh_le_at ha P hx), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]

theorem vb_exists_smul_mem_L (hd : d.Ok) (ha : SepElt ST a) (P : ST) {y : Sp E n} (hy : y ∈ d.kerAt P) :
    ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧ s • y ∈ d.L := by
  classical
  obtain ⟨hyN, hyf⟩ := (hd.mem_kerAt P y).1 hy
  choose p hp hpP using fun Q : {Q : ST // Q ≠ P} =>
    exists_mem_notMem (P := Q.1.1) (Q := P.1) (fun e => Q.2 (Subtype.ext e))
  refine ⟨∏ Q, p Q, ?_, ?_⟩
  · intro h
    obtain ⟨Q, -, hQ⟩ := (P.1.isPrime.prod_mem_iff).1 h
    exact hpP Q hQ
  · refine (hd.mem_L _).2 ⟨Submodule.smul_mem _ _ hyN, fun Q => ?_⟩
    rw [hd.f_smul Q _ y (hd.Lsh_le_at ha Q (hd.N_le_Lsh hyN))]
    by_cases hQ : Q = P
    · subst hQ
      rw [hyf, mul_zero]
    · have h1 : (∏ Q, p Q) ∈ Q.1.asIdeal := by
        rw [← Finset.mul_prod_erase Finset.univ p (Finset.mem_univ (⟨Q, hQ⟩ : {Q : ST // Q ≠ P}))]
        exact Ideal.mul_mem_right _ _ (hp ⟨Q, hQ⟩)
      rw [Ideal.Quotient.eq_zero_iff_mem.2 h1, zero_mul]

theorem vb_LshKer_le_at (hd : d.Ok) (ha : SepElt ST a) (P : ST) {x : Sp E n} (hx : x ∈ d.LshKer P) :
    ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧ s • x ∈ d.L ⊔ P.1.asIdeal • d.Lsh := by
  have h1 : x ∈ localization₂ P.1.asIdeal (d.kerAt P) := by
    rw [← hd.locP_LshKer_self ha P]
    exact le_locP _ _ hx
  obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 h1
  obtain ⟨t, ht, htx⟩ := vb_exists_smul_mem_L hd ha P hsx
  exact ⟨t * s, fun h => (P.1.isPrime.mem_or_mem h).elim ht hs, by
    rw [mul_smul]; exact Submodule.mem_sup_left htx⟩

theorem vb_sup_lattice (hd : d.Ok) (P : ST) : Submodule.IsLattice E (d.L ⊔ P.1.asIdeal • d.Lsh) :=
  lattice_between hd.L_lattice hd.Lsh_lattice le_sup_left (sup_le hd.L_le_Lsh Submodule.smul_le_right)

end Deco

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ)
  (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K))
  (hval : ∀ w (x : X.K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))

include hval hPr in
open Classical in

theorem vb_mem_locP_BvLat_iff (u : Pr.Word) (j : ℕ) (lam' : X.Tau → DomWeight (R.N j))
    (hn : ∀ τ, (W.lamTrue u j τ).natW = (lam' τ).natW) (w : Pl.Pl) (hw : Pl.resChar w = Pr.T u) (hs : seenC Pr u (pw w))
    (v : {P // P ∈ Pr.vT u}) (d : ColDeco X Pr u (R.N j)) (F : VV X.K (W.lamTrue u j)) :
    haveI := hX.nonempty_Tau
    F ∈ localization₂ (pw w).asIdeal (BvLat W u j v d) ↔
      ∀ B B' : GL (Fin (R.N j)) X.E, IsLocBasis (Pr.T u) (d.1.Lsh : Set (Fin (R.N j) → X.E)) B →
        IsLocBasis (Pr.T u) ((d.1.L ⊔ v.1.asIdeal • d.1.Lsh : Submodule (𝓞 X.E) (Fin (R.N j) → X.E)) : Set (Fin (R.N j) → X.E)) B' →
        ∃ P ∈ vlIntSpan σ₀ Pl w lam', evV X.emb (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) (W.lamTrue u j) σ₀ F =
          fnOf _ (shiftOf (W.lamTrue u j))
            (fun τ => @ite _ (τ = tauOfC (pw w) v.1) (Classical.propDecidable _)
              (atInf (embAt σ₀ X.emb) ((B'⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)
              (atInf (embAt σ₀ X.emb) ((B⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)) P := by
  have := hX.nonempty_Tau
  have ha := sepElt_of_ok hPr u
  have hT : (Pr.T u : 𝓞 X.K) ∈ (pw w).asIdeal := hw ▸ vl_resChar_mem Pl pw hval w
  set τ₀ := tauOfC (pw w) v.1 with hτ₀

  have hsee : pullW τ₀ (pw w) = v.1 := by
    rcases tauOfC_spec hX hPr u (pw w) hT v with h | h
    · exact h
    · exact absurd h ((moveHyp_of_ok hPr u v).st ⟨pullW τ₀ (pw w), (seenC_iff hPr u (pw w)).1 hs τ₀⟩)
  let M : X.Tau → Submodule (𝓞 X.E) (Fin (R.N j) → X.E) := fun τ => if τ = τ₀ then d.1.L ⊔ v.1.asIdeal • d.1.Lsh else d.1.Lsh
  have hM : ∀ τ, Submodule.IsLattice X.E (M τ) := by
    intro τ
    by_cases hτ : τ = τ₀
    · simp only [M, if_pos hτ]; exact vb_sup_lattice d.2 v
    · simp only [M, if_neg hτ]; exact d.2.Lsh_lattice
  have e1 : localization₂ (pw w).asIdeal (BvLat W u j v d) =
      localization₂ (pw w).asIdeal (delK (W.lamTrue u j) fun τ => dualFr (tauLat X.emb τ (M τ))) := by
    rw [BvLat_eq_BvLatF W hX hPr u j hs v d]
    unfold BvLatF
    refine round_locP_congr_fam X.emb (W.lamTrue u j) (pw w) (fun τ => ?_) hM (fun τ => ?_)
    · by_cases hτ : τ = τ₀
      · rw [if_pos hτ]; exact d.2.LshKer_lattice ha v
      · rw [if_neg hτ]; exact d.2.Lsh_lattice
    · by_cases hτ : τ = τ₀
      · have hτ' : τ = tauOfC (pw w) v.1 := hτ
        simp only [M, if_pos hτ]
        rw [if_pos hτ']
        subst hτ
        constructor
        · intro x hx
          obtain ⟨s, hs', hsx⟩ := vb_LshKer_le_at d.2 ha v hx
          refine ⟨s, ?_, hsx⟩
          intro h
          apply hs'
          rw [← hsee]
          exact h
        · intro x hx
          exact ⟨1, by rw [map_one]; exact one_notMem (pw w), by rw [one_smul]; exact vb_sup_le_LshKer d.2 ha v hx⟩
      · have hτ' : ¬ τ = tauOfC (pw w) v.1 := hτ
        simp only [M, if_neg hτ]
        rw [if_neg hτ']
        exact ⟨fun x hx => ⟨1, by rw [map_one]; exact one_notMem (pw w), by rwa [one_smul]⟩,
          fun x hx => ⟨1, by rw [map_one]; exact one_notMem (pw w), by rwa [one_smul]⟩⟩
  rw [e1]
  have key : ∀ B B' : GL (Fin (R.N j)) X.E, IsLocBasis (Pr.T u) (d.1.Lsh : Set (Fin (R.N j) → X.E)) B →
      IsLocBasis (Pr.T u) ((d.1.L ⊔ v.1.asIdeal • d.1.Lsh : Submodule (𝓞 X.E) (Fin (R.N j) → X.E)) : Set (Fin (R.N j) → X.E)) B' →
      (F ∈ localization₂ (pw w).asIdeal (delK (W.lamTrue u j) fun τ => dualFr (tauLat X.emb τ (M τ))) ↔
        ∃ P ∈ vlIntSpan σ₀ Pl w lam', evV X.emb (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) (W.lamTrue u j) σ₀ F =
          fnOf _ (shiftOf (W.lamTrue u j))
            (fun τ => @ite _ (τ = τ₀) (Classical.propDecidable _)
              (atInf (embAt σ₀ X.emb) ((B'⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)
              (atInf (embAt σ₀ X.emb) ((B⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)) P) := by
    intro B B' hB hB'
    have h := mem_localization_iff_forall_localBasis_of_valuation Pl pw hval X.emb σ₀ w (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) (W.lamTrue u j) lam' hn M hM F
      (fun τ => if τ = τ₀ then B' else B) (fun τ => by
        rw [hw]
        by_cases hτ : τ = τ₀
        · simp only [M, if_pos hτ]; exact hB'
        · simp only [M, if_neg hτ]; exact hB)
    have e2 : (fun τ => atInf (embAt σ₀ X.emb) ((((if τ = τ₀ then B' else B) : GL (Fin (R.N j)) X.E)⁻¹ : GL (Fin (R.N j)) X.E) :
        Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) τ) =
        fun τ => @ite _ (τ = τ₀) (Classical.propDecidable _)
          (atInf (embAt σ₀ X.emb) ((B'⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)
          (atInf (embAt σ₀ X.emb) ((B⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ) := by
      funext τ
      by_cases hτ : τ = τ₀
      · rw [if_pos hτ, if_pos hτ]
      · rw [if_neg hτ, if_neg hτ]
    rw [e2] at h
    exact h
  constructor
  · intro h B B' hB hB'
    exact (key B B' hB hB').1 h
  · intro h
    have : Fact (Pr.T u).Prime := ⟨hPr.T_prime u⟩
    obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pr.T u) X.E d.1.Lsh d.2.Lsh_lattice.fg d.2.Lsh_lattice.span_eq_top
    obtain ⟨B', hB'⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pr.T u) X.E _ (vb_sup_lattice d.2 v).fg
      (vb_sup_lattice d.2 v).span_eq_top
    exact (key B B' hB hB').2 (h B B' hB hB')

end One

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ)

include hX in

theorem mem_localization_stepLattice_iff (w : HeightOneSpectrum (𝓞 X.K)) (v : {P // P ∈ Pr.vT u}) (x : (stepGSD W Λ u i).EqFun) :
    x ∈ localization₂ w.asIdeal (stepBv W Λ u i v) ↔ ∀ c : StCl W Λ u i,
      (x : (stepGSD W Λ u i).D → (stepGSD W Λ u i).V) ((stepGSD W Λ u i).outSec.rep c) ∈
        localization₂ w.asIdeal (BvLat W u i v ((stepGSD W Λ u i).outSec.rep c)) := by
  constructor
  · rintro ⟨t, ht, h⟩ c
    exact ⟨t, ht, h _⟩
  · intro h
    classical
    let _ := (stepOk W Λ hX u i).fintypeCl
    choose t ht htx using h
    refine ⟨∏ c, t c, ?_, ?_⟩
    · intro hmem
      obtain ⟨c, -, hc'⟩ := (w.isPrime.prod_mem_iff).1 hmem
      exact ht c hc'
    · refine ((stepGSD W Λ u i).mem_intOf_iff _ (BvLat_equivG W u i (Λ i) v) (stepGSD W Λ u i).outSec _).2 fun c => ?_
      have h2 : ∀ F : VV X.K (W.lamTrue u i), t c • F ∈ BvLat W u i v ((stepGSD W Λ u i).outSec.rep c) →
          (∏ c, t c) • F ∈ BvLat W u i v ((stepGSD W Λ u i).outSec.rep c) := by
        intro F hF
        rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ c), mul_comm]
        have e : ((∏ x ∈ Finset.univ.erase c, t x) * t c) • F = (∏ x ∈ Finset.univ.erase c, t x) • (t c • F) := mul_smul _ _ _
        rw [e]
        exact Submodule.smul_mem _ _ hF
      exact h2 _ (htx c)

theorem Val.bw (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K))
    (hval : ∀ w (x : X.K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (Q : ValCrd W Λ σ₀ u i)
    (Pv : {P // P ∈ Pr.vT u} → Ideal (𝓞 X.E)) (hPv : ∀ v, Pv v = v.1.asIdeal) :
    Val.Bw W Λ hc hX hPr σ₀ hσ u i Pl pw Q Pv := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  obtain rfl : Pv = fun v => v.1.asIdeal := funext hPv
  intro w hw hs v x
  have := hX.nonempty_Tau
  have hT : (Pr.T u : 𝓞 X.K) ∈ (pw w).asIdeal := hw ▸ vl_resChar_mem Pl pw hval w
  have htau : tauOfR hX hPr u (pw w) v = tauOfC (pw w) v.1 := by
    unfold tauOfR
    rw [dif_pos hT]
    rfl
  rw [vl_mem_span_intW_iff Pl pw hval w (stepBv W Λ u i v) x, mem_localization_stepLattice_iff W Λ hX u i (pw w) v x]
  refine forall_congr' fun c => ?_
  refine (vb_mem_locP_BvLat_iff W hX hPr σ₀ Pl pw hval u i (W.lamN u i) (vl_natW_lamTrue W u i) w hw hs v
    ((stepGSD W Λ u i).outSec.rep c)
    ((x : (stepGSD W Λ u i).D → (stepGSD W Λ u i).V) ((stepGSD W Λ u i).outSec.rep c))).trans ?_
  have hd : dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L =
      ((stepGSD W Λ u i).outSec.rep c).1.Lsh := rlc_span_dualSet hc (R.N i) _
  constructor
  · intro h B B' hB hB'
    have hB1 : IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L : Set (Fin (R.N i) → X.E)) B := hB
    have hB2 : IsLocBasis (Pr.T u) ((((stepGSD W Λ u i).outSec.rep c).1.L ⊔ v.1.asIdeal •
        dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set (Fin (R.N i) → X.E)) B' := hB'
    rw [hd] at hB1 hB2
    obtain ⟨P, hP, he⟩ := h B B' hB1 hB2
    refine ⟨P, hP, fun z => ?_⟩
    rw [htau]
    exact congrFun he z
  · intro h B B' hB hB'
    have hB1 : IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L : Set (Fin (R.N i) → X.E)) B := by
      rw [hd]; exact hB
    have hB2 : IsLocBasis (Pr.T u) ((((stepGSD W Λ u i).outSec.rep c).1.L ⊔ v.1.asIdeal •
        dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set (Fin (R.N i) → X.E)) B' := by
      rw [hd]; exact hB'
    obtain ⟨P, hP, he⟩ := h B B' hB1 hB2
    rw [htau] at he
    exact ⟨P, hP, funext he⟩

end Gen

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m)

def valuationAgreementConcrete : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV i hi (classAgreement a hS hH hP u i hi) :=
  valuationAgreement a hS hH hP u i hi (tieEV d.sp.cm d.hX d.hPr u)
    (Val.fi (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (valCrd a hS hH u i hi))
    (Val.rat (Pr := d.Pr) d.W d.lev d.hX d.σ₀ d.star_cx u i (valCrd a hS hH u i hi))
    (Val.lat (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.σ₀ d.star_cx u i d.what₂.places d.plEq d.plEq.surjective hH.val_eq
      (valCrd a hS hH u i hi))
    (Val.dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (tieEV d.sp.cm d.hX d.hPr u) (tieEV_over d.sp.cm d.hX d.hPr u) (valCrd a hS hH u i hi))
    (Val.dilT (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (tieEV d.sp.cm d.hX d.hPr u) (tieEV_over d.sp.cm d.hX d.hPr u) (valCrd a hS hH u i hi))

theorem stepValTied_eY : (valuationAgreementConcrete a hS hH hP u i hi).eY = valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi) := rfl

theorem stepNormTie : CF.NormTie (valuationAgreementConcrete a hS hH hP u i hi) :=
  normTie a hS hH hP u i hi _ (valuationAgreementConcrete a hS hH hP u i hi) rfl

theorem stepBwTie : CF.BwTie (atTTied a hH u) (valuationAgreementConcrete a hS hH hP u i hi) :=
  bwTie_of a hS hH hP u i hi (valuationAgreementConcrete a hS hH hP u i hi) rfl
    (Val.bw (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i d.what₂.places d.plEq hH.val_eq (valCrd a hS hH u i hi)
      (atTTied a hH u).Pv (fun _ => Ideal.mk_ker))

end Formalism.L2.Col
end
end
