import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdxNOneMulAbsNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPartnerLift
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTermsGramClassOverSublattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesBoundedDetLeSum
import BuildAid.ForwardExisting
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

section
open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.LoopC.Partner

section Count

open Formalism.MainNotions.S.Cnt GlobalTheory.Mass
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cntCl_mono {α : Type} {X Y : Set α} (h : X ⊆ Y) (R : α → α → Prop) : cntCl X R ≤ cntCl Y R := by
  unfold cntCl
  have hsub : {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} ⊆
      (fun O => O ∩ X) '' {O : Set α | ∃ a ∈ Y, O = {b | b ∈ Y ∧ R a b}} := by
    rintro O ⟨a, ha, rfl⟩
    refine ⟨{b | b ∈ Y ∧ R a b}, ⟨a, h ha, rfl⟩, ?_⟩
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨_, hc⟩, hcX⟩
      exact ⟨hcX, hc⟩
    · rintro ⟨hcX, hc⟩
      exact ⟨⟨h hcX, hc⟩, hcX⟩
  exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)

theorem one_le_prod_real {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x) (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl h

variable {D : D7}

theorem one_le_sizeZ (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  exact one_le_prod_real fun τ _ => one_le_prod_real fun l _ => le_max_left _ _

theorem prod_Gz_le {b C B T T' : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C) (hr : 1 ≤ D.R.rS) (hT : 1 ≤ T * T') (hB : T * T' ≤ B)
    (Z : GramM D) :
    ∏ τ, Gz D T T' Z τ ≤ (B * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f * sizeZ D b C Z ^ 2 := by
  obtain ⟨hcard, -, -, -, hrd, -⟩ := GlobalTheory.real_places_facts D
  have hH : 0 < b ^ (C * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos (by linarith) _
  have hB1 : 1 ≤ B := hT.trans hB
  have hnn : ∀ l τ, 0 ≤ absDl D Z l τ := fun l τ => by
    unfold absDl absReal
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hM1 : ∀ l τ, 1 ≤ max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := fun l τ => le_max_left _ _
  have hsq : ∀ l τ, absDl D Z l τ ^ 2 ≤
      (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 * max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 := fun l τ => by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (hnn l τ) ?_ 2
    have h := le_max_right 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))
    rw [div_le_iff₀ hH] at h
    linarith
  have hpt : ∀ τ, |Gz D T T' Z τ| ≤ B * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 *
      (max 1 (absDl D Z (D.R.rS + 1) τ / b ^ (C * (D.R.m : ℝ) ^ 2)) *
        max 1 (absDl D Z D.R.rS τ / b ^ (C * (D.R.m : ℝ) ^ 2))) ^ 2 := fun τ => by
    unfold Gz
    have ha := hsq (D.R.rS + 1) τ
    have hc := hsq D.R.rS τ
    have hMa := one_le_pow₀ (n := 2) (hM1 (D.R.rS + 1) τ)
    have hMc := one_le_pow₀ (n := 2) (hM1 D.R.rS τ)
    have hK := sq_nonneg (b ^ (C * (D.R.m : ℝ) ^ 2))
    have hA0 := sq_nonneg (absDl D Z (D.R.rS + 1) τ)
    have hC0 := sq_nonneg (absDl D Z D.R.rS τ)
    have e1 := mul_nonneg (sub_nonneg.2 hB1) (mul_nonneg (mul_nonneg hK (zero_le_one.trans hMa)) (zero_le_one.trans hMc))
    have e2 := mul_nonneg (mul_nonneg hK (zero_le_one.trans hMa)) (sub_nonneg.2 hMc)
    have e3 := mul_nonneg (zero_le_one.trans hT) hC0
    have e4 := mul_nonneg (sub_nonneg.2 hB) hC0
    have e5 := mul_nonneg (zero_le_one.trans hB1) (sub_nonneg.2 hc)
    have e6 := mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hB1) hK) (zero_le_one.trans hMc)) (sub_nonneg.2 hMa)
    rw [abs_le]
    constructor <;> nlinarith [e1, e2, e3, e4, e5, e6, ha, hA0]
  have hprod : ∏ τ, Gz D T T' Z τ ≤ ∏ τ, (B * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 *
      (max 1 (absDl D Z (D.R.rS + 1) τ / b ^ (C * (D.R.m : ℝ) ^ 2)) *
        max 1 (absDl D Z D.R.rS τ / b ^ (C * (D.R.m : ℝ) ^ 2))) ^ 2) :=
    calc ∏ τ, Gz D T T' Z τ ≤ |∏ τ, Gz D T T' Z τ| := le_abs_self _
      _ = ∏ τ, |Gz D T T' Z τ| := Finset.abs_prod _ _
      _ ≤ _ := Finset.prod_le_prod (fun τ _ => abs_nonneg _) (fun τ _ => hpt τ)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, Finset.prod_pow] at hprod
  have hsz : ∏ τ, (max 1 (absDl D Z (D.R.rS + 1) τ / b ^ (C * (D.R.m : ℝ) ^ 2)) *
      max 1 (absDl D Z D.R.rS τ / b ^ (C * (D.R.m : ℝ) ^ 2))) ≤ sizeZ D b C Z := by
    unfold sizeZ
    refine Finset.prod_le_prod (fun τ _ => mul_nonneg (zero_le_one.trans (hM1 _ _)) (zero_le_one.trans (hM1 _ _))) ?_
    intro τ _
    have hmem1 : D.R.rS + 1 ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    have hmem2 : D.R.rS ∈ (Finset.Icc 1 (D.R.rS + 1)).erase (D.R.rS + 1) :=
      Finset.mem_erase.2 ⟨by omega, Finset.mem_Icc.2 ⟨hr, by omega⟩⟩
    rw [← Finset.mul_prod_erase _ _ hmem1, ← Finset.mul_prod_erase _ _ hmem2]
    have h1 : 1 ≤ ∏ l ∈ ((Finset.Icc 1 (D.R.rS + 1)).erase (D.R.rS + 1)).erase D.R.rS,
        max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := one_le_prod_real fun l _ => hM1 l τ
    have ha := hM1 (D.R.rS + 1) τ
    have hc := hM1 D.R.rS τ
    rw [← mul_assoc]
    exact le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans ha) (zero_le_one.trans hc)) h1
  refine hprod.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ hsz 2) (pow_nonneg ?_ _))
  · exact Finset.prod_nonneg fun τ _ => mul_nonneg (zero_le_one.trans (hM1 _ _)) (zero_le_one.trans (hM1 _ _))
  · exact mul_nonneg (by linarith) (sq_nonneg _)

theorem sizes {b C CT : ℝ} (hb : 1 ≤ b) (hC : 2 ≤ C) (hCT : CT ≤ C) (hr : 1 ≤ D.R.rS) {T T' : ℝ} (h1 : 1 ≤ T)
    (h1' : 1 ≤ T') (hT : T ≤ b ^ (CT * D.R.m)) (hT' : T' ≤ b ^ (CT * D.R.m)) (Z : GramM D) :
    1 ≤ HHZ D b C Z ∧ T ^ D.R.f ≤ HHZ D b C Z ∧ ∏ τ, Gz D T T' Z τ ≤ HHZ D b C Z := by
  have hb0 : 0 ≤ b := by linarith
  have hbp : 0 < b := by linarith
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hs := one_le_sizeZ b C Z
  have hs4 : 1 ≤ sizeZ D b C Z ^ 4 := one_le_pow₀ hs
  have hE : HHZ D b C Z = b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) * sizeZ D b C Z ^ 4 := by
    unfold HHZ
    rw [← Real.rpow_mul hb0]
  have hE0 : 0 ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by positivity
  have hbE : 1 ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.one_le_rpow hb hE0
  refine ⟨?_, ?_, ?_⟩
  · rw [hE]
    exact one_le_mul_of_one_le_of_one_le hbE hs4
  · rw [hE]
    have e1 : T ^ D.R.f ≤ (b ^ (CT * D.R.m)) ^ D.R.f := pow_le_pow_left₀ (by linarith) hT _
    rw [← Real.rpow_mul_natCast hb0] at e1
    have hx : CT * D.R.m * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
      have q1 := mul_nonneg (mul_nonneg (sub_nonneg.2 hCT) (by linarith : (0 : ℝ) ≤ D.R.m)) hf
      have q2 : (1 : ℝ) ≤ C * (D.R.m : ℝ) ^ 2 := by nlinarith
      have q3 := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (by linarith : (0 : ℝ) ≤ D.R.m)) hf)
        (sub_nonneg.2 q2)
      nlinarith
    have e2 := Real.rpow_le_rpow_of_exponent_le hb hx
    calc T ^ D.R.f ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := e1.trans e2
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hs4
  · have hTT : 1 ≤ T * T' := one_le_mul_of_one_le_of_one_le h1 h1'
    have hB : T * T' ≤ b ^ (CT * D.R.m) * b ^ (CT * D.R.m) :=
      mul_le_mul hT hT' (by linarith) (Real.rpow_nonneg hb0 _)
    have hP := prod_Gz_le (C := C) hb (by linarith) hr hTT hB Z
    have eB : (b ^ (CT * D.R.m) * b ^ (CT * D.R.m) * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f =
        b ^ ((2 * CT * D.R.m + 2 * C * (D.R.m : ℝ) ^ 2) * D.R.f) := by
      rw [← Real.rpow_add hbp, ← Real.rpow_mul_natCast hb0 _ 2, ← Real.rpow_add hbp,
        ← Real.rpow_mul_natCast hb0]
      congr 1
      push_cast
      ring
    rw [eB] at hP
    have hx : (2 * CT * D.R.m + 2 * C * (D.R.m : ℝ) ^ 2) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
      have q1 : 2 * CT * D.R.m + 2 * C * (D.R.m : ℝ) ^ 2 ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) := by
        have r1 := mul_nonneg (sub_nonneg.2 hCT) (by linarith : (0 : ℝ) ≤ D.R.m)
        have r2 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (by linarith : (0 : ℝ) ≤ D.R.m))
          (by linarith : (0 : ℝ) ≤ D.R.m - 1)
        have r3 : (4 : ℝ) ≤ C * D.R.m := by nlinarith
        have r4 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (sq_nonneg (D.R.m : ℝ))) (sub_nonneg.2 r3)
        nlinarith
      have := mul_le_mul_of_nonneg_right q1 hf
      linarith
    have e2 := Real.rpow_le_rpow_of_exponent_le hb hx
    have hs2 : sizeZ D b C Z ^ 2 ≤ sizeZ D b C Z ^ 4 := pow_le_pow_right₀ hs (by norm_num)
    rw [hE]
    exact hP.trans (mul_le_mul e2 hs2 (sq_nonneg _) (by linarith))

theorem final_arith {N De H C : ℝ} {r f : ℕ} (hr : 1 ≤ r) (hN0 : 0 ≤ N) (hN : N ≤ H) (hD0 : 1 ≤ De) (hD : De ≤ H)
    (hC : 37 ≤ C) :
    N ^ (2 * r) * De ^ r * 9 ^ (1 * f) * H ^ (9 * 1 + 9 * 1 * r + 16 * r ^ 2) ≤ C ^ f * H ^ (C * (r : ℝ) ^ 2) := by
  have hH : 1 ≤ H := hD0.trans hD
  have h1 : N ^ (2 * r) ≤ H ^ (2 * r) := pow_le_pow_left₀ hN0 hN _
  have h2 : De ^ r ≤ H ^ r := pow_le_pow_left₀ (by linarith) hD _
  have h3 : (9 : ℝ) ^ (1 * f) ≤ C ^ f := by
    rw [one_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hexp : ((2 * r + r + (9 * 1 + 9 * 1 * r + 16 * r ^ 2) : ℕ) : ℝ) ≤ C * (r : ℝ) ^ 2 := by
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    push_cast
    nlinarith
  have h4 : H ^ (2 * r + r + (9 * 1 + 9 * 1 * r + 16 * r ^ 2)) ≤ H ^ (C * (r : ℝ) ^ 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hH hexp
  calc N ^ (2 * r) * De ^ r * 9 ^ (1 * f) * H ^ (9 * 1 + 9 * 1 * r + 16 * r ^ 2)
      ≤ H ^ (2 * r) * H ^ r * C ^ f * H ^ (9 * 1 + 9 * 1 * r + 16 * r ^ 2) := by
        have hH0 : 0 ≤ H := by linarith
        have s1 : N ^ (2 * r) * De ^ r ≤ H ^ (2 * r) * H ^ r :=
          mul_le_mul h1 h2 (pow_nonneg (by linarith) _) (pow_nonneg hH0 _)
        have s2 : N ^ (2 * r) * De ^ r * 9 ^ (1 * f) ≤ H ^ (2 * r) * H ^ r * C ^ f :=
          mul_le_mul s1 h3 (by positivity) (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
        exact mul_le_mul_of_nonneg_right s2 (pow_nonneg hH0 _)
    _ = C ^ f * H ^ (2 * r + r + (9 * 1 + 9 * 1 * r + 16 * r ^ 2)) := by
        rw [pow_add, pow_add]
        ring
    _ ≤ C ^ f * H ^ (C * (r : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h4 (pow_nonneg (by linarith) _)

theorem partners_le : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.count_terms_gramClass_over_sublattice Cg cb Cu cT CT C0 A
  refine ⟨max (max C₀ 37) CT, ?_⟩
  intro D large₂ u u' C' Cl hCl hHyp F0 he hz Λ hΛ F' hterm hgen hrel Z hZ
  have hCC₀ : C₀ ≤ max (max C₀ 37) CT := (le_max_left _ _).trans (le_max_left _ _)
  have hC37 : (37 : ℝ) ≤ max (max C₀ 37) CT := (le_max_right _ _).trans (le_max_left _ _)
  have hCT : CT ≤ max (max C₀ 37) CT := le_max_right _ _
  have hHyp' := hHyp
  obtain ⟨⟨hS0, -, -⟩, hSt, -⟩ := hHyp'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTr, -, -⟩ := hS0
  obtain ⟨hr, -, -, hT3, hT3', -, -, hg0, hg1, -, -, -, -⟩ := hSt
  have hb : 1 ≤ large₂.sc.b := by
    show 1 ≤ Real.exp (large₂.sc.x ^ large₂.sc.eps)
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hTu : ((Tu D u : ℕ) : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := (hTr u).2
  have hTu' : ((Tu D u' : ℕ) : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := (hTr u').2
  have hT1 : (1 : ℝ) ≤ (Tu D u : ℕ) := by exact_mod_cast (by omega : 1 ≤ Tu D u)
  have hT1' : (1 : ℝ) ≤ (Tu D u' : ℕ) := by exact_mod_cast (by omega : 1 ≤ Tu D u')
  have hTne : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTne' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hg : gS D ≠ 0 := by
    unfold gS
    exact Nat.mul_ne_zero hg0.ne_zero hg1.ne_zero
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hΛ' := hΛ
  obtain ⟨-, ⟨hlat, huni, hlift, -⟩, hXS⟩ := hΛ'
  have hterm' := hterm
  obtain ⟨⟨hlift', -, hG'⟩, -, hXS'⟩ := hterm'
  have hfr : ∀ b, frame (lf D F0) b ∈ Λ := frame_mem_of_XS (lf D F0) hlift hXS
  have hfr' : ∀ b, frame F' b ∈ Λ := frame_mem_of_XS F' hlift' hXS'
  have hUUE : UUE Λ (lf D F0) F' = Xplus (lf D F0) ⊔ Xplus F' := UUE_eq (lf D F0) F' hlift hlift' hfr hfr'
  have hW : WHyp D (lf D F0) (Wsp D) := Formalism.MainNotions.WHyp_Wsp D u (by omega) (lf D F0) he hz
  have hRP := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  have hPD := hRP.1.1
  have hInt := (hRP.2 Λ hΛ).1
  have hsz := sizes (D := D) hb (by linarith) hCT hr hT1 hT1' hTu hTu' (ZhatL (lf D F0) F')
  have hszZ := sizes (D := D) hb (by linarith) hCT hr hT1 hT1' hTu hTu' Z
  have hHle : Hp Λ (lf D F0) F' ≤ orth (hS D) (Xplus (lf D F0)) := by
    intro x hx
    unfold Hp at hx
    rw [Formalism.MainNotions.mem_orth_iff] at hx ⊢
    intro y hy
    apply hx y
    show y ∈ UUE Λ (lf D F0) F'
    rw [hUUE]
    exact Submodule.mem_sup_left hy
  have hbot : (Xplus (lf D F0) ⊔ Xplus F') ⊓ orth (hS D) (Xplus (lf D F0) ⊔ Xplus F') = ⊥ :=
    sup_inf_orth (lf D F0).fl F'.fl hG'
  have hHX : Hp Λ (lf D F0) F' ⊓ Xsp (lf D F0) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx3 : x ∈ (Xplus (lf D F0) ⊔ Xplus F') ⊓ orth (hS D) (Xplus (lf D F0) ⊔ Xplus F') := by
      refine Submodule.mem_inf.2 ⟨Submodule.mem_sup_left ?_, ?_⟩
      · exact (le_sup_left : (lf D F0).fl.X ≤ (lf D F0).fl.X ⊔ Submodule.span D.host.E {(lf D F0).fl.z}) hx2
      · rw [← hUUE]
        exact hx1
    rw [hbot] at hx3
    exact hx3
  have hfinV := Formalism.MainNotions.finrank_hS D
  have horth := finrank_orth_le (lf D F0).fl F'.fl hG' hTne hTne'
  have hHpfin : finrank D.host.E (Hp Λ (lf D F0) F') + 2 * (D.R.rS + 1) ≤ finrank D.host.E (hS D).V := by
    unfold Hp
    rw [hUUE]
    exact horth
  have hThle : ∀ (F'' : Fg D ((Tu D u' : ℕ) : D.host.E)) (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
      Th Λ (lf D F0) F' F'' β ≤ Hp Λ (lf D F0) F' := by
    intro F'' β x hx
    unfold Th at hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
    unfold ThPairs at hp
    exact (Submodule.mem_prod.1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hp).1).1).1
  have hThEq : ∀ (F'' : Fg D ((Tu D u' : ℕ) : D.host.E)) (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
      s0 Λ (lf D F0) F' F'' β D.R.k = 1 → Th Λ (lf D F0) F' F'' β = Hp Λ (lf D F0) F' := by
    intro F'' β hs
    unfold s0 at hs
    refine Submodule.eq_of_le_of_finrank_le (hThle F'' β) ?_
    omega
  by_cases hne : (Partners D Λ (lf D F0) F' Z).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : cntPartners D Λ (lf D F0) F' Z = 0 := by
      unfold cntPartners cntCl
      rw [hne]
      simp
    rw [h0]
    simp
  obtain ⟨F₁, -, -, -, β₁, -, hs₁⟩ := hne
  have hrank : finrank D.host.E (Hp Λ (lf D F0) F') = D.R.k - 1 := by
    have hE := hThEq F₁ β₁ hs₁
    unfold s0 at hs₁
    rw [hE] at hs₁
    omega
  have hsub : Partners D Λ (lf D F0) F' Z ⊆
      FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z (seen D (lf D F0) (Thp Λ (lf D F0) F')) := by
    rintro F'' ⟨hterm'', hgen'', hZ'', β, hpair, hs⟩
    refine ⟨hterm'', hZ'', ?_⟩
    have hterm3 := hterm''
    obtain ⟨⟨hlift'', -, hG''⟩, -, hXS''⟩ := hterm3
    have hfr'' : ∀ b, frame F'' b ∈ Λ := frame_mem_of_XS F'' hlift'' hXS''
    have hTh := hThEq F'' β hs
    intro w hw
    rw [mem_seen] at hw ⊢
    obtain ⟨x, hx, hxw⟩ := hw
    have hxΛ : x ∈ Λ := (Submodule.mem_inf.1 hx).1
    have hxH : x ∈ Hp Λ (lf D F0) F' := (Submodule.mem_inf.1 hx).2
    have hxT : x ∈ Th Λ (lf D F0) F' F'' β := by rw [hTh]; exact hxH
    obtain ⟨y, hy, hxy⟩ := exists_partner_lift hg (lf D F0) F' F'' β hlift hlift' hlift'' hfr hfr' hfr''
      hG'' hgen'' hpair hxΛ hxT
    refine ⟨y, hy, ?_⟩
    have := Submodule.add_mem _ hxw hxy
    rwa [sub_add_sub_cancel] at this
  have hPL0 : seen D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) :=
    seen_le_L0X (lf D F0) (Hp Λ (lf D F0) F') hHle
  have hrk : rkW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 := by
    rw [← hrank]
    exact rk_seen (lf D F0) hlat hW (Hp Λ (lf D F0) F') hHle hHX
  have hXle : Xplus (lf D F0) ≤ spanE (hS D) (UU Λ (lf D F0) F') := by
    show Xplus (lf D F0) ≤ UUE Λ (lf D F0) F'
    rw [hUUE]
    exact le_sup_left
  have hnd : spanE (hS D) (UU Λ (lf D F0) F') ⊓ orth (hS D) (spanE (hS D) (UU Λ (lf D F0) F')) = ⊥ := by
    show UUE Λ (lf D F0) F' ⊓ orth (hS D) (UUE Λ (lf D F0) F') = ⊥
    rw [hUUE]
    exact hbot
  have hdet : detW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) ≤ NG Λ (lf D F0) F' :=
    det_seen_le (lf D F0) hlat huni hW (fun τ x hx => hPD τ x hx) hInt (UU Λ (lf D F0) F')
      (UU_le (lf D F0) F' hlift hlift') hXle hnd
  have hNG := GlobalTheory.LoopC.FrameDet.main D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hHyp F0 he hz Λ hΛ F' hterm hgen
  have hdetH : detW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) ≤ HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') := by
    rw [hNG] at hdet
    exact hdet.trans hsz.2.2
  have hHh1 : 1 ≤ HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    one_le_mul_of_one_le_of_one_le hsz.1 hszZ.1
  have hHZ : HHZ D large₂.sc.b (max (max C₀ 37) CT) Z ≤
      HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    le_mul_of_one_le_left (by linarith [hszZ.1]) hsz.1
  have hZ'le : HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') ≤
      HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    le_mul_of_one_le_right (by linarith [hsz.1]) hszZ.1
  have hDeH : max 1 (detW D (seen D (lf D F0) (Thp Λ (lf D F0) F'))) ≤
      HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    max_le hHh1 (hdetH.trans hZ'le)
  have hDe3 : max 1 (detW D (seen D (lf D F0) (Thp Λ (lf D F0) F'))) ≤
      (HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z) ^ 3 :=
    hDeH.trans (le_self_pow₀ hHh1 (by norm_num))
  have hcnt := hC₀ (max (max C₀ 37) CT) hCC₀ D large₂ u u' C' Cl hCl hHyp F0 he hz Λ hΛ Z hZ 1 le_rfl hk1
    (seen D (lf D F0) (Thp Λ (lf D F0) F')) hPL0 hrk
    (max 1 (detW D (seen D (lf D F0) (Thp Λ (lf D F0) F'))))
    (HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z)
    (le_max_left _ _) (le_max_right _ _) hHZ hDe3
  have hN0 : 0 ≤ NT D u := by unfold NT; positivity
  have hN : NT D u ≤ HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    (hsz.2.1 : NT D u ≤ _).trans hZ'le
  have hfin := final_arith (f := D.R.f) hr hN0 hN (le_max_left _ _) hDeH hC37
  calc (cntPartners D Λ (lf D F0) F' Z : ℝ≥0∞)
      ≤ (cntCl (FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z (seen D (lf D F0) (Thp Λ (lf D F0) F')))
          (TEqv D Λ (lf D F0)) : ℝ≥0∞) := by
        unfold cntPartners
        exact_mod_cast cntCl_mono hsub _
    _ ≤ _ := hcnt
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

end Count

end GlobalTheory.LoopC.Partner
end

section
section
open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.LoopC.AdmissibleOrder

open GlobalTheory.LoopC.Partner

theorem one_mem_of_local {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (J : Ideal (𝓞 E)) (hg : g ∈ J)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∃ s ∈ J, s ∉ P.asIdeal) : (1 : 𝓞 E) ∈ J := by
  by_contra h1
  have hJ : J ≠ ⊤ := fun hJ => h1 (hJ ▸ Submodule.mem_top)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField E)
  obtain ⟨s, hsJ, hsM⟩ := h ⟨M, hM.isPrime, hM0⟩ (hJM hg)
  exact hsM (hJM hsJ)

theorem pow_card_le {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] [Finite Q] (I : Ideal R) {n : ℕ}
    (q : Fin n → Q) (h : ∀ c : Fin n → R, ∑ b, c b • q b = 0 → ∀ b, c b ∈ I) :
    Nat.card (R ⧸ I) ^ n ≤ Nat.card Q := by
  have key : ∀ c c' : Fin n → R, ∑ b, c b • q b = ∑ b, c' b • q b →
      ∀ b, Ideal.Quotient.mk I (c b) = Ideal.Quotient.mk I (c' b) := by
    intro c c' hcc b
    rw [Ideal.Quotient.eq]
    have hz : ∑ b, (c - c') b • q b = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcc, sub_self]
    simpa using h (c - c') hz b
  let f : Q → (Fin n → R ⧸ I) := fun x =>
    if hx : ∃ c : Fin n → R, ∑ b, c b • q b = x then fun b => Ideal.Quotient.mk I (hx.choose b) else 0
  have hf : Function.Surjective f := by
    intro t
    choose c hc using fun b => Ideal.Quotient.mk_surjective (I := I) (t b)
    have hx : ∃ c' : Fin n → R, ∑ b, c' b • q b = ∑ b, c b • q b := ⟨c, rfl⟩
    refine ⟨∑ b, c b • q b, ?_⟩
    simp only [f, dif_pos hx]
    funext b
    rw [key _ c hx.choose_spec b, hc]
  have hle := Nat.card_le_card_of_surjective f hf
  simpa [Nat.card_fun] using hle

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem frame_indep (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (b : Fin (r + 1) → E)
    (hb : ∑ j, b j • F'.fvec j = 0) : b = 0 := by
  have hlast : T' * b (Fin.last r) = 0 := by
    have h0 := hT_fvec_sum F' b (Fin.last r)
    rw [hb, map_zero] at h0
    simpa using h0.symm
  have hZ : (Zhat F F').mulVec b = Pi.single (Fin.last r) (T * (0 : Fin (r + 1) → E) (Fin.last r)) := by
    funext i
    have h0 : S.hT (F.fvec i) (∑ j, b j • F'.fvec j) = 0 := by rw [hb, map_zero]
    rw [map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    simp only [Pi.zero_apply, mul_zero, Pi.single_zero]
    rw [← h0]
    simp only [Matrix.mulVec, dotProduct, Zhat, brS]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h2 : (Zhat F F').conjTranspose.mulVec (0 : Fin (r + 1) → E) = Pi.single (Fin.last r) (T' * b (Fin.last r)) := by
    rw [hlast, Matrix.mulVec_zero, Pi.single_zero]
  have hd1 : Dl F F' (r + 1) = (Zhat F F').det := by
    unfold Dl leadMinorE
    rw [dif_pos le_rfl]
    congr 1
  have hd0 : Dl F F' r = ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det := by
    unfold Dl leadMinorE
    rw [dif_pos (Nat.le_succ r)]
    congr 1
  have hG' := hG
  unfold Gflag at hG'
  rw [hd1, hd0] at hG'
  exact (pair_eq_zero (Zhat F F') 0 b T T' hG' hZ h2).2

variable {Λ : Submodule (𝓞 E) S.V}

theorem exists_div {g : ℕ} {x : S.V} (hx : x ∈ Λ) (h : ModG S Λ g x) : ∃ w ∈ Λ, (g : 𝓞 E) • w = x := by
  set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)} • Λ).colon {x} with hJ
  have hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ := fun s =>
    Submodule.mem_colon_singleton
  have h1 : (1 : 𝓞 E) ∈ J := by
    refine one_mem_of_local (g : 𝓞 E) J
      ((hmem _).2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx)) ?_
    intro P hP
    obtain ⟨s, hs, hsx⟩ := h P hP
    exact ⟨s, (hmem s).2 hsx, hs⟩
  have hx1 := (hmem 1).1 h1
  rw [one_smul, Submodule.ideal_span_singleton_smul] at hx1
  obtain ⟨w, hw, hwx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx1
  exact ⟨w, hw, hwx⟩

theorem coeff_mem {g : ℕ} (F : LFlag S r T) (hL : IsLift Λ F) (hC : IsFixedConv Λ g F)
    (hind : ∀ b : Fin (r + 1) → E, ∑ j, b j • frame F j = 0 → b = 0) (c : Fin (r + 1) → 𝓞 E) {q : S.V}
    (hq : q ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt}) (h : ∑ j, c j • frame F j = (g : 𝓞 E) • q) (b : Fin (r + 1)) :
    c b ∈ Ideal.span {(g : 𝓞 E)} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hq
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
  set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)}).colon {c b} with hJ
  have hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • c b ∈ Ideal.span {(g : 𝓞 E)} := fun s =>
    Submodule.mem_colon_singleton
  have key : ∀ s : 𝓞 E, s • x ∈ Submodule.span (𝓞 E) (Set.range F.fl.e) → s ∈ J := by
    intro s hs
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hs
    let d' : Fin (r + 1) → 𝓞 E := Fin.snoc (α := fun _ => 𝓞 E) d (s * o)
    have e1 : ∑ j, d' j • frame F j = s • x + (s * o) • F.zt := by
      rw [Fin.sum_univ_castSucc]
      simp only [d', frame, FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last, hd, hL.2]
    have hsum : ∑ j, ((s * c j - (g : 𝓞 E) * d' j : 𝓞 E) : E) • frame F j = 0 := by
      simp only [smul_coe]
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [← Finset.smul_sum, ← Finset.smul_sum, h, e1]
      module
    have hb0 : ((s * c b - (g : 𝓞 E) * d' b : 𝓞 E) : E) = 0 := congrFun (hind _ hsum) b
    have hb1 : s * c b = (g : 𝓞 E) * d' b := by
      rw [← sub_eq_zero]
      exact_mod_cast hb0
    rw [hmem, smul_eq_mul, hb1]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h1 : (1 : 𝓞 E) ∈ J := by
    refine one_mem_of_local (g : 𝓞 E) J ?_ ?_
    · rw [hmem, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro P hP
      obtain ⟨cc, -, hc1, hloc⟩ := hC.1 P
      have hx' : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F)) := by
        show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ XLam Λ F
        exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
      rw [hloc] at hx'
      obtain ⟨s, hs, hsx⟩ := hx'
      refine ⟨s, key s ?_, hs⟩
      have hfun : (fun a => cc a • F.fl.e a) = F.fl.e := funext fun a => by rw [hc1 hP a, one_smul]
      rwa [hfun] at hsx
  simpa using (hmem 1).1 h1

theorem NE_pow_le_card_BQ : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → Gval F F' ≠ 0 → Finite (BQ Λ F F') → NE (E := E) g ^ (r + 1) ≤ (Nat.card (BQ Λ F F') : ℝ) := by
  intro E _ _ _ S r Λ g T T' F F' hg hL hL' hF hF' hC' hAdm hGv hfin
  obtain ⟨ξ, -, -, hξ⟩ := hAdm
  have hfX : ∀ b, frameAct (frame F) ξ b ∈ Xplus F :=
    fun b => (mem_Xplus_iff F.fl _).2 ⟨fun a => ((ξ a b : 𝓞 E) : E), rfl⟩
  have hf'X : ∀ b, frame F' b ∈ Xplus F' := fun b =>
    (mem_Xplus_iff F'.fl _).2 ⟨Pi.single b 1, by simp [Pi.single_apply, ite_smul]⟩
  have hxΛ : ∀ b, frame F' b - frameAct (frame F) ξ b ∈ Λ := by
    intro b
    refine Λ.sub_mem (hF' b) (Λ.sum_mem fun a _ => ?_)
    rw [smul_coe]
    exact Λ.smul_mem _ (hF a)
  choose w hwΛ hw using fun b => exists_div (hxΛ b) (hξ b)
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have hwB : ∀ b, w b ∈ BLat Λ F F' := by
    intro b
    refine Submodule.mem_inf.2 ⟨hwΛ b, ?_⟩
    show w b ∈ UUE Λ F F'
    rw [UUE_eq F F' hL hL' hF hF']
    have hwb : w b = (g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b) := by
      rw [← hw b, ← smul_coe, smul_smul]
      have hc : (((g : 𝓞 E) : E)) = (g : E) := by simp
      rw [hc, inv_mul_cancel₀ hgE, one_smul]
    rw [hwb]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.mem_sup_right (hf'X b)) (Submodule.mem_sup_left (hfX b)))
  have _hfin := hfin
  let q : Fin (r + 1) → BQ Λ F F' := fun b => Submodule.Quotient.mk ⟨w b, hwB b⟩
  have key : ∀ c : Fin (r + 1) → 𝓞 E, ∑ b, c b • q b = 0 → ∀ b, c b ∈ Ideal.span {(g : 𝓞 E)} := by
    intro c hc
    have hc' : ∑ b, c b • w b ∈ UU Λ F F' := by
      have h0 : (Submodule.mkQ ((UU Λ F F').comap (BLat Λ F F').subtype))
          (∑ b, c b • (⟨w b, hwB b⟩ : BLat Λ F F')) = 0 := by
        rw [map_sum]
        simpa only [map_smul, Submodule.mkQ_apply, q] using hc
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
      simpa using h0
    rw [UU_eq] at hc'
    obtain ⟨u, hu, u', hu', huu⟩ := Submodule.mem_sup.1 hc'
    have hgsum : ∑ b, c b • (frame F' b - frameAct (frame F) ξ b) = (g : 𝓞 E) • u + (g : 𝓞 E) • u' := by
      rw [← smul_add, huu, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hw b, smul_comm]
    simp only [smul_sub, Finset.sum_sub_distrib] at hgsum
    have hA : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' =
        ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by
      calc ∑ b, c b • frame F' b - (g : 𝓞 E) • u'
          = (∑ b, c b • frame F' b - ∑ b, c b • frameAct (frame F) ξ b) +
              ∑ b, c b • frameAct (frame F) ξ b - (g : 𝓞 E) • u' := by abel
        _ = ((g : 𝓞 E) • u + (g : 𝓞 E) • u') + ∑ b, c b • frameAct (frame F) ξ b - (g : 𝓞 E) • u' := by
              rw [hgsum]
        _ = ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by abel
    have huX : u ∈ Xplus F := (Submodule.mem_inf.1 (half_le F hL hu)).2
    have hu'X : u' ∈ Xplus F' := (Submodule.mem_inf.1 (half_le F' hL' hu')).2
    have hmF' : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ Xplus F' :=
      Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hf'X b))
        (Submodule.smul_of_tower_mem _ _ hu'X)
    have hmF : ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u ∈ Xplus F :=
      Submodule.add_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hfX b))
        (Submodule.smul_of_tower_mem _ _ huX)
    have hm : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ F.fl.Xplus ⊓ F'.fl.Xplus :=
      Submodule.mem_inf.2 ⟨hA ▸ hmF, hmF'⟩
    rw [Xplus_inf F.fl F'.fl hGv] at hm
    have hfin2 : ∑ b, c b • frame F' b = (g : 𝓞 E) • u' := sub_eq_zero.1 ((Submodule.mem_bot E).1 hm)
    exact coeff_mem F' hL' hC' (fun b hb => frame_indep F.fl F'.fl hGv b hb) c hu' hfin2
  have hcard := pow_card_le (Ideal.span {(g : 𝓞 E)}) q key
  have hN : ((Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) : ℕ) : ℝ) = NE (E := E) g := by
    have hn := Ideal.absNorm_span_singleton ((g : 𝓞 E))
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    rw [hn, NE]
    have hg' : ((g : 𝓞 E)) = algebraMap ℤ (𝓞 E) (g : ℤ) := by simp
    rw [hg', Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  rw [← hN]
  exact_mod_cast hcard

end GlobalTheory.LoopC.AdmissibleOrder
end

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_le_card_flag_quotient : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → Gval F F' ≠ 0 → Finite (BQ Λ F F') → NE (E := E) g ^ (r + 1) ≤ (Nat.card (BQ Λ F F') : ℝ) := by
  atlas_forward_decl GlobalTheory.LoopC.AdmissibleOrder.NE_pow_le_card_BQ
end

section
section
open scoped BigOperators

namespace GlobalTheory

private lemma exponent_product_le_G_div_N_mul_rpow (f r : ℕ) (G N H Q l d : ℝ) (hG : 1 ≤ G) (hN : 1 ≤ N)
    (hGH : G ≤ H) (hNH : N ≤ H) (hQ : 0 ≤ Q) (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d)
    (hdG : d ≤ G) :
    (G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
        (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)) ≤
      G / N * H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have hGd0 : 0 < G / d := div_pos (by linarith) hd0
  have hGdG : G / d ≤ G := div_le_self (by linarith) hd

  have h1 : (G / d) ^ (l + 3) ≤ G * H ^ (l + 2) := by
    rw [show l + 3 = 1 + (l + 2) by ring, Real.rpow_add hGd0, Real.rpow_one]
    exact mul_le_mul hGdG (Real.rpow_le_rpow hGd0.le (hGdG.trans hGH) (by linarith))
      (Real.rpow_nonneg hGd0.le _) (by linarith)

  have h2 : N ^ (2 * r) * N * (Q * 9 ^ f) ≤ H ^ (2 * r + 2) := by
    have hN2 : N ^ (2 * r) ≤ H ^ (2 * r) := pow_le_pow_left₀ hN0.le hNH _
    calc N ^ (2 * r) * N * (Q * 9 ^ f) ≤ H ^ (2 * r) * H * H :=
          mul_le_mul (mul_le_mul hN2 hNH hN0.le (pow_nonneg hH0.le _)) hQH
            (mul_nonneg hQ (by positivity)) (mul_nonneg (pow_nonneg hH0.le _) hH0.le)
      _ = H ^ (2 * r + 2) := by ring
  have h3 : G ^ r ≤ H ^ r := pow_le_pow_left₀ (by linarith) hGH r

  have hE : H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) =
      H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r * H ^ (9 + 9 * r + 16 * r ^ 2) := by
    rw [← Real.rpow_natCast H (2 * r + 2), ← Real.rpow_natCast H r,
      ← Real.rpow_natCast H (9 + 9 * r + 16 * r ^ 2), ← Real.rpow_add hH0, ← Real.rpow_add hH0,
      ← Real.rpow_add hH0, ← Real.rpow_add hH0]
    congr 1
    push_cast
    ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hN0, hE]
  have hP : 0 ≤ H ^ (11 + 3 * l) := Real.rpow_nonneg hH0.le _
  have hM : 0 ≤ N ^ (2 * r) * N * (Q * 9 ^ f) :=
    mul_nonneg (mul_nonneg (pow_nonneg hN0.le _) hN0.le) (mul_nonneg hQ (by positivity))
  have hA : 0 ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hH0.le _)) hP
  have hR : 0 ≤ G ^ r := pow_nonneg (by linarith) _
  have hS : 0 ≤ H ^ (9 + 9 * r + 16 * r ^ 2) := pow_nonneg hH0.le _
  have hAM : 0 ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) :=
    mul_nonneg hA (pow_nonneg hH0.le _)
  calc (G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)) * N
        = (G / d) ^ (l + 3) * H ^ (11 + 3 * l) * (N ^ (2 * r) * N * (Q * 9 ^ f)) * G ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2) := by ring
    _ ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h1 hP) h2 hM hA) h3 hR hAM) hS
    _ = G * (H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2)) := by ring

theorem exponent_term (k f r : ℕ) (G N H a Q l d : ℝ) (hk : 1 ≤ k)
    (hG : 1 ≤ G) (hN : 1 ≤ N) (hGH : G ≤ H) (hNH : N ≤ H) (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d) (hdG : d ≤ G) :
    (d / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * l)) *
        ((G / d) ^ ((k : ℝ) + (1 + l) + 1) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤
      H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have hGd0 : 0 < G / d := div_pos (by linarith) hd0

  have hexp : ((m + 1 : ℕ) : ℝ) + (1 + l) + 1 = (m : ℝ) + (l + 3) := by push_cast; ring
  rw [hexp, Real.rpow_add hGd0, Real.rpow_natCast, Nat.add_sub_cancel, pow_succ]
  have hdm : (d / N) ^ m * (G / d) ^ m = (G / N) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hB := exponent_product_le_G_div_N_mul_rpow f r G N H Q l d hG hN hGH hNH hQ hQH hl hd hdG
  have hX : 0 ≤ a * (G / N) ^ m := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)
  calc (d / N) ^ m * a * (Q * H ^ (11 + 3 * l)) *
          ((G / d) ^ m * (G / d) ^ (l + 3) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)))
        = a * ((d / N) ^ m * (G / d) ^ m) * ((G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) := by ring
    _ = a * (G / N) ^ m * ((G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) := by rw [hdm]
    _ ≤ a * (G / N) ^ m * (G / N * H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hB hX
    _ = H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * ((G / N) ^ m * (G / N))) := by
          ring

theorem exponent_sum_le :
    ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  intro k f r G N H a Q C hk hr hf hlog hG hN hGH hNH ha hQ hQH hC
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl0 : 0 ≤ Real.logb 2 (f : ℝ) := Real.logb_nonneg one_lt_two hf1
  have h2f : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.logb 2 f := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (by linarith)), Real.logb_self_eq_one one_lt_two]
  have hX : 0 ≤ a * (G / N) ^ k := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)

  refine le_trans (Finset.sum_le_sum (g := fun _ =>
    H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k)) ?_) ?_
  · intro de hde
    rw [Finset.mem_Icc] at hde
    have hd1 : (1 : ℝ) ≤ de := by exact_mod_cast hde.1
    have hdG : (de : ℝ) ≤ G := le_trans (Nat.cast_le.mpr hde.2) (Nat.floor_le (by linarith))
    simp only [h2f]
    exact exponent_term k f r G N H a Q (Real.logb 2 f) de hk hG hN hGH hNH ha hQ hQH
      hl0 hd1 hdG
  ·
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hfl : (⌊G⌋₊ : ℝ) ≤ H := (Nat.floor_le (by linarith)).trans hGH
    have hsq : Real.sqrt r ≤ r := by
      have h0 := Real.sqrt_nonneg (r : ℝ)
      have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ r by linarith)
      nlinarith
    have hlog2 := Real.log_two_gt_d9
    have hlb : Real.logb 2 (f : ℝ) ≤ 7 / 4 * r := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by linarith)
        (show (0 : ℝ) ≤ Real.log 2 - 0.69 by linarith)]
    have hexp : 1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) ≤
        C * (r : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg (r : ℝ))]
    have hE0 : 0 ≤ H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) :=
      Real.rpow_nonneg hH0.le _
    calc (⌊G⌋₊ : ℝ) * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k))
        ≤ H * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k)) := mul_le_mul_of_nonneg_right hfl (mul_nonneg hE0 hX)
      _ = H ^ (1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) *
            (a * (G / N) ^ k) := by rw [Real.rpow_add hH0 1, Real.rpow_one]; ring
      _ ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) hX

end GlobalTheory
end

open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_divisor_sum_le : ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  atlas_forward_decl GlobalTheory.exponent_sum_le
end

section
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.SizeQ

theorem one_le_size (D : D7) (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  refine Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl (fun τ _ => ?_)
  exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl (fun l _ => le_max_left _ _)

private lemma one_add_logb_two_mul_le_of_log_le_sqrt (f r : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (hlog : Real.log f ≤ Real.sqrt r) : 1 + Real.logb 2 (2 * (f : ℝ)) ≤ 2 * (r : ℝ) + 2 := by
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hsq : Real.sqrt r ≤ r := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hsplit : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.log f / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num) hf0.ne', add_div, div_self (by linarith)]
  have hdiv : Real.log f / Real.log 2 ≤ 2 * r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem classNumber_le (D : D7) (b : ℝ) (hb : 1 ≤ b) (hrd : D.host.rdE ≤ b) (hf : 1 ≤ D.R.f)
    (hr : 1 ≤ D.R.rS) (hlog : Real.log D.R.f ≤ Real.sqrt D.R.rS) :
    (classNumber D.host.E : ℝ) ≤ b ^ ((D.R.m : ℝ) * D.R.f) := by
  obtain ⟨-, hdeg, -, hm, hrd1, -⟩ := GlobalTheory.real_places_facts D
  have hcn := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.classNumberBound D.host.E
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hdeg' : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by rw [hdeg]; push_cast; ring

  have hdisc : |(NumberField.discr D.host.E : ℝ)| = D.host.rdE ^ (2 * (D.R.f : ℝ)) := by
    rw [Formalism.BasicNotions.Host.rdE, hdeg', ← Real.rpow_mul (abs_nonneg _), one_div,
      inv_mul_cancel₀ (by positivity), Real.rpow_one]
  rw [hdisc, hdeg', ← Real.rpow_mul (by linarith)] at hcn
  have hc := one_add_logb_two_mul_le_of_log_le_sqrt D.R.f D.R.rS hf hr hlog
  have hf1r : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hlb : 0 ≤ Real.logb 2 (2 * (D.R.f : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hm' : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by rw [hm]; push_cast; ring
  calc (classNumber D.host.E : ℝ)
      ≤ D.host.rdE ^ (2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2)) := hcn
    _ ≤ b ^ (2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2)) :=
        Real.rpow_le_rpow (by linarith) hrd (by positivity)
    _ ≤ b ^ ((D.R.m : ℝ) * D.R.f) := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        rw [hm']
        nlinarith

private lemma le_rpow_abs_div_eight_of_mul_pow_le (k b Cg g : ℝ) (hk : 0 ≤ k) (hb : 1 ≤ b) (h1 : (k * b) ^ 8 ≤ g)
    (h2 : g ≤ b ^ Cg) : k ≤ b ^ (|Cg| / 8) := by
  have hk8 : k ^ 8 ≤ b ^ |Cg| := by
    calc k ^ 8 ≤ (k * b) ^ 8 := by
          apply pow_le_pow_left₀ hk; nlinarith
      _ ≤ b ^ Cg := h1.trans h2
      _ ≤ b ^ |Cg| := Real.rpow_le_rpow_of_exponent_le hb (le_abs_self _)
  by_contra hlt
  push_neg at hlt
  have hpos : 0 ≤ b ^ (|Cg| / 8) := Real.rpow_nonneg (by linarith) _
  have := pow_lt_pow_left₀ hlt hpos (by norm_num : (8 : ℕ) ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at this
  norm_num at this
  linarith

theorem main : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ Z : GramM D, (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f ≤ HHZ D large₂.sc.b C Z := by
  intro Cg cb Cu cT CT C0 A
  refine ⟨|Cg| / 8 + 3 / 2 + 6, ?_⟩
  intro C hC D large₂ u u' C' Cl hCl hH Z
  obtain ⟨⟨hS0, -, -⟩, hSt, -⟩ := hH
  obtain ⟨-, -, hmf, -, hlogf, -, -, -, -, -, hlrd, hg1, hg1b, -, -, -, -, -, hv, -, -, -, -, -, -⟩ := hS0
  have hr : 1 ≤ D.R.rS := hSt.1
  obtain ⟨-, -, -, hm, hrd1, -⟩ := GlobalTheory.real_places_facts D

  set b := large₂.sc.b with hbdef
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hbexp : b = Real.exp large₂.sc.L := rfl
  have hrd2 : 2 ≤ D.host.rdE := by
    have : D.host.v = D.host.rdE / 2 := rfl
    linarith
  have hrdb : D.host.rdE ≤ b := by
    have hlog : Real.log D.host.rdE ≤ large₂.sc.L := by
      have : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self hL.le hCl
      linarith
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.mpr hlog
      _ = b := hbexp.symm
  have hb2 : 2 ≤ b := hrd2.trans hrdb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm4 : 4 ≤ D.R.m := by omega
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf

  have hk : (D.R.k : ℝ) ≤ b ^ (|Cg| / 8) := le_rpow_abs_div_eight_of_mul_pow_le _ _ _ _ (Nat.cast_nonneg _) hb1 hg1 hg1b
  have hsq : D.host.rdE ^ ((1 : ℝ) / 2) ≤ b ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) hrdb (by norm_num)
  have hbase : 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) ≤ b ^ (|Cg| / 8 + 3 / 2) := by
    have e : b ^ (|Cg| / 8 + 3 / 2) = b ^ (1 : ℝ) * b ^ (|Cg| / 8) * b ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; ring_nf
    rw [e, Real.rpow_one]
    have h0 : 0 ≤ D.host.rdE ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have h0' : 0 ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
    have h0'' : 0 ≤ b ^ (|Cg| / 8) := Real.rpow_nonneg hb0.le _
    calc 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) ≤ b * b ^ (|Cg| / 8) * D.host.rdE ^ ((1 : ℝ) / 2) := by
          gcongr
      _ ≤ b * b ^ (|Cg| / 8) * b ^ ((1 : ℝ) / 2) := by gcongr
  have hcls := classNumber_le D b hb1 hrdb hf1 hr hlogf
  have h18 : (2 : ℝ) ^ D.R.f * 9 ^ D.R.f ≤ b ^ ((5 : ℝ) * D.R.f) := by
    rw [← mul_pow, Real.rpow_mul hb0.le, Real.rpow_natCast]
    apply pow_le_pow_left₀ (by norm_num)
    have : (2 : ℝ) ^ (5 : ℝ) ≤ b ^ (5 : ℝ) := Real.rpow_le_rpow (by norm_num) hb2 (by norm_num)
    have h32 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
    linarith

  set e1 : ℝ := |Cg| / 8 + 3 / 2 with he1
  have he1n : 0 ≤ e1 := by positivity
  have hpow : (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f ≤ b ^ (e1 * D.R.f) := by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hprod : (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f
      ≤ b ^ ((e1 + D.R.m + 5) * D.R.f) := by
    have e : b ^ ((e1 + D.R.m + 5) * D.R.f) = b ^ (e1 * D.R.f) * b ^ ((D.R.m : ℝ) * D.R.f) * b ^ ((5 : ℝ) * D.R.f) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; ring_nf
    rw [e, mul_assoc _ ((2 : ℝ) ^ D.R.f)]
    have hc0 : (0 : ℝ) ≤ classNumber D.host.E := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ D.R.f * 9 ^ D.R.f := by positivity
    gcongr

  have hm1 : (4 : ℝ) ≤ D.R.m := by exact_mod_cast hm4
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |Cg| / 8 := by positivity
    linarith
  have hexp : (e1 + D.R.m + 5) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have h1 : e1 + D.R.m + 5 ≤ C * D.R.m := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C - (e1 + 6)) (by linarith : (0 : ℝ) ≤ D.R.m),
        mul_nonneg he1n (by linarith : (0 : ℝ) ≤ D.R.m - 1)]
    have hm2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h2 : 1 ≤ C * (D.R.m : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hC1 hm2
    have h3 : e1 + D.R.m + 5 ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) :=
      h1.trans (le_mul_of_one_le_left (by positivity) h2)
    calc (e1 + D.R.m + 5) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) * D.R.f :=
          mul_le_mul_of_nonneg_right h3 hf0
      _ = C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by ring
  have hsz := one_le_size D b C Z
  unfold HHZ
  rw [← Real.rpow_mul hb0.le]
  calc _ ≤ b ^ ((e1 + D.R.m + 5) * D.R.f) := hprod
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_le_rpow_of_exponent_le hb1 hexp
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) * sizeZ D b C Z ^ 4 := by
        have : 1 ≤ sizeZ D b C Z ^ 4 := one_le_pow₀ hsz
        have : 0 ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_nonneg hb0.le _
        nlinarith

end GlobalTheory.LoopC.SizeQ
end

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_rootDisc_factor_le_HHZ : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ Z : GramM D, (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f ≤ HHZ D large₂.sc.b C Z := by
  atlas_forward_decl GlobalTheory.LoopC.SizeQ.main
end

section
namespace GlobalTheory.LoopC.GenericMean

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lead_eq {E : Type} [Field E] {n : ℕ} {Z Z₂ : Matrix (Fin n) (Fin n) E} (h : ZEquiv Z Z₂) (l : ℕ) :
    leadMinorE Z₂ l = leadMinorE Z l := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ := h
  unfold leadMinorE
  split_ifs with hl
  · exact Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.leadingMinorInvariant E n l hl _ Z _ (fun i => by simp [hA1])
      (fun i j hij => by simp [hA0 i j hij]) (fun i => by simp [hB1]) (fun i j hij => by simp [hB0 i j hij])
  · rfl

open GlobalTheory.Mass GlobalTheory.LoopC.DetCard Formalism.HermitianLatticesTheory in

theorem det_index {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (M P : Submodule (𝓞 K) V) (hM : M.FG) (hI : IsIntegralLat h M) (hP : P ≤ M)
    (hU : Submodule.span K (P : Set V) = Submodule.span K (M : Set V))
    (hn : ∀ x ∈ Submodule.span K (M : Set V), (∀ y ∈ Submodule.span K (M : Set V), h y x = 0) → x = 0) :
    idxN M P ≠ 0 ∧ latDetH h P = latDetH h M * idxN M P := by
  have hIP : IsIntegralLat h P := fun x hx y hy => hI x (hP hx) y (hP hy)
  obtain ⟨-, m3⟩ := Partner.det_sq h hK hs M hM hI hn
  obtain ⟨-, p3⟩ := Partner.det_sq h hK hs P (hM.of_le hP) hIP (hU ▸ hn)
  set U := Submodule.span K (M : Set V) with hUd
  have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
  have hnU : (hRes h U).Nondegenerate :=
    ⟨fun x hx => Subtype.ext (hn x x.2 fun y hy => RowPerp.swap_zero hs (hx ⟨y, hy⟩)),
      fun x hx => Subtype.ext (hn x x.2 fun y hy => hx ⟨y, hy⟩)⟩
  have m1 : IsIntLat (hRes h U) (latIn U M) :=
    ⟨isLattice_latIn_span hM rfl, fun x hx y hy => hI x hx y hy⟩
  have p1 : IsIntLat (hRes h U) (latIn U P) :=
    ⟨isLattice_latIn_span (hM.of_le hP) hU, fun x hx y hy => hIP x hx y hy⟩
  obtain ⟨q1, q2⟩ := (DiscOrder.main K U _ hK hsU hnU _ p1).2.2.1 _ m1 (Submodule.comap_mono hP)
  rw [← idxN_latIn (U := U) (fun x hx => Submodule.subset_span hx)
    (fun x hx => Submodule.subset_span (hP hx))] at q1 q2
  refine ⟨q1, ?_⟩
  rw [p3, m3, idxN_dualInH h hU, idxN_dualInH h hUd.symm, q2, Nat.cast_mul, Nat.cast_pow,
    Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

theorem le_finrank_orth {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') :
    finrank E S.V ≤ finrank E (orth S (F.Xplus ⊔ F'.Xplus)) + 2 * (r + 1) := by
  let φ : S.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E) := LinearMap.pi fun i => S.hT (Sum.elim F.fvec F'.fvec i)
  have h1 := φ.finrank_range_add_finrank_ker
  have h2 := Submodule.finrank_le (LinearMap.range φ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h2
  have h3 : LinearMap.ker φ ≤ orth S (F.Xplus ⊔ F'.Xplus) := fun v hv => by
    have hv' : ∀ i, S.hT (Sum.elim F.fvec F'.fvec i) v = 0 := fun i => congrFun (LinearMap.mem_ker.1 hv) i
    refine (Formalism.MainNotions.mem_orth_iff _ _).2 fun x hx => ?_
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, LinearMap.add_apply,
      Formalism.MainNotions.hT_zero_of_mem_Xplus F (fun a => by simpa [FlagG.fvec] using hv' (.inl a.castSucc))
        (by simpa [FlagG.fvec] using hv' (.inl (Fin.last r))) p hp,
      Formalism.MainNotions.hT_zero_of_mem_Xplus F' (fun a => by simpa [FlagG.fvec] using hv' (.inr a.castSucc))
        (by simpa [FlagG.fvec] using hv' (.inr (Fin.last r))) q hq, add_zero]
  have h4 := Submodule.finrank_mono h3
  omega

theorem orth_lattice (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D) (hs : Stand D u u')
    (hb : IsBase D u F0) (hΛ : IsRowLat D F0 Λ) (F' : FlagU D u') (hF' : IsTermF D Λ (lf D F0) F') :
    seen D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) ∧
      rkW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 ∧
      detW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) ≤ G0 Λ (gS D) (lf D F0) F' := by
  obtain ⟨hW, -, hpd, b4, b5, -⟩ := Base.main D u u' F0 Λ hs hb hΛ
  obtain ⟨-, ⟨hL, hu, hl, -⟩, hX⟩ := id hΛ
  obtain ⟨⟨hl', had, hG⟩, hc', hX'⟩ := hF'
  have hF := Partner.frame_mem_of_XS (lf D F0) hl hX
  have hF' := Partner.frame_mem_of_XS F' hl' hX'
  have n1 := Partner.UUE_eq (lf D F0) F' hl hl' hF hF'
  have n2 : UUE Λ (lf D F0) F' ⊓ orth (hS D) (UUE Λ (lf D F0) F') = ⊥ := by
    rw [n1]; exact Partner.sup_inf_orth F0 F'.fl hG
  have n3 : finrank D.host.E (Hp Λ (lf D F0) F') = D.R.k - 1 := by
    have a1 := Partner.finrank_orth_le F0 F'.fl hG (Nat.cast_ne_zero.2 hs.2.1.ne_zero)
      (Nat.cast_ne_zero.2 hs.2.2.1.ne_zero)
    have a2 := le_finrank_orth F0 F'.fl
    have a3 := Formalism.MainNotions.finrank_hS D
    rw [Hp, n1]
    change finrank D.host.E (orth (VS D) (F0.Xplus ⊔ F'.fl.Xplus)) = _
    change finrank D.host.E (VS D).V = _ at a3
    omega
  have hXp : Xplus (lf D F0) ≤ UUE Λ (lf D F0) F' := n1 ▸ le_sup_left
  have hH : Hp Λ (lf D F0) F' ≤ orth (hS D) (Xplus (lf D F0)) := fun x hx =>
    (Formalism.MainNotions.mem_orth_iff _ _).2 fun y hy => (Formalism.MainNotions.mem_orth_iff _ _).1 hx y (hXp hy)
  have hle := Partner.UU_le (lf D F0) F' hl hl'
  have hsp : spanE (hS D) (BLat Λ (lf D F0) F') = UUE Λ (lf D F0) F' := GlobalTheory.Mass.DetAgree.span_inf_eq Λ hL _
  have d1 := Partner.det_seen_le (lf D F0) hL hu hW hpd ⟨b4, b5⟩ (BLat Λ (lf D F0) F') inf_le_left
    (hsp ▸ hXp) (hsp ▸ n2)
  rw [hsp] at d1
  obtain ⟨g1, g2⟩ := det_index (hS D).hT D.sp.cm.cmUnram (hS D).herm (BLat Λ (lf D F0) F') (UU Λ (lf D F0) F')
    (hL.fg.of_le inf_le_left)
    (fun x hx y hy => (Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).1 (hu.ge hy.1) x hx.1)
    (fun x hx => ⟨hle hx, Submodule.subset_span hx⟩) hsp.symm (fun x hx H =>
      (Submodule.mem_bot _).1 (n2.le ⟨hsp.le hx, (Formalism.MainNotions.mem_orth_iff _ _).2 fun y hy => H y (hsp.ge hy)⟩))
  have hg : gS D ≠ 0 := mul_ne_zero hs.2.2.2.2.2.2.2.1.ne_zero hs.2.2.2.2.2.2.2.2.1.ne_zero
  have hB := GlobalTheory.T.norm_pow_le_card_flag_quotient _ (hS D) _ Λ (gS D) _ _ (lf D F0) F' hg hl hl' hF hF' hc' had hG
    (Nat.finite_of_card_ne_zero g1)
  refine ⟨Partner.seen_le_L0X _ _ hH, (Partner.rk_seen _ hL hW _ hH ?_).trans n3, d1.trans ?_⟩
  · rw [eq_bot_iff, ← n2, inf_comm]
    exact inf_le_inf (le_sup_left.trans hXp) le_rfl
  · have hN : 0 < NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) := by
      unfold NE
      have : (0 : ℝ) < gS D := Nat.cast_pos.2 (Nat.pos_of_ne_zero hg)
      positivity
    rw [G0, le_div_iff₀ hN, NG, latDet, latDet, g2]
    exact mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)

theorem sub_count (D : D7) (L : LatW D) (hp : IsPosDef (D.sp.X 0).hT)
    (hk : finrank D.host.E (D.sp.X 0).V = D.R.k) (hL : L.FG) (hI : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L)
    (n : ℕ) (G : ℝ) :
    (Set.encard {P : LatW D | P ≤ L ∧ rkW D P = n ∧ detW D P ≤ G} : ℝ≥0∞) ≤
      ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, (cntPrim (D.sp.X 0).hT L n de : ℝ≥0∞) *
        ENNReal.ofReal ((G / (de : ℝ)) ^ ((D.R.k : ℝ) + lg2f D.R.f + 1)) := by
  rcases le_or_gt 1 G with hG | hG
  · exact SubCount.main D L hp hk hL hI n G hG
  · have : {P : LatW D | P ≤ L ∧ rkW D P = n ∧ detW D P ≤ G} = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro P ⟨h1, -, h2⟩
      obtain ⟨a, b, -⟩ := DetCard.main D P (hL.of_le h1) hp fun x hx y hy => hI x (h1 hx) y (h1 hy)
      have c : (1 : ℝ) ≤ detW D P ^ 2 := by rw [← b]; exact_mod_cast a
      have d : 0 ≤ detW D P := Real.sqrt_nonneg _
      nlinarith
    simp [this]

theorem cntCl_le_encard_mul {α ι : Type} {R : α → α → Prop} (hR : Equivalence R) (X : Set α) (I : Set ι)
    (Y : ι → Set α) (B : ℝ≥0∞) (hB0 : B ≠ 0) (h : ∀ a ∈ X, ∃ i ∈ I, a ∈ Y i)
    (hY : ∀ i ∈ I, (cntCl (Y i) R : ℝ≥0∞) ≤ B) : (cntCl X R : ℝ≥0∞) ≤ (I.encard : ℝ≥0∞) * B := by
  by_cases hI : I.Finite
  · have h1 := FrEqv.cntCl_le_sum hR hI.toFinset X Y fun a ha => by
      obtain ⟨i, hi, hi'⟩ := h a ha
      exact ⟨i, hI.mem_toFinset.2 hi, a, hi', hR.refl a⟩
    have h2 : (cntCl X R : ℝ≥0∞) ≤ ∑ i ∈ hI.toFinset, (cntCl (Y i) R : ℝ≥0∞) := by
      have := ENat.toENNReal_le.2 h1
      refine this.trans (le_of_eq ?_)
      exact map_sum ENat.toENNRealRingHom _ _
    refine h2.trans ((Finset.sum_le_card_nsmul _ _ B fun i hi => hY i (hI.mem_toFinset.1 hi)).trans ?_)
    rw [hI.encard_eq_coe_toFinset_card, nsmul_eq_mul]
    simp
  · rw [Set.Infinite.encard_eq hI, ENat.toENNReal_top, ENNReal.top_mul hB0]
    exact le_top

theorem prod_nV (D : D7) (u u' : D.what₂.Word) (Z : GramM D) (hg : gS D ≠ 0) :
    ∏ τ, nV D (Tu D u) (Tu D u') Z τ = (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
      ((∏ τ, Gz D (Tu D u) (Tu D u') Z τ) / NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) / NT D u) ^ D.R.k := by
  obtain ⟨hcard, hE, -, hm, -⟩ := GlobalTheory.real_places_facts D
  have hg' : (0 : ℝ) < gS D := Nat.cast_pos.2 (Nat.pos_of_ne_zero hg)
  have e : ∀ τ, nV D (Tu D u) (Tu D u') Z τ = ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) *
      (((gS D : ℝ) ^ D.R.m)⁻¹ * (Tu D u : ℝ)⁻¹) * Gz D (Tu D u) (Tu D u') Z τ) ^ D.R.k := fun τ => by
    rw [nV, Real.rpow_neg hg'.le, Real.rpow_natCast]
    congr 1
    ring
  simp only [e]
  rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, NE, hE, hm, NT,
    mul_comm D.R.k D.R.f, pow_mul, ← mul_pow]
  congr 1
  unfold Tu
  ring

theorem main : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → (Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ de : ℕ, 1 ≤ de → ∀ HH : ℝ, (de : ℝ) ≤ HH → NT D u ≤ HH → MeanLe D F0 what₂ (fun Λ => cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - 1) de) (((de : ℝ) / NT D u) ^ (D.R.k - 1) * (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) * (((2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f) * HH ^ (11 + 3 * Real.logb 2 D.R.f)))) → Formalism.MainNotions.S.UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C1, h1⟩ := GlobalTheory.T.count_terms_gramClass_over_sublattice Cg cb Cu cT CT C0 A
  obtain ⟨C3, h3⟩ := GlobalTheory.T.classNumber_rootDisc_factor_le_HHZ Cg cb Cu cT CT C0 A
  refine ⟨max (max C1 CT) (max C3 60), fun D large₂ u u' C' Cl hCl hP hH F0 he hz what₂ hrows Z hZ => ?_⟩
  set C := max (max C1 CT) (max C3 60) with hC
  have c1 : C ≥ C1 := (le_max_left _ _).trans (le_max_left _ _)
  have c2 : CT ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have c3 : C ≥ C3 := (le_max_left _ _).trans (le_max_right _ _)
  have c4 : 60 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hs : Stand D u u' := hH.2.1
  have hS0 := hH.1.1
  have hg : gS D ≠ 0 := mul_ne_zero hs.2.2.2.2.2.2.2.1.ne_zero hs.2.2.2.2.2.2.2.2.1.ne_zero
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (lt_of_lt_of_le two_pos D.R.two_le_m)) hS0.2.2.1
  have hk : 1 ≤ D.R.k := hf.trans hS0.2.2.2.1
  have hlog : Real.log D.R.f ≤ Real.sqrt D.R.rS := hS0.2.2.2.2.1
  have hv : 1 ≤ D.host.v := hS0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTb := hS0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (zero_lt_one.trans large₂.sc.one_lt_alt).le _)
  obtain ⟨-, z1, z2⟩ : _ ∧ NT D u ≤ _ ∧ _ := Partner.sizes hb (by linarith : 2 ≤ C) c2 hs.1
    (Nat.one_le_cast.2 hs.2.1.one_le : (1 : ℝ) ≤ Tu D u) (Nat.one_le_cast.2 hs.2.2.1.one_le : (1 : ℝ) ≤ Tu D u')
    (hTb u).2 (hTb u').2 Z
  have z3 := h3 C c3 D large₂ u u' C' Cl hCl hH Z
  set H := HHZ D large₂.sc.b C Z with hHd
  set G := (∏ τ, Gz D (Tu D u) (Tu D u') Z τ) / NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) with hGd
  have hN : 1 ≤ NT D u := one_le_pow₀ (Nat.one_le_cast.2 hs.2.1.one_le)
  have hH1 : 1 ≤ H := hN.trans z1
  have hNE : 1 ≤ NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) :=
    one_le_pow₀ (one_le_pow₀ (Nat.one_le_cast.2 (Nat.pos_of_ne_zero hg)))
  have hGH : G ≤ H := by
    rw [hGd, div_le_iff₀ (one_pos.trans_le hNE)]
    exact z2.trans (le_mul_of_one_le_right (zero_le_one.trans hH1) hNE)
  set G' := max G 1 with hG'
  set B := NT D u ^ (2 * D.R.rS) * G' ^ D.R.rS * 9 ^ D.R.f * H ^ (9 + 9 * D.R.rS + 16 * D.R.rS ^ 2) with hB
  have hG'1 : 1 ≤ G' := le_max_right _ _
  have hB0 : 0 < B := by positivity
  have row : ∀ Λ ∈ what₂, (cntSW D ((Tu D u' : ℕ) : D.host.E) (lf D F0) Λ Z : ℝ≥0∞) ≤
      ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, (cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - 1) de : ℝ≥0∞) *
        ENNReal.ofReal ((G / de) ^ ((D.R.k : ℝ) + Real.logb 2 (2 * D.R.f) + 1) * B) := by
    intro Λ hΛr
    have hΛ := hrows.1 Λ hΛr
    obtain ⟨b1, b2, b3, b4, b5, -⟩ := Base.main D u u' F0 Λ hs ⟨he, hz⟩ hΛ
    have b6 : finrank D.host.E (D.sp.X 0).V = D.R.k := (LinearMap.finrank_range_of_inj b2).symm.trans b1.2.2
    have a1 := cntCl_le_encard_mul (FrEqv.TEqv_equivalence D Λ (lf D F0) (T' := ((Tu D u' : ℕ) : D.host.E)))
      {F' | IsTerm Λ (gS D) (lf D F0) F' ∧ FrameOK D Λ F' ∧ IsGeneric Λ (gS D) (lf D F0) F' ∧
        ZEquiv (ZhatL (lf D F0) F') Z}
      {P : LatW D | P ≤ L0X D Λ (lf D F0) ∧ rkW D P = D.R.k - 1 ∧ detW D P ≤ G}
      (fun P => FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (ENNReal.ofReal B)
      (ENNReal.ofReal_pos.2 hB0).ne'
      (by
        rintro F' ⟨t1, t2, t3, t4⟩
        obtain ⟨o1, o2, o3⟩ := orth_lattice D u u' F0 Λ hs ⟨he, hz⟩ hΛ F' ⟨t1, t2⟩
        refine ⟨_, ⟨o1, o2, o3.trans (le_of_eq ?_)⟩, ⟨t1, t2⟩, t4, le_rfl⟩
        rw [G0, FrameDet.main D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz Λ hΛ F' ⟨t1, t2⟩ t3, hGd]
        simp only [Gz, absDl, lead_eq t4])
      (by
        rintro P ⟨p1, p2, p3⟩
        have := h1 C c1 D large₂ u u' C' Cl hCl hH F0 he hz Λ hΛ Z hZ 1 le_rfl hk P p1 p2 G' H hG'1
          (p3.trans (le_max_left _ _)) le_rfl
          ((max_le hGH hH1).trans (le_self_pow₀ hH1 three_ne_zero))
        simpa only [mul_one, one_mul] using this)
    refine a1.trans ((mul_le_mul_left (sub_count D _ b3 b6 b4.fg b5 (D.R.k - 1) G) _).trans (le_of_eq ?_))
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun de _ => ?_
    rw [mul_assoc, ← ENNReal.ofReal_mul' hB0.le]
    rfl
  unfold MeanLe
  refine (Finset.sum_le_sum fun Λ hΛ => mul_le_mul_right (row Λ hΛ) _).trans ?_
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  rcases lt_or_ge G 1 with hG1 | hG1
  · rw [Nat.floor_eq_zero.2 hG1]
    simp
  have hGG : G' = G := max_eq_left hG1
  have ha : 0 ≤ (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) := by
    have := Real.pi_pos
    positivity
  have hrd : 0 ≤ D.host.rdE := zero_le_one.trans (GlobalTheory.real_places_facts D).2.2.2.2.1
  have key := GlobalTheory.T.exponent_divisor_sum_le D.R.k D.R.f D.R.rS G (NT D u) H _
    ((2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f) C hk hs.1 hf
    hlog hG1 hN hGH z1 ha (by positivity) z3 c4
  refine (Finset.sum_le_sum fun de hde => mul_le_mul_left
    (hP hH F0 he hz what₂ hrows de (Finset.mem_Icc.1 hde).1 H
      (((Nat.le_floor_iff (zero_le_one.trans hG1)).1 (Finset.mem_Icc.1 hde).2).trans hGH) z1) _).trans ?_
  simp only [mul_assoc (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ))]
  rw [← Finset.mul_sum]
  refine mul_le_mul_right ?_ _
  rw [prod_nV D u u' Z hg]
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal key)
  rw [ENNReal.ofReal_sum_of_nonneg fun de _ => by positivity]
  refine Finset.sum_congr rfl fun de _ => ?_
  rw [← ENNReal.ofReal_mul (by positivity), hB, hGG]

end GlobalTheory.LoopC.GenericMean
end
