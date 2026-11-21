import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopHer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEOneLetterDens
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceDone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLocCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamJFOK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamAlg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHRepLin
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHCellTie
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSliceFamGood
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSliceFamJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHOpClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelTransport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtieLevTransportHerOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDGqRes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDJNice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta

section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

def LevTransportU : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)),
    ∃ Tw : D.LevTower P.k P.r Wp Wq, D.TowerNormalised Tw ∧
      Tw.base.z = z ∧ Tw.base.z' = z' ∧ Tw.base.π = π ∧ Tw.base.π' = π' ∧
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'))) (κ : ℝ),
      Di = Tw.bs i ∧ 0 < κ ∧ IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
      ∀ (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
      ∃ T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π',
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))

end Formalism.FourierDecayAlt.P.PTie
end
end

section
open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieUL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB Formalism.FourierDecayAlt.P.PTieL

theorem lev_indU {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (X : ActualOps P.k P.r T.base.z T.base.z' T.base.π T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π'))) (l0 : ℕ)
    (hD : P5.IsData P T.base.z T.base.z' T.base.π T.base.π' X μ L st l0) :
    ∀ (j : ℕ) (hj : j ≤ P.r),
    ∃ (Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
      (μj : Measure (Mt P.k (P.r - j)))
      (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
      (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (κ : ℝ),
      0 < κ ∧ P5.IsData (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj μj Lj stj l0 ∧
      KB.ZetaNorm (T.bs j) μj ∧
      ∀ c : Fin P.r → ℂ, (∀ l : Fin P.r, l.val < j → c l ≠ 0) →
      ∃ Tj : RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π' →ₗ[ℂ]
        RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π',
      (∀ Φ c'' g, (Tj Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c'' g =
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))
          (D.castM (by omega) (ιLev P.k j (P.r - j) g))) ∧
      (∀ Φ Ψ c'', P5.pairAt μj (Tj Φ) (Tj Ψ) c'' =
        (κ : ℂ) * P5.pairAt μ Φ Ψ (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))) ∧
      (∀ l : Fin (P.r - j), Rel Tj (L.p ⟨l.val + j, by omega⟩) (Lj.p l) ∧
        Rel Tj (L.c ⟨l.val + j, by omega⟩) (Lj.c l) ∧ Rel Tj (L.ci ⟨l.val + j, by omega⟩) (Lj.ci l)) ∧
      ∀ (n : ℕ) (hn : n + j ≤ P.r) (Y : ℂ),
        MRel Tj (P5.QQi L st ⟨n + j, by omega⟩ Y) (P5.QQi Lj stj ⟨n, by omega⟩ Y)
  | 0, _ => by
    obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - 0) Wp Wq (T.bs 0)
    have h1 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, μ = a • μ0 := by
      have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed P.k P.r
      have h1' := h1
      have h0 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ0 := hμ0.1
      rw [glev_last_eq] at h1' h0
      exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar P.k P.r _ μ0 μ hU h0 h1'.conc h1'.left h1'.finite_compact
    have ha0 : (a : ℝ) ≠ 0 := by
      intro h
      apply h1.ne_zero
      rw [ha, show a = 0 from by exact_mod_cast h, zero_smul]
    refine ⟨X, μ0, L, st, (a : ℝ)⁻¹, inv_pos.2 (lt_of_le_of_ne a.2 (Ne.symm ha0)),
      ⟨JCTx5.isPlace_lev P T ⟨0, by omega⟩ hP, hμ0.1, hD.2.2⟩, hμ0, fun c _ => ⟨LinearMap.id,
      fun Φ c'' g => ?_, fun Φ Ψ c'' => ?_, fun l => ⟨rel_id _, rel_id _, rel_id _⟩, fun n hn Y => mrel_id _⟩⟩
    · rw [glue_zero', castM_iota0]; rfl
    · rw [glue_zero', ha, pairAt_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha0, Complex.ofReal_one,
        one_mul]
      rfl
  | j + 1, hj => by
    obtain ⟨Xj, μj, Lj, stj, κ, hκ, hDj, hZj, hall⟩ := lev_indU P T hP X μ L st l0 hD j (by omega)
    have hj' : j + 1 ≤ P.r := hj
    have hPl := JCTx5.isPlace_lev P T ⟨j + 1, by omega⟩ hP
    obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
    obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs l0
    obtain ⟨μs, hμs⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - (j + 1)) Wp Wq (T.bs (j + 1))
    have hDs : P5.IsData (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π' Xs μs Ls sts l0 := ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
    refine ⟨Xs, μs, Ls, sts, κ, hκ, hDs, hμs, fun c hc => ?_⟩
    obtain ⟨Tj, hform, hpair, hsite, hqq⟩ := hall c (fun l hl => hc l (by omega))
    have hn : P.r - j = 1 + (P.r - (j + 1)) := by omega
    have hcj : c ⟨j, by omega⟩ ≠ 0 := hc ⟨j, by omega⟩ (by simp)
    obtain ⟨T', hf', hs', hq', hp'⟩ := step_cast (k := P.k) (n := P.r - j) (ρ := P.r - (j + 1)) hn
      (levTower_bs_z_eq_castV_liftVec T j hj') (levTower_bs_z'_eq_castV_liftVec T j hj') (T.bs (j + 1)).z_mem (T.bs (j + 1)).z'_mem (tower_π T j hj')
      (tower_π' T j hj') Xj Xs Lj stj Ls sts (M.sgn (JC.parLev P j) l0) μj μs hDj.2.2.1 hDs.2.2.1
      hDj.2.2.2.1 hDs.2.2.2.1 hZj.1 hμs.1 hZj.2 hμs.2 (c ⟨j, by omega⟩) hcj
    refine ⟨T' ∘ₗ Tj, fun Φ c'' g => ?_, fun Φ Ψ c'' => ?_, fun l => ?_, fun n hn' Y => ?_⟩
    · rw [LinearMap.comp_apply, hf', hform, glue_step j hj' c c'' hn,
        lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r hn.symm (by omega) (by omega)]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hp', hpair, glue_step j hj' c c'' hn]
    · have e : (⟨l.val + 1 + j, by omega⟩ : Fin P.r) = ⟨l.val + (j + 1), by omega⟩ :=
        Fin.ext (show l.val + 1 + j = l.val + (j + 1) by omega)
      obtain ⟨a1, a2, a3⟩ := hsite ⟨l.val + 1, by omega⟩
      obtain ⟨b1, b2, b3⟩ := hs' l
      rw [← e]
      exact ⟨rel_comp a1 b1, rel_comp a2 b2, rel_comp a3 b3⟩
    · have e : (⟨n + 1 + j, by omega⟩ : Fin (P.r + 1)) = ⟨n + (j + 1), by omega⟩ :=
        Fin.ext (show n + 1 + j = n + (j + 1) by omega)
      have a := hqq (n + 1) (by omega) Y
      have b := hq' n (by omega) Y
      rw [← e]
      exact mrel_comp a b

theorem levTransportU : Formalism.FourierDecayAlt.P.PTie.LevTransportU := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 Bs hD hz hz' hπ hπ' i
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have e1 : T.base.z = z := h1.trans hz
  have e2 : T.base.z' = z' := h2.trans hz'
  have e3 : T.base.π = π := h3.trans hπ
  have e4 : T.base.π' = π' := h4.trans hπ'
  subst e1 e2 e3 e4
  obtain ⟨Xi, μi, Li, sti, κ, hκ, hDi, -, hall⟩ := lev_indU P T hD.1 X μ L st l0 hD i.val (by omega)
  refine ⟨T, hN, rfl, rfl, rfl, rfl, T.bs i, Xi, μi, Li, sti, κ, rfl, hκ, hDi, fun c hc => ?_⟩
  obtain ⟨Ti, hform, hpair, hsite, hqq⟩ := hall c hc
  refine ⟨Ti, ⟨hform, ⟨κ, hκ, hpair⟩, fun n hn Y => hqq n hn Y,
    fun S _ _ w => ⟨fun l => ?_, fun n hn => ?_, fun hw => ?_⟩⟩, hpair⟩
  · obtain ⟨a1, a2, a3⟩ := hsite l
    exact arel_bT (σ := P5.site L ⟨l.val + i, by omega⟩) (σ' := P5.site Li l) a1 a2 a3 w
  · exact arel_RRw (fun Y => hqq n hn Y) w
  · obtain ⟨⟨hA1, hA2, hA3, hA4⟩, hw2, hw3⟩ := hw
    have hq : sti.q = st.q := hDi.2.2.2.2.1.trans hD.2.2.2.2.1.symm
    have hinv : sti.inv = st.inv := hDi.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm
    refine ⟨⟨hA1, hA2, fun l hl => ?_, hA4⟩, hw2, hw3⟩
    rw [hq, hinv]
    exact hA3 l hl

end Formalism.FourierDecayAlt.P.PTieUL

namespace Formalism.FourierDecayAlt.P

theorem level_transport_unitary : Formalism.FourierDecayAlt.P.PTie.LevTransportU := PTieUL.levTransportU

end Formalism.FourierDecayAlt.P
end
end

section
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Tr

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fs_tr (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ Ψ : RadSp k r z z' π π') :
    fs μ l Φ Ψ c t = (κ : ℂ)⁻¹ * ∫ c'' : Cf (r - l.succ) 0, wtI 0 c'' *
      pairAt μi (T Φ) (T Ψ) (glue 0 (shiftV l.succ (Function.update c l t)) c'') := by
  have hjl : (0 : Fin (r - l.succ + 1)).val + l.succ.val = l.succ.val := by simp
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  unfold fs
  rw [← (shEqJ_mp l.succ l.succ 0 hjl).integral_comp', ← integral_const_mul]
  congr 1; funext c''
  rw [wtI_shEqJ, glue_shEqJ l.succ l.succ 0 hjl (Function.update c l t) (Function.update c l t) (fun _ _ => rfl), hT]
  field_simp

theorem level_one_square_integrable_of_transport (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ : RadSp k r z z' π π') (c₀ : Fin (r - l.succ) → ℂ) (h : LevelSquareIntegrable μi 0 (T Φ) c₀) :
    LevelSquareIntegrable μ l.succ Φ (Function.update c l t) :=
  level_square_integrable_of_transport μ l.succ (Function.update c l t) μi T κ hκ hT Φ c₀ h

end Tr

end Formalism.FourierDecayAlt.P5.HerD
end
end

section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE.FamCC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem phiP_contDiffAt (f : ℂ × Mat k r → E) {U : Set (ℂ × Mat k r)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (p : ℂ × ((Fin j → Mat k r) × Mat k r)), (p.1, p.2.2) ∈ U →
      ContDiffAt ℝ ∞ (fun p : ℂ × ((Fin j → Mat k r) × Mat k r) => Phi (fun x => f (p.1, x)) j bs p.2) p := by
  intro j
  induction j with
  | zero =>
    intro bs p hp
    have hm : ContDiff ℝ ∞ (fun p : ℂ × ((Fin 0 → Mat k r) × Mat k r) => (p.1, p.2.2)) :=
      contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
    exact (hf.contDiffAt (hU.mem_nhds hp)).comp p hm.contDiffAt
  | succ j ih =>
    intro bs p hp
    have hsh : ContDiff ℝ ∞ (fun q : (ℂ × ((Fin (j + 1) → Mat k r) × Mat k r)) × Mat k r =>
        (q.1.1, ((fun i : Fin j => q.1.2.1 i.succ), q.2))) :=
      (contDiff_fst.comp contDiff_fst).prodMk
        ((contDiff_pi.2 fun (i : Fin j) =>
          (contDiff_apply ℝ (Mat k r) i.succ).comp (contDiff_fst.comp (contDiff_snd.comp contDiff_fst))).prodMk
          contDiff_snd)
    have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (q : ℂ × ((Fin (j + 1) → Mat k r) × Mat k r)) (g : Mat k r) =>
        Phi (fun x => f (q.1, x)) j (fun i => bs i.succ) ((fun i => q.2.1 i.succ), g)) (p, p.2.2) :=
      ContDiffAt.comp (g := fun q : ℂ × ((Fin j → Mat k r) × Mat k r) =>
        Phi (fun x => f (q.1, x)) j (fun i => bs i.succ) q.2) (p, p.2.2)
        (ih (fun i => bs i.succ) (p.1, ((fun i => p.2.1 i.succ), p.2.2)) hp) hsh.contDiffAt
    have h2 := ContDiffAt.fderiv h1 (contDiffAt_snd.comp p contDiffAt_snd) top_add_one_le
    have h3 : ContDiff ℝ ∞ (fun q : ℂ × ((Fin (j + 1) → Mat k r) × Mat k r) => vf (bs 0) (q.2.1 0) q.2.2) :=
      vf_contDiff (bs 0) ((contDiff_apply ℝ (Mat k r) 0).comp (contDiff_fst.comp contDiff_snd))
        (contDiff_snd.comp contDiff_snd)
    exact h2.clm_apply h3.contDiffAt

theorem local_boundP {G : ℂ → Mat k r → E} (f : ℂ × Mat k r → E) {U : Set (ℂ × Mat k r)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hGf : ∀ p ∈ U, p.2 ∈ GV k r → G p.1 p.2 = f p) (m : ℕ) {p₀ : ℂ × Mat k r}
    (hp₀ : p₀ ∈ U) :
    ∃ V ∈ 𝓝 p₀, ∃ c : ℝ, 0 ≤ c ∧ ∀ p ∈ V, p.2 ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool)
      (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G p.1) p.2‖ ≤ c := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p₀ hp₀
  have hsub : Metric.closedBall p₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hb : ∀ (j : ℕ) (bs : Fin j → Bool), ∃ c : ℝ, ∀ q ∈ Metric.closedBall p₀.1 (ε / 2) ×ˢ
      ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2)),
      ‖Phi (fun x => f (q.1, x)) j bs q.2‖ ≤ c := by
    intro j bs
    have hK : IsCompact (Metric.closedBall p₀.1 (ε / 2) ×ˢ
        ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2))) :=
      (isCompact_closedBall _ _).prod ((isCompact_univ_pi fun _ => box_compact).prod (isCompact_closedBall _ _))
    refine hK.exists_bound_of_continuousOn fun q hq => ?_
    have hqU : (q.1, q.2.2) ∈ U := by
      apply hsub
      rw [Metric.mem_closedBall, Prod.dist_eq]
      exact max_le (Metric.mem_closedBall.1 hq.1) (Metric.mem_closedBall.1 hq.2.2)
    exact (phiP_contDiffAt f hU hf j bs q hqU).continuousAt.continuousWithinAt
  choose c hcb using hb
  refine ⟨Metric.closedBall p₀ (ε / 2), Metric.closedBall_mem_nhds p₀ (by linarith),
    ∑ j : Fin (m + 1), ∑ bs : Fin j → Bool, |c j bs|, by positivity, ?_⟩
  intro p hp hpG j hj bs Xs hL hB
  have hpU : p ∈ U := hsub hp
  have hUt : IsOpen {x : Mat k r | (p.1, x) ∈ U} :=
    hU.preimage (continuous_const.prodMk continuous_id)
  have hft : ContDiffOn ℝ ∞ (fun x => f (p.1, x)) {x : Mat k r | (p.1, x) ∈ U} :=
    hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => hx)
  have hmem : p.2 ∈ {x : Mat k r | (p.1, x) ∈ U} := hpU
  rw [W_eq_phi hUt hft (fun x hx hxG => hGf (p.1, x) hx hxG) j bs Xs hL p.2 hmem hpG]
  have hpd : dist p p₀ ≤ ε / 2 := Metric.mem_closedBall.1 hp
  rw [Prod.dist_eq] at hpd
  have hq : (p.1, (Xs, p.2)) ∈ Metric.closedBall p₀.1 (ε / 2) ×ˢ
      ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2)) :=
    ⟨Metric.mem_closedBall.2 ((le_max_left _ _).trans hpd), fun i _ => hB i,
      Metric.mem_closedBall.2 ((le_max_right _ _).trans hpd)⟩
  calc ‖Phi (fun x => f (p.1, x)) j bs (Xs, p.2)‖ ≤ |c j bs| := (hcb j bs _ hq).trans (le_abs_self _)
    _ = |c (⟨j, by omega⟩ : Fin (m + 1)) bs| := rfl
    _ ≤ ∑ bs' : Fin (⟨j, by omega⟩ : Fin (m + 1)) → Bool, |c (⟨j, by omega⟩ : Fin (m + 1)) bs'| :=
        Finset.single_le_sum (f := fun bs' => |c (⟨j, by omega⟩ : Fin (m + 1)) bs'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ bs)
    _ ≤ ∑ j' : Fin (m + 1), ∑ bs' : Fin j' → Bool, |c j' bs'| :=
        Finset.single_le_sum (f := fun j' : Fin (m + 1) => ∑ bs' : Fin j' → Bool, |c j' bs'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

theorem ccle_unif {G : ℂ → Mat k r → E} {K : Set ℂ} (hK : IsCompact K) {C : Set (Mat k r)} (hC : IsCompact C)
    (hloc : ∀ t ∈ K, ∀ γ ∈ GV k r, ∃ (U : Set (ℂ × Mat k r)) (f : ℂ × Mat k r → E), IsOpen U ∧ (t, γ) ∈ U ∧
      ContDiffOn ℝ ∞ f U ∧ ∀ p ∈ U, p.2 ∈ GV k r → G p.1 p.2 = f p)
    (hck : ∀ t ∈ K, CkOn ⊤ (GV k r) (G t))
    (hsupp : ∀ t ∈ K, ∀ γ, G t γ ≠ 0 → γ ∈ C) (A : ℝ) (m : ℕ) :
    ∃ c : ℝ, ∀ t ∈ K, CCle A m (G t) c := by
  classical
  have hS : IsCompact (K ×ˢ (C ∩ GV k r)) := hK.prod (hC.inter_right B5.GV_closed)
  have hl : ∀ p ∈ K ×ˢ (C ∩ GV k r), ∃ V, V ∈ 𝓝 p ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ q ∈ V, q.2 ∈ GV k r → ∀ (j : ℕ), j ≤ m →
      ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G q.1) q.2‖ ≤ c := fun p hp => by
    obtain ⟨U, f, hU, hpU, hf, hGf⟩ := hloc p.1 hp.1 p.2 hp.2.2
    obtain ⟨V, hV, c, hc0, hc⟩ := local_boundP f hU hf hGf m (p₀ := (p.1, p.2)) hpU
    exact ⟨V, hV, c, hc0, hc⟩
  choose! V hV c hc0 hc using hl
  obtain ⟨s, hsS, hcov⟩ := hS.elim_nhds_subcover V hV
  have hsum0 : 0 ≤ ∑ x ∈ s, c x := Finset.sum_nonneg fun y hy => hc0 y (hsS y hy)
  have hcW : ∀ t ∈ K, ∀ g ∈ C ∩ GV k r, ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r),
      (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G t) g‖ ≤ ∑ x ∈ s, c x := by
    intro t ht g hg j hj bs Xs hL hB
    obtain ⟨x, hxs, hgx⟩ := Set.mem_iUnion₂.1 (hcov (show (t, g) ∈ K ×ˢ (C ∩ GV k r) from ⟨ht, hg⟩))
    exact (hc x (hsS x hxs) (t, g) hgx hg.2 j hj bs Xs hL hB).trans
      (Finset.single_le_sum (fun y hy => hc0 y (hsS y hy)) hxs)
  obtain ⟨cg, hcg⟩ := (hC.inter_right B5.GV_closed).exists_bound_of_continuousOn
    (f := fun g : Mat k r => gN g ^ A)
    fun g hg => ((B6.gN_continuous.continuousAt).rpow_const (Or.inl (B6.gN_pos hg.2).ne')).continuousWithinAt
  refine ⟨|cg| * ∑ x ∈ s, c x, fun t ht => ⟨B5.ckOn_mono le_top (hck t ht), ?_⟩⟩
  intro u v hu hv hlen g hg
  rw [dLR_eq]
  have hmemlr : ∀ y ∈ lr u v, unitLie k r y.2 := by
    intro y hy
    simp only [lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  by_cases hgC : g ∈ C
  · have hw : lr u v = List.ofFn fun i : Fin (lr u v).length => ((lr u v)[i].1, (lr u v)[i].2) := by
      simp
    have hlen' : (lr u v).length ≤ m := by simp [lr]; omega
    have hb := hcW t ht g ⟨hgC, hg⟩ _ hlen' (fun i => (lr u v)[i].1) (fun i => (lr u v)[i].2)
      (fun i => (hmemlr _ (List.getElem_mem _)).1) (fun i => mem_box (hmemlr _ (List.getElem_mem _)).2)
    rw [← hw] at hb
    have hg1 : gN g ^ A ≤ |cg| := by
      have := hcg g ⟨hgC, hg⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    exact mul_le_mul hg1 hb (norm_nonneg _) (abs_nonneg _)
  · have h0 := W_local_zero hC.isClosed.isOpen_compl
      (fun x hx _ => by by_contra h; exact hx (hsupp t ht x h)) (lr u v)
      (fun y hy => (hmemlr y hy).1) g hgC hg
    rw [h0, norm_zero, mul_zero]
    positivity

end Formalism.FourierDecayAlt.P.CutSE.FamCC

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_uniform_compact_convergence : FamCCUnif := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG K hK hK0 A m
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
  have hck : ∀ t ∈ K, B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro t ht γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t (hK0 t ht) γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  exact FamCC.ccle_unif hK hC (fun t ht γ hγ => hG1 t (hK0 t ht) γ hγ) hck
    (fun t ht γ h => (hCε t ht γ h).1) A m

end Formalism.FourierDecayAlt.P.CutSE
end
end

section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerD Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jSRadLoc_of (hU : FamCCUnif) : JSRadLoc := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl ε hε G hN hGc Φ hlc hΦ c hc js hjs t0 ht0
  have hr0 : 0 < P.r := by have := l.isLt; omega
  obtain rfl : l = ⟨0, hr0⟩ := Fin.ext hl
  obtain ⟨Tw, hNw, e1, e2, e3, e4, Di, Xi, μi, Li, sti, κ, hDiEq, hκ, hDi, hall⟩ :=
    Formalism.FourierDecayAlt.P.level_transport_unitary Wp Wq P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' ⟨1, by omega⟩
  subst e1 e2 e3 e4
  subst hDiEq
  have hj : 0 + 1 ≤ P.r := by omega
  have hP : IsPlace P Tw.base.z Tw.base.z' Tw.base.π Tw.base.π' := hD.1
  have hPj := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P Tw ⟨0, by omega⟩ hP
  have hPs := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P Tw ⟨0 + 1, by omega⟩ hP
  obtain ⟨κ0, hκ0⟩ := Formalism.FourierDecayAlt.P.jacquet_scaling P.k P.r Wp Wq D Tw.base hz hz' hπ hπ'

  set G0 : B.Mat P.k (P.r - 0) → (Wq →L[ℂ] Wp) := fun g => κ0 • G g with hG0
  have hG0ok : JFOKCpt (JC.parLev P 0) (Tw.bs 0).z (Tw.bs 0).z' G0 := by
    have hck : B.CkOn ⊤ (B.GV P.k (P.r - 0)) G0 := by
      intro g₀ hg₀
      obtain ⟨U, f', hU', hgU, hcf, hff⟩ := hN.1 g₀ hg₀
      exact ⟨U, fun g => κ0 • f' g, hU', hgU, hcf.const_smul κ0, fun g hg hgG => by
        simp only [hG0]; rw [hff g hg hgG]⟩
    have hz0 : ∀ g ∈ B.GV P.k (P.r - 0), g ∉ tsupport G → G0 g = 0 := fun g _ hg => by
      simp only [hG0]; rw [image_eq_zero_of_notMem_tsupport hg, smul_zero]
    refine ⟨⟨fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hck hGc hz0 A m, ε, hε, fun g hg hne => ?_⟩, ?_⟩
    · have hne' : G g ≠ 0 := fun h => hne (by simp only [hG0]; rw [h, smul_zero])
      have := hN.2.2 g hg hne'
      rwa [hz, hz'] at this
    · exact HasCompactSupport.intro hGc (fun g hg => by simp only [hG0]; rw [image_eq_zero_of_notMem_tsupport hg, smul_zero])
  have hΦ0 : IsRadJF (JC.parLev P 0) (Tw.bs 0).z (Tw.bs 0).z' (Tw.bs 0).π (Tw.bs 0).π' (Tw.bs 0) G0 Φ := by
    intro (x : (Fin P.r → ℂ) × Mx P.k P.r) hx
    have e : B.JF Tw.base G0 = κ0 • B.JF Tw.base G := by
      funext h
      exact Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul (Bs := Tw.base) κ0 G h
    have h2 : resG P.k P.r (Fin.last P.r) (B.JF D G) x.1 x.2 =
        resG P.k P.r (Fin.last P.r) (B.JF Tw.base G0) x.1 x.2 := by
      rw [hκ0 G, e]
    exact (hΦ x hx).trans h2
  have hC0 : CutSH.InC Tw 0 hj Φ :=
    CutSH.inC_seed Formalism.FourierDecayAlt.P.cell_compatibility_identity Formalism.FourierDecayAlt.P.slice_family_good
      CutSH.slice_family_orbital hP hNw hPj hPs G0 hG0ok Φ hΦ0
  have hW : ∀ js : List (Fin 6), CutSH.InC Tw 0 hj (wOp X ⟨0, hr0⟩ js Φ) := by
    intro js
    induction js with
    | nil => simpa [wOp] using hC0
    | cons j js ih =>
      have e : wOp X ⟨0, hr0⟩ (j :: js) Φ = X.op ⟨0, hr0⟩ j (wOp X ⟨0, hr0⟩ js Φ) := by
        simp [wOp, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [e]
      exact Formalism.FourierDecayAlt.P.operator_class_closed Wp Wq P Tw hP hNw 0 hj hPj hPs X j _ ih
  obtain ⟨Gj, hGj, hRep⟩ := hW js
  set K : Set ℂ := Metric.closedBall t0 (‖t0‖ / 2) with hKdef
  have hK : IsCompact K := isCompact_closedBall _ _
  have hn0 : 0 < ‖t0‖ := norm_pos_iff.2 ht0
  have hK0 : ∀ t ∈ K, t ≠ 0 := fun t ht h0 => by
    rw [h0, hKdef, Metric.mem_closedBall, dist_zero_left] at ht
    linarith
  obtain ⟨c4, hc4⟩ := hU Wp Wq P Tw 0 Gj hGj K hK hK0 (B.AB P.k (P.r - (0 + 1))) 4
  obtain ⟨CR, hCR, hRB⟩ := Formalism.FourierDecayAlt.P.radial_beta_pos Wp Wq P Tw ⟨1, by omega⟩ μi hDi.2.1
  obtain ⟨-, -, -, ⟨CB, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k (P.r - (0 + 1)) Wp Wq (Tw.bs (0 + 1))
    (B.AB _ _) le_rfl
  refine ⟨‖t0‖ / 2, by positivity, κ⁻¹ * CR⁻¹ * (|CB| * |c4| * |c4|), fun t ht => ?_⟩
  have htK : t ∈ K := Metric.ball_subset_closedBall ht
  have ht0' : t ≠ 0 := hK0 t htK
  obtain ⟨Tt, ⟨hform, -⟩, hpair⟩ := hall (Function.update c ⟨0, hr0⟩ t) (fun l' hl' => by
    have e : l' = ⟨0, hr0⟩ := Fin.ext (by simp at hl'; omega)
    subst e
    simpa using ht0')

  set Ψ := wOp X ⟨0, hr0⟩ js Φ with hΨdef
  have hTΨ : ∀ x ∈ DomR P.k (P.r - (0 + 1)) (Tw.bs (0 + 1)).z (Tw.bs (0 + 1)).z',
      (Tt Ψ : Fn P.k (P.r - (0 + 1)) (Wq →L[ℂ] Wp)) x.1 x.2 =
        resG P.k (P.r - (0 + 1)) (Fin.last _) (B.JF (Tw.bs (0 + 1)) (Gj t)) x.1 x.2 := by
    intro x hx
    rw [hform]
    have hg : glue ⟨1, by omega⟩ (Function.update c ⟨0, hr0⟩ t) (PTie.shiftCf ⟨1, by omega⟩ x.1) =
        CutSH.cc 0 hj t x.1 := by
      funext l'
      rcases Nat.eq_zero_or_pos l'.val with h | h
      · have e : l' = ⟨0, hr0⟩ := Fin.ext h
        subst e
        simp [glue, CutSH.cc, consC]
      · have hne : l' ≠ ⟨0, hr0⟩ := fun e => by rw [e] at h; simp at h
        have h1 : (1 : ℕ) ≤ l'.val := h
        simp [glue, CutSH.cc, consC, PTie.shiftCf, h1, Nat.pos_iff_ne_zero.mp h]
    rw [hg]
    exact hRep t ht0' x hx
  obtain ⟨⟨hInCC, εt, hεt, hεG⟩, -⟩ := CutSH.family_orbital_valid Wp Wq P Tw 0 Gj hGj t ht0'
  have hck : B.CkOn ⊤ (B.GV P.k (P.r - (0 + 1))) (Gj t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU', hmem, hf, hfe⟩ := hGj.1 t ht0' γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (0 + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU'.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  have hNice : JC.NiceCoef (Tw.bs (0 + 1)) εt (Gj t) := ⟨hck, hInCC, hεG⟩
  have hL2 : LevelSquareIntegrable μi 0 (Tt Ψ) 0 := by
    have h := Formalism.FourierDecayAlt.P5.HerC.level_zero_form_integrable_compact (S := Empty) (Tw.bs (0 + 1)) μi hDi.2.1 (fun _ => Gj t) (fun _ => Gj t)
      (fun _ => Tt Ψ) (fun _ => Tt Ψ) (fun _ => hInCC) (fun _ => hInCC) (fun _ => hTΨ) (fun _ => hTΨ) 0
    unfold LevelSquareIntegrable
    simpa [wtI] using h
  refine ⟨level_one_square_integrable_of_transport μ ⟨0, hr0⟩ c t μi Tt κ hκ hpair Ψ 0 hL2, ?_⟩
  rw [fs_tr μ ⟨0, hr0⟩ c t μi Tt κ hκ hpair Ψ Ψ]
  have hform0 : (∫ c'' : Cf (P.r - (0 + 1)) 0, wtI 0 c'' * pairAt μi (Tt Ψ) (Tt Ψ)
      (glue 0 (shiftV (Fin.succ ⟨0, hr0⟩) (Function.update c ⟨0, hr0⟩ t)) c'')) =
      form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 := by
    unfold form
    congr 1
    funext c''
    have eg : glue 0 (shiftV (Fin.succ ⟨0, hr0⟩) (Function.update c ⟨0, hr0⟩ t)) c'' = glue 0 0 c'' := by
      funext l'; simp [glue]
    rw [eg]
    simp [wtI]
  have hβ := hRB 0 (fun _ => Gj t) (fun _ => Gj t) (fun _ => Tt Ψ) (fun _ => Tt Ψ) εt hεt (fun _ => hNice)
    (fun _ => hNice) (fun _ => hTΨ) (fun _ => hTΨ)
  have hβ' : B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t) = (CR : ℂ) * form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 := by
    convert hβ using 1
    · simp
    · rfl
  have hb := (hB1 (Gj t) (Gj t) c4 c4 (hInCC _ 5) (hInCC _ 5) (hc4 t htK) (hc4 t htK)).2.2
  erw [hform0]
  have hf : form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 = (CR : ℂ)⁻¹ * B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t) := by
    rw [hβ']
    have : (CR : ℂ) ≠ 0 := by exact_mod_cast hCR.ne'
    field_simp
  rw [hf, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hκ.le,
    Real.norm_of_nonneg hCR.le, mul_assoc]
  gcongr
  calc ‖B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t)‖ ≤ CB * c4 * c4 := hb
    _ ≤ |CB| * |c4| * |c4| := by
      have := abs_mul_abs_self c4
      calc CB * c4 * c4 = CB * (c4 * c4) := by ring
        _ ≤ |CB * (c4 * c4)| := le_abs_self _
        _ = |CB| * |c4| * |c4| := by rw [abs_mul, abs_mul, mul_assoc]

theorem spectral_radial_locality : JSRadLoc := jSRadLoc_of family_uniform_compact_convergence

end Formalism.FourierDecayAlt.P.CutSE
end
end

section
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Col

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ}

def Jm : Matrix (Fin 2) (Fin 2) A := !![0, 1; -1, 0]

theorem tvl_conjT (L : R.LevelData A r) (hS : StarCoords L) (Y : ℂ) (hY : star Y = Y) (l : Fin r) :
    (L.Tvl Y l)ᴴ = (L.Tl Y l)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R.LevelData.Tl, R.LevelData.Tvl, Matrix.conjTranspose_apply, (hS l).1, (hS l).2.1,
      (hS l).2.2.1, (hS l).2.2.2.1, (hS l).2.2.2.2.1, (hS l).2.2.2.2.2, ← algebraMap_star_comm, hY]

theorem tJt (L : R.LevelData A r) (Y : ℂ) (l : Fin r) : (L.Tl (Y + 1) l)ᵀ * Jm * L.Tl Y l = Jm := by
  have e1 : L.p l * L.ci l = L.ci l * L.p l - L.ci l := by simpa using L.p_ci l l
  have e2 : algebraMap ℂ A Y * L.ci l = L.ci l * algebraMap ℂ A Y := Algebra.commutes Y (L.ci l)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R.LevelData.Tl, Jm, Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [add_mul, mul_add, e1, e2, one_mul]
    abel
  · exact L.ci_c l
  · exact L.c_ci l

theorem diag_mul_comm (f : A) (X : Matrix (Fin 2) (Fin 2) A) (h : ∀ i j, Commute f (X i j)) :
    Matrix.diagonal (fun _ => f) * X = X * Matrix.diagonal (fun _ => f) := by
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, (h i j).eq]

theorem tl_comm (L : R.LevelData A r) (f : A) (l : Fin r) (Y : ℂ) (hp : Commute f (L.p l)) (hc : Commute f (L.c l))
    (hci : Commute f (L.ci l)) : ∀ i j, Commute f ((L.Tl Y l) i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [R.LevelData.Tl]
  all_goals first
    | exact (Algebra.commute_algebraMap_right Y f).add_right hp
    | exact hc
    | exact hc.neg_right
    | exact hci
    | exact Commute.zero_right f

theorem tele (L : R.LevelData A r) (Y : ℂ) (f : A) (ls : List (Fin r))
    (hls : ∀ l ∈ ls, Commute f (L.p l) ∧ Commute f (L.c l) ∧ Commute f (L.ci l)) :
    (ls.map (fun l => (L.Tl (Y + 1) l)ᵀ)).prod * (Matrix.diagonal (fun _ => f) * Jm) *
      (ls.map (L.Tl Y)).reverse.prod = Matrix.diagonal (fun _ => f) * Jm := by
  induction ls with
  | nil => simp
  | cons l t ih =>
    have hl := hls l (by simp)
    have ht : ∀ m ∈ t, Commute f (L.p m) ∧ Commute f (L.c m) ∧ Commute f (L.ci m) :=
      fun m hm => hls m (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.prod_append, List.prod_nil,
      Matrix.mul_one]
    rw [show ∀ (X P Q T M : Matrix (Fin 2) (Fin 2) A), X * P * M * (Q * T) = X * (P * M * Q) * T from
      fun X P Q T M => by simp only [Matrix.mul_assoc], ih ht]
    have hcomm : ∀ i j, Commute f ((L.Tl (Y + 1) l)ᵀ i j) :=
      fun i j => tl_comm L f l (Y + 1) hl.1 hl.2.1 hl.2.2 j i
    calc (L.Tl (Y + 1) l)ᵀ * (Matrix.diagonal (fun _ => f) * Jm) * L.Tl Y l
        = Matrix.diagonal (fun _ => f) * ((L.Tl (Y + 1) l)ᵀ * Jm * L.Tl Y l) := by
          rw [← Matrix.mul_assoc, ← diag_mul_comm f _ hcomm]
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun _ => f) * Jm := by rw [tJt]

theorem site_zero_matrix_entry (L : R.LevelData A r) (l : Fin r) (s Y : ℂ) (f : A) (hci : Commute f (L.ci l))
    (hp : L.p l * f = f * L.p l + algebraMap ℂ A s * f * L.c l) :
    (((L.Tl (Y + 1) l)ᵀ * (Matrix.diagonal (fun _ => f) * Jm) * L.Tl Y l : Matrix (Fin 2) (Fin 2) A) 0 0) =
      algebraMap ℂ A s * f := by
  have e1 : L.p l * L.ci l = L.ci l * L.p l - L.ci l := by simpa using L.p_ci l l
  have k2 : f * L.ci l = L.ci l * f := hci.eq
  have k1 : algebraMap ℂ A Y * (f * L.ci l) = L.ci l * (f * algebraMap ℂ A Y) := by
    rw [Algebra.commutes, k2, mul_assoc]
  have k3 : L.p l * (f * L.ci l) = L.ci l * (f * L.p l) - L.ci l * f + algebraMap ℂ A s * f := by
    calc L.p l * (f * L.ci l) = (L.p l * f) * L.ci l := (mul_assoc _ _ _).symm
      _ = f * (L.p l * L.ci l) + algebraMap ℂ A s * f * (L.c l * L.ci l) := by
        rw [hp]
        simp only [add_mul, mul_assoc]
      _ = f * (L.ci l * L.p l - L.ci l) + algebraMap ℂ A s * f := by rw [e1, L.c_ci, mul_one]
      _ = L.ci l * (f * L.p l) - L.ci l * f + algebraMap ℂ A s * f := by
        rw [mul_sub, ← mul_assoc, k2, mul_assoc]
  simp [R.LevelData.Tl, Jm, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [add_mul, mul_add, mul_assoc, one_mul]
  rw [k1, k3, k2]
  abel

end Col

theorem radial_collapse : RDCollapse := by
  intro A _ _ _ _ r hr L st s Y f fi hS hW hY
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hY1 : star (Y + 1) = Y + 1 := by simp [hY]
  have hM : (L.Tvprod (Y + 1))ᴴ = ((List.finRange (k + 1)).map (fun l => (L.Tl (Y + 1) l)ᵀ)).prod := by
    rw [R.LevelData.Tvprod, Matrix.conjTranspose_list_prod, List.map_reverse, List.reverse_reverse,
      List.map_ofFn, List.ofFn_eq_map]
    congr 1
    apply List.map_congr_left
    intro l _
    exact tvl_conjT L hS (Y + 1) hY1 l
  have hN : L.Tprod Y = ((List.finRange (k + 1)).map (L.Tl Y)).reverse.prod := by
    rw [R.LevelData.Tprod, List.ofFn_eq_map]
  have key : star (L.Avr (Y + 1)) * f * L.Br Y - star (L.Bvr (Y + 1)) * f * L.Ar Y =
      ((L.Tvprod (Y + 1))ᴴ * (Matrix.diagonal (fun _ => f) * Jm) * L.Tprod Y :
        Matrix (Fin 2) (Fin 2) A) 0 0 := by
    simp [R.LevelData.Avr, R.LevelData.Bvr, R.LevelData.Ar, R.LevelData.Br, Matrix.mul_apply,
      Fin.sum_univ_two, Jm, Matrix.conjTranspose_apply]
    noncomm_ring
  have hls : ∀ l ∈ (List.finRange k).map Fin.succ,
      Commute f (L.p l) ∧ Commute f (L.c l) ∧ Commute f (L.ci l) := by
    intro l hl
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
    have hne : i.succ ≠ ⟨0, hr⟩ := Fin.succ_ne_zero i
    have h8 := hW.2.2.2.2.2.2.2.1 i.succ hne
    exact ⟨h8 _ (by simp [coordOps]), h8 _ (by simp [coordOps]), h8 _ (by simp [coordOps])⟩
  rw [key, hM, hN, List.finRange_succ, List.map_cons, List.map_cons, List.prod_cons, List.reverse_cons,
    List.prod_append, List.prod_singleton,
    show ∀ (X P Q T M : Matrix (Fin 2) (Fin 2) A), X * P * M * (Q * T) = X * (P * M * Q) * T from
      fun X P Q T M => by simp only [Matrix.mul_assoc], tele L Y f _ hls]
  exact site_zero_matrix_entry L 0 s Y f hW.2.2.1 hW.2.2.2.2.2.1

private theorem star_eq_self_of_right_inv_of_star_eq_self {A : Type} [Ring A] [StarRing A] {b bi : A} (hb : star b = b)
    (h1 : b * bi = 1) : star bi = bi := by
  have hsb : star bi * b = 1 := by
    calc star bi * b = star bi * star b := by rw [hb]
      _ = star (b * bi) := (star_mul b bi).symm
      _ = 1 := by rw [h1, star_one]
  calc star bi = star bi * (b * bi) := by rw [h1, mul_one]
    _ = bi := by rw [← mul_assoc, hsb, one_mul]

theorem radial_gauge_identity : RadialGaugeAdjointRelation := by
  intro A _ _ _ _ r L st Y hSL hS hLS hY hYi hY1i
  obtain ⟨hxx, hxx'⟩ := hLS.x_xi Y hYi
  obtain ⟨hxx1, hxx1'⟩ := hLS.x_xi (Y + 1) hY1i
  have h11 := congrFun (congrFun (hLS.start.det Y).1 1) 1
  simp [YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, hLS.tau] at h11
  have hrel : st.QQ (Y + 1) 0 1 * (L.GG * st.x Y) = L.GG * st.x (Y + 1) * st.QQ Y 0 1 := by
    rw [← sub_eq_zero]
    rw [← h11]
    noncomm_ring
  have hzb : star L.ζb = L.ζ := by rw [← hSL.1, star_star]
  have hGGs : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, hzb, hSL.1, ← algebraMap_star_comm, hSL.2.2]
  have hGGis : star L.GGi = L.GGi := star_eq_self_of_right_inv_of_star_eq_self hGGs L.GG_GGi
  have hxis : star (st.xi Y) = st.xi Y := star_eq_self_of_right_inv_of_star_eq_self (hLS.x_star Y hY) hxx
  have hQs : star (st.QQ Y 1 0) = st.QQ Y 0 1 := by
    have := congrFun (congrFun (hLS.start.herm Y hY) 0) 1
    simpa [Matrix.conjTranspose_apply] using this
  have hxG : Commute (st.x Y) L.GGi := hLS.x_fn Y _ (by simp [Fr.zfns])
  have hQ01 : st.QQ Y 0 1 = st.xi (Y + 1) * L.GGi * st.QQ (Y + 1) 0 1 * (L.GG * st.x Y) := by
    rw [mul_assoc (st.xi (Y + 1) * L.GGi), hrel,
      show st.xi (Y + 1) * L.GGi * (L.GG * st.x (Y + 1) * st.QQ Y 0 1) =
        st.xi (Y + 1) * (L.GGi * L.GG) * st.x (Y + 1) * st.QQ Y 0 1 by simp only [mul_assoc],
      L.GGi_GG, mul_one, hxx1', one_mul]
  have h1 : L.GG * st.x Y * (L.GGi * st.xi Y) = 1 := by
    rw [mul_assoc, ← mul_assoc (st.x Y), hxG.eq, mul_assoc, ← mul_assoc L.GG, L.GG_GGi, one_mul, hxx]
  rw [star_mul, star_mul, hQs, hGGis, hxis, hQ01, mul_assoc (st.xi (Y + 1) * L.GGi * st.QQ (Y + 1) 0 1), h1,
    mul_one]

section Rearr

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem comm_inv' {a b bi : A} (h : Commute a b) (h1 : b * bi = 1) (h2 : bi * b = 1) : Commute a bi := by
  show a * bi = bi * a
  calc a * bi = (bi * b) * a * bi := by rw [h2, one_mul]
    _ = bi * (b * a) * bi := by rw [mul_assoc bi b a]
    _ = bi * (a * b) * bi := by rw [h.eq]
    _ = bi * a * (b * bi) := by simp only [mul_assoc]
    _ = bi * a := by rw [h1, mul_one]

theorem star_inv' {b bi : A} (hb : star b = b) (h1 : b * bi = 1) (h2 : bi * b = 1) : star bi = bi := by
  have hsb : star bi * b = 1 := by
    calc star bi * b = star bi * star b := by rw [hb]
      _ = star (b * bi) := (star_mul b bi).symm
      _ = 1 := by rw [h1, star_one]
  calc star bi = star bi * (b * bi) := by rw [h1, mul_one]
    _ = bi := by rw [← mul_assoc, hsb, one_mul]

theorem canc {a b : A} (h : a * b = 1) (z : A) : a * (b * z) = z := by rw [← mul_assoc, h, one_mul]

theorem star_list_prod_comm (l : List A) (h : ∀ a ∈ l, ∀ b ∈ l, Commute (star a) (star b)) :
    star l.prod = (l.map star).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, star_mul, List.map_cons, List.prod_cons,
      ih (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))]
    refine (Commute.list_prod_right _ _ ?_).eq.symm
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact h a (by simp) x (List.mem_cons_of_mem _ hx)

theorem star_ofFn_prod {r : ℕ} (g h : Fin r → A) (hs : ∀ i, star (g i) = h i) (hc : ∀ i j, Commute (h i) (h j)) :
    star (List.ofFn g).prod = (List.ofFn h).prod := by
  rw [star_list_prod_comm _ ?_, List.map_ofFn, show star ∘ g = h from funext hs]
  intro a ha b hb
  simp only [List.mem_ofFn] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rw [hs, hs]
  exact hc i j

end Rearr

private theorem commute_list_ofFn_prod_of_commute {A : Type} [Ring A] {r : ℕ} (a : A) (g : Fin r → A)
    (h : ∀ i, Commute a (g i)) : Commute a (List.ofFn g).prod := by
  refine Commute.list_prod_right _ _ ?_
  intro b hb
  simp only [List.mem_ofFn] at hb
  obtain ⟨i, rfl⟩ := hb
  exact h i

private theorem commute_list_ofFn_prod_ofFn_prod {A : Type} [Ring A] {r : ℕ} (g h : Fin r → A)
    (hc : ∀ i j, Commute (g i) (h j)) : Commute (List.ofFn g).prod (List.ofFn h).prod :=
  commute_list_ofFn_prod_of_commute _ _ (fun j => (commute_list_ofFn_prod_of_commute _ _ (fun i => (hc i j).symm)).symm)

private theorem list_ofFn_prod_mul_ofFn_prod_eq_one {A : Type} [Ring A] {r : ℕ} (g h : Fin r → A)
    (hgh : ∀ i, g i * h i = 1) (hc : ∀ i j, Commute (g i) (h j)) :
    (List.ofFn g).prod * (List.ofFn h).prod = 1 := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hP : Commute (List.ofFn fun i : Fin n => g i.succ).prod (h 0) :=
      (commute_list_ofFn_prod_of_commute (h 0) _ (fun i => (hc i.succ 0).symm)).symm
    rw [mul_assoc, ← mul_assoc _ (h 0), hP.eq, mul_assoc, ← mul_assoc (g 0), hgh 0, one_mul,
      ih (fun i => g i.succ) (fun i => h i.succ) (fun i => hgh _) (fun i j => hc _ _)]

private theorem commute_of_commute_mul_of_left_inv {A : Type} [Ring A] {G Gi x y : A} (h1 : Gi * G = 1)
    (hGx : Commute (G * x) y) (hG : Commute G y) : Commute x y := by
  show x * y = y * x
  calc x * y = Gi * (G * x) * y := by rw [← mul_assoc Gi, h1, one_mul]
    _ = Gi * ((G * x) * y) := mul_assoc _ _ _
    _ = Gi * (y * (G * x)) := by rw [hGx.eq]
    _ = Gi * (y * G * x) := by rw [← mul_assoc y]
    _ = Gi * (G * y * x) := by rw [← hG.eq]
    _ = y * x := by rw [mul_assoc G, ← mul_assoc Gi, h1, one_mul]

theorem radial_rearrangement : RDRearr := by
  intro A _ _ _ _ r hr L st s Y f fi hS hSL hLS hSC hW hY hYi hY1i hGa
  have hfc : ∀ a ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}, ∀ b ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪
      Set.range L.cbi ∪ {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}, Commute a b := L.fns_comm
  have hY1 : star (Y + 1) = Y + 1 := by simp [hY]
  obtain ⟨hx0, hx0'⟩ := hLS.x_xi Y hYi
  obtain ⟨hx1, hx1'⟩ := hLS.x_xi (Y + 1) hY1i
  have hWz := hW.2.2.2.2.2.2.2.2.1
  have hWQ := hW.2.2.2.2.2.2.2.2.2
  have hfG : Commute f L.GG := hWz _ (by simp [Fr.zfns])
  have hfGi : Commute f L.GGi := hWz _ (by simp [Fr.zfns])
  have hfl : ∀ l, Commute f (L.c l) ∧ Commute f (L.ci l) ∧ Commute f (L.cb l) ∧ Commute f (L.cbi l) := by
    intro l
    by_cases hl : l = ⟨0, hr⟩
    · subst hl
      exact ⟨hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
    · have h8 := hW.2.2.2.2.2.2.2.1 l hl
      exact ⟨h8 _ (by simp [coordOps]), h8 _ (by simp [coordOps]), h8 _ (by simp [coordOps]),
        h8 _ (by simp [coordOps])⟩
  have hfD : Commute f L.Dr := commute_list_ofFn_prod_of_commute _ _ (fun i => (hfl i).1)
  have hfDi : Commute f L.Dri := commute_list_ofFn_prod_of_commute _ _ (fun i => (hfl i).2.1)
  have hxg : ∀ Z l y, y ∈ coordOps L l → Commute L.GG y → Commute (st.x Z) y :=
    fun Z l y hy hG => commute_of_commute_mul_of_left_inv L.GGi_GG (by rw [← hLS.tau]; exact hSC Z 1 1 l y hy) hG
  have hxDb : ∀ Z, Commute (st.x Z) L.Drb := fun Z =>
    commute_list_ofFn_prod_of_commute _ _ (fun i => hxg Z i _ (by simp [coordOps]) (hfc _ (by simp) _ (by simp)))
  have hxG : ∀ Z, Commute (st.x Z) L.GG := fun Z => hLS.x_fn Z _ (by simp [Fr.zfns])
  have hxGi : ∀ Z, Commute (st.x Z) L.GGi := fun Z => hLS.x_fn Z _ (by simp [Fr.zfns])
  have hxiDb0 : Commute (st.xi Y) L.Drb := (comm_inv' (hxDb Y).symm hx0 hx0').symm
  have hxiDb1 : Commute (st.xi (Y + 1)) L.Drb := (comm_inv' (hxDb (Y + 1)).symm hx1 hx1').symm
  have hxiG0 : Commute (st.xi Y) L.GG := (comm_inv' (hxG Y).symm hx0 hx0').symm
  have hxiG1 : Commute (st.xi (Y + 1)) L.GG := (comm_inv' (hxG (Y + 1)).symm hx1 hx1').symm
  have hxiGi0 : Commute (st.xi Y) L.GGi := (comm_inv' (hxGi Y).symm hx0 hx0').symm
  have hxiGi1 : Commute (st.xi (Y + 1)) L.GGi := (comm_inv' (hxGi (Y + 1)).symm hx1 hx1').symm
  have hfx1 : Commute f (st.x (Y + 1)) :=
    (commute_of_commute_mul_of_left_inv L.GGi_GG (by rw [← hLS.tau]; exact (hWQ (Y + 1) 1 1).symm) hfG.symm).symm
  have hfxi1 : Commute f (st.xi (Y + 1)) := comm_inv' hfx1 hx1 hx1'
  have hGiDb : Commute L.GGi L.Drb := commute_list_ofFn_prod_of_commute _ _ (fun i => hfc _ (by simp) _ (by simp))
  have hDbDi : Commute L.Drb L.Dri := commute_list_ofFn_prod_ofFn_prod _ _ (fun i j => hfc _ (by simp) _ (by simp))
  have hDDi : L.Dr * L.Dri = 1 := list_ofFn_prod_mul_ofFn_prod_eq_one _ _ L.c_ci (fun i j => hfc _ (by simp) _ (by simp))
  have hDiD : L.Dri * L.Dr = 1 := list_ofFn_prod_mul_ofFn_prod_eq_one _ _ L.ci_c (fun i j => hfc _ (by simp) _ (by simp))
  have hDbDbi : L.Drb * L.Drbi = 1 :=
    list_ofFn_prod_mul_ofFn_prod_eq_one _ _ L.cb_cbi (fun i j => hfc _ (by simp) _ (by simp))
  have hDbiDb : L.Drbi * L.Drb = 1 :=
    list_ofFn_prod_mul_ofFn_prod_eq_one _ _ L.cbi_cb (fun i j => hfc _ (by simp) _ (by simp))
  have hsD : star L.Dr = L.Drb :=
    star_ofFn_prod _ _ (fun i => (hS i).2.2.1) (fun i j => hfc _ (by simp) _ (by simp))
  have hsDb : star L.Drb = L.Dr :=
    star_ofFn_prod _ _ (fun i => (hS i).2.2.2.1) (fun i j => hfc _ (by simp) _ (by simp))
  have hsDi : star L.Dri = L.Drbi :=
    star_ofFn_prod _ _ (fun i => (hS i).2.2.2.2.1) (fun i j => hfc _ (by simp) _ (by simp))
  have hsDbi : star L.Drbi = L.Dri :=
    star_ofFn_prod _ _ (fun i => (hS i).2.2.2.2.2) (fun i j => hfc _ (by simp) _ (by simp))
  have hzb : star L.ζb = L.ζ := by rw [← hSL.1, star_star]
  have hGs : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, hzb, hSL.1, ← algebraMap_star_comm, hSL.2.2]
  have hGis : star L.GGi = L.GGi := star_inv' hGs L.GG_GGi L.GGi_GG
  have hx1s : star (st.x (Y + 1)) = st.x (Y + 1) := hLS.x_star (Y + 1) hY1
  have hxi1s : star (st.xi (Y + 1)) = st.xi (Y + 1) := star_inv' hx1s hx1 hx1'
  have hQ1s : star (st.QQ (Y + 1) 0 1) = st.QQ (Y + 1) 1 0 := by
    have := congrFun (congrFun (hLS.start.herm (Y + 1) hY1) 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have B1 : L.Dr * (f * (L.Dri * (L.Drbi * (L.GGi * (st.xi Y * (L.Drb * st.QQ Y 1 0)))))) =
      f * (L.GGi * (st.xi Y * st.QQ Y 1 0)) := by
    rw [hfD.symm.left_comm, canc hDDi, hxiDb0.left_comm, hGiDb.left_comm, canc hDbiDb]
  have B2 : L.Dr * (f * (L.Dri * (L.Drbi * (L.GGi * (st.xi Y * (L.Drb * (L.GG * st.x Y))))))) = f := by
    rw [hfD.symm.left_comm, canc hDDi, hxiDb0.left_comm, hGiDb.left_comm, canc hDbiDb,
      hxiG0.left_comm, canc L.GGi_GG, hx0', mul_one]
  have B3 : L.Drb * (st.xi (Y + 1) * (L.GGi * (L.Dri * (L.Drbi * (f * L.Dr))))) =
      st.xi (Y + 1) * (L.GGi * f) := by
    rw [hxiDb1.symm.left_comm, hGiDb.symm.left_comm, hDbDi.left_comm, canc hDbDbi, hfDi.symm.left_comm,
      hDiD, mul_one]
  have B4 : st.x (Y + 1) * (L.GG * (L.Drb * (st.xi (Y + 1) * (L.GGi * (L.Dri * (L.Drbi * (f * L.Dr))))))) =
      f := by
    rw [B3, hxiG1.symm.left_comm, canc L.GG_GGi, canc hx1]
  have hfQ : Commute f (star (st.QQ (Y + 1) 0 1)) := by
    rw [hQ1s]
    exact hWQ (Y + 1) 1 0
  have hG' : st.xi Y * L.GGi * st.QQ Y 1 0 = star (st.QQ (Y + 1) 0 1) * (L.GGi * st.xi (Y + 1)) := by
    have := congrArg star hGa
    rwa [star_star, star_mul, star_mul, hGis, hxi1s] at this
  have E3 : f * (L.GGi * (st.xi Y * st.QQ Y 1 0)) =
      star (st.QQ (Y + 1) 0 1) * (st.xi (Y + 1) * (L.GGi * f)) := by
    calc f * (L.GGi * (st.xi Y * st.QQ Y 1 0)) = f * (st.xi Y * L.GGi * st.QQ Y 1 0) := by
          rw [← mul_assoc L.GGi, hxiGi0.symm.eq]
      _ = f * (star (st.QQ (Y + 1) 0 1) * (L.GGi * st.xi (Y + 1))) := by rw [hG']
      _ = star (st.QQ (Y + 1) 0 1) * (f * (L.GGi * st.xi (Y + 1))) := by
          rw [← mul_assoc, hfQ.eq, mul_assoc]
      _ = star (st.QQ (Y + 1) 0 1) * (st.xi (Y + 1) * (L.GGi * f)) := by
          rw [hfGi.left_comm, hfxi1.eq, hxiGi1.symm.left_comm]
  have E1 : star (thR L st Y 0) * f * thR L st Y 1 =
      star (L.Avr (Y + 1)) * (L.Dr * (f * (L.Dri * (L.Drbi * (L.GGi * (st.xi Y * (L.Drb *
        (L.GG * st.x Y)))))))) * L.Br Y +
      star (L.Avr (Y + 1)) * (L.Dr * (f * (L.Dri * (L.Drbi * (L.GGi * (st.xi Y * (L.Drb *
        st.QQ Y 1 0))))))) * L.Ar Y := by
    rw [show thR L st Y 0 = L.Drb * L.Avr (Y + 1) from rfl,
      show thR L st Y 1 = L.Dri * L.Drbi * L.GGi * st.xi Y *
        (L.Drb * (st.QQ Y 1 0 * L.Ar Y + st.QQ Y 1 1 * L.Br Y)) from rfl, hLS.tau, star_mul, hsDb]
    simp only [mul_add, add_mul, mul_assoc]
    all_goals abel
  have E2 : star (thR L st Y 2) * f * thR L st Y 3 =
      star (L.Bvr (Y + 1)) * (st.x (Y + 1) * (L.GG * (L.Drb * (st.xi (Y + 1) * (L.GGi * (L.Dri *
        (L.Drbi * (f * L.Dr)))))))) * L.Ar Y +
      star (L.Avr (Y + 1)) * (star (st.QQ (Y + 1) 0 1) * (L.Drb * (st.xi (Y + 1) * (L.GGi * (L.Dri *
        (L.Drbi * (f * L.Dr))))))) * L.Ar Y := by
    rw [show thR L st Y 2 = L.Dri * L.Drbi * L.GGi * st.xi (Y + 1) *
        (L.Dr * (st.QQ (Y + 1) 0 1 * L.Avr (Y + 1) + st.QQ (Y + 1) 1 1 * L.Bvr (Y + 1))) from rfl,
      show thR L st Y 3 = L.Dr * L.Ar Y from rfl, hLS.tau]
    simp only [star_mul, star_add, hsD, hsDi, hsDbi, hGis, hxi1s, hx1s, hGs, mul_add, add_mul, mul_assoc]
    all_goals abel
  rw [E1, E2, B2, B1, B4, B3, E3]
  abel

end Formalism.FourierDecayAlt.P.CutSE
end
end

section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_start_coordinates : RDStartCoord := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have ht : ∀ Y (a b : Fin 2) l (i : Fin 6), Commute (X.t Y a b) (X.op l i) :=
    fun Y a b l i => Formalism.FourierDecayAlt.P.NFx1.TC.t_op_comm X Y a b l i
  intro Y a b l x hx
  have hm : Commute (X.QQ Y a b) x := by
    rw [Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 0) (ht (star Y) b a l 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 3) (ht (star Y) b a l 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 1) (ht (star Y) b a l 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 2) (ht (star Y) b a l 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 4) (ht (star Y) b a l 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 5) (ht (star Y) b a l 2)
  rw [hQ Y, Matrix.smul_apply]
  exact hm.smul_left _

end Formalism.FourierDecayAlt.P.CutSE
end
end

section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
open scoped ComplexConjugate

section PairSub

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem rdw_sub_fst (a b : Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem rdw_sub_snd (a b : Pr V) : (a - b).2.unop = a.2.unop - b.2.unop := rfl

end PairSub

theorem radial_wave_radial : RDWaveRad := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD Wv Wv' hW hW'
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hL
  obtain ⟨hWave, hWc, hWci, hWp⟩ := waveSiteAll Wp Wq P z z' π π' X L hL' ⟨0, hr⟩ s Wv Wv' hW hW'
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ (l : Fin P.r) i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun l i Φ => X.op_apply l i Φ
  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → Commute W (X.op ⟨0, hr⟩ i) := by
    intro W u hWu i hi
    show W * X.op ⟨0, hr⟩ i = X.op ⟨0, hr⟩ i * W
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hoth : ∀ (t : ℂ) (W : Module.End ℂ (RadSp P.k P.r z z' π π')),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        fsv t (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ l : Fin P.r, l ≠ ⟨0, hr⟩ → ∀ i : Fin 6, Commute W (X.op l i) :=
    fun t W hWt l hl i => mulOp_comm_op X W t ⟨0, hr⟩ hWt hl i
  refine ⟨hWave, hWc, hWci, ?_, ?_, hWp, ?_, ?_, ?_, ?_⟩
  · rw [hcb]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hcomm Wv _ hW1 4 (by decide)) (hcomm Wv' _ hW2 1 (by decide))
  · rw [hcbi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hcomm Wv _ hW1 5 (by decide)) (hcomm Wv' _ hW2 2 (by decide))
  · rw [hpb, hcb]
    refine pr_ext ?_ ?_
    · simp only [mkPair_fst', pr_mul_fst, rdw_sub_fst, pr_alg_fst]
      apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
      obtain ⟨hd, h0⟩ := radSp_regular Φ g c
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
        Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, hop, crd, hW1, opL]
      have e := pbOp_fsv_smul (-s) ⟨0, hr⟩ _ c hd h0
      simp only [neg_neg] at e
      rw [e]
      simp only [cbOp, map_neg]
      module
    · simp only [mkPair_snd', pr_mul_snd, rdw_sub_snd, pr_alg_snd]
      apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
      obtain ⟨hd, h0⟩ := radSp_regular Φ g c
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
        Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, hop,
        crd, hW2, opL]
      rw [pOp_fsv_smul (-s) ⟨0, hr⟩ _ c hd h0]
      simp only [cOp, Complex.conj_conj]
      module
  · intro l hl x hx
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 0) (hoth (-s) Wv' hW2 l hl 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 3) (hoth (-s) Wv' hW2 l hl 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 1) (hoth (-s) Wv' hW2 l hl 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 2) (hoth (-s) Wv' hW2 l hl 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 4) (hoth (-s) Wv' hW2 l hl 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 5) (hoth (-s) Wv' hW2 l hl 2)
  · have hf : ∀ j : Fin 6, Commute Wv (X.fn j) ∧ Commute Wv' (X.fn j) := fun j =>
      ⟨TwistedTransfer.mulOp_comm_fn X Wv _ hW j, TwistedTransfer.mulOp_comm_fn X Wv' _ hW' j⟩
    intro x hx
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 0).1 (hf 2).2
    · rw [hzi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 1).1 (hf 3).2
    · rw [hzb]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 2).1 (hf 0).2
    · rw [hzbi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 3).1 (hf 1).2
    · rw [hG]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 4).1 (hf 4).2
    · rw [hGi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 5).1 (hf 5).2
  · intro Y a b
    rw [hQ Y, Matrix.smul_apply, Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    exact (Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (comm_xt_of_fsv_smul_endomorphism X Wv s ⟨0, hr⟩ hW1 Y a b)
      (comm_xt_of_fsv_smul_endomorphism X Wv' (-s) ⟨0, hr⟩ hW2 (star Y) b a)).smul_right _

end Formalism.FourierDecayAlt.P.CutSE
end
end

section
open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section WaveFF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem rdb_one_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩

theorem rdb_n_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {n : Mx k r} (hn : n ∈ Nlev k r 0) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩

theorem rdb_h_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {h : Mx k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

theorem rdb_fsv_dmin_contDiff (z z' : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (h1 : 1 < r + 2) :
    ContDiff ℝ ∞ (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) := by
  have e : (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) = fun g =>
      Complex.exp (Formalism.FourierDecayAlt.P.PBFV.phaseL s (Formalism.FourierDecayAlt.P.JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g) :=
    funext fun g => Formalism.FourierDecayAlt.P.PBFV.fsv_dmin_one s z z' g h1
  rw [e]
  exact Complex.contDiff_exp.comp (ContinuousLinearMap.contDiff _)

theorem rdb_wvG_mem_FFl {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (s : ℂ)
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' 0 Dm) : wvG z z' s J ∈ FFl k r z z' π π' 0 Dm := by
  have h1 : 1 < r + 2 := by omega
  have inv : ∀ {a b : Mx k r}, a ∈ Sset k r z → b ∈ Sset k r z' → ∀ g : Mx k r,
      Dmin k r z z' (a * g * b) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ :=
    fun ha hb g => dInv k r z z' hz hz' _ ha _ hb g _
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    refine ⟨U, fun g => fsv s (Dmin k r z z' g ⟨1, h1⟩) • F g, hU, hgU,
      (rdb_fsv_dmin_contDiff z z' s h1).contDiffOn.smul hF, fun g hgU hgG => ?_⟩
    show fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g = _
    rw [hFJ g hgU hgG]
  · intro g hg n hn
    have e : Dmin k r z z' (n * g) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_n_mem_Sset z hn) (rdb_one_mem_Sset z') g
      simpa using this
    show fsv s (Dmin k r z z' (n * g) ⟨1, h1⟩) • J (n * g) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hL g hg n hn, smul_comm]
  · intro g hg n hn
    have e : Dmin k r z z' (g * n) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_one_mem_Sset z) (rdb_n_mem_Sset z' hn) g
      simpa using this
    show fsv s (Dmin k r z z' (g * n) ⟨1, h1⟩) • J (g * n) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hR g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    show fsv s (Dmin k r z z' (h * g * h') ⟨1, h1⟩) • J (h * g * h') =
      (π h).comp ((fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g).comp (π' h'))
    rw [inv (rdb_h_mem_Sset z hh) (rdb_h_mem_Sset z' hh') g, hU g hg h hh h' hh',
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end WaveFF

theorem radial_wave_function_field : RDWaveFF := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD J hJ
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  have h1 : 1 < P.r + 2 := by omega
  refine ⟨rdb_wvG_mem_FFl hz hz' s hJ, fun x hx => ?_⟩
  simp only [resG, wvG]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord hz hz' hr x.1 hx.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
end
end

section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_wave_orbital : RDWaveJ := by
  intro k r Wp Wq _ _ _ _ _ _ D s H _ g _
  unfold wvG
  exact PBFV.JF_mul_inv D _ (fun p hp x => by rw [BigCellZetaMinors.dmin_sgs D hp]) H g

end Formalism.FourierDecayAlt.P.CutSE
end
end

section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_operator_locality : RDOpLocal := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ f₁ f₂ h g hg
  have hO := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus (k := k) (r := r) D.z D.z'
  have h' : ∀ x ∈ B.GV k r, x ∈ Q.OmPlus k r D.z D.z' → f₁ x = f₂ x := fun x hx hxO => h x ⟨hx, hxO⟩
  exact ⟨Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opApply_congr_GV Θ hO h' g hg.1 hg.2,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hO h' g hg.1 hg.2⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_identity_of_spectral_data : RDRadIdOfSpec :=
  rDRadIdOfSpec_of_grpId_theta
    (rDGrpIdOfSpec_of_radIdAlg (rDRadIdAlg_of_collapse_gauge_rearr radial_collapse radial_gauge_identity radial_rearrangement)
      radial_start_coordinates radial_wave_radial Formalism.FourierDecayAlt.P5.waveCExists radial_residue_formula radial_wave_function_field radial_operator_function_field radial_group_residue)
    (Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds)
    radial_orbital_niceness radial_wave_orbital radial_operator_locality

theorem radDecay_of_spec (h : RDIdentSpec) : RadDecay :=
  radDecay_of_ABQ (rDIdentABQ_of_spec h radial_identity_of_spectral_data)

end Formalism.FourierDecayAlt.P.CutSE
end

section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem leibniz_class : LeibnizCls := leibnizCls_of_radLoc spectral_radial_locality

theorem density_smooth_class : DensSmoothCls := densSmoothCls_of_radLoc spectral_radial_locality

theorem thmPActualCpt_of_spec (h : RDIdentSpec) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_leaves (one_letter_density_estimate leibniz_class density_smooth_class) density_smooth_class
    (radDecay_of_spec h)

end Formalism.FourierDecayAlt.P.CutSE
end
