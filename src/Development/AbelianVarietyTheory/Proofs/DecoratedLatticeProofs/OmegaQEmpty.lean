import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifiStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RightMove

variable {D : D7}

theorem topL_mul {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem lowZero_mul {κ : Type} [CommRing κ] {a b : ℕ} {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y)
    (γ : Matrix (Fin a) (Fin a) κ) : LowZero a (y * γ) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy i l hi l.2, zero_mul]

abbrev Cond {a b : ℕ} (L : LevDat D.host.E ℂ a) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : Prop :=
  (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1),
    (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
    (∀ PP : ↥L.Pg, g PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (g PP)) ∈ L.P.H

theorem cond_mul {a b : ℕ} (L : LevDat D.host.E ℂ a) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y z : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : ∀ PP, z PP = y PP * (γ PP).val)
    (h : Cond L y) : Cond L z := by
  obtain ⟨h1, g, h2, h3, h4⟩ := h
  refine ⟨fun PP hP' => (hz PP).symm ▸ lowZero_mul (h1 PP hP') _, fun PP => g PP * γ PP.1, fun PP => ?_,
    fun PP => mul_mem (h3 PP) (hγ PP.1 PP.2), ?_⟩
  · rw [Units.val_mul, h2, hz, topL_mul]
  · have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (g PP * γ PP.1)) =
        (fun PP => upperLeftBlock L.hr (g PP)) * (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) := by
      funext PP
      exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (h3 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact mul_mem h4 hP

theorem omegaG_mul_right : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  intro D a b L χ G hG hP y
  have hGi : ∀ PP ∈ L.Pg, (G PP)⁻¹ ∈ blockTri (blkOf L.r L.t) := fun PP h => inv_mem (hG PP h)
  have hPi : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) ∈ L.P.H := by
    have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) = (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1))⁻¹ := by
      funext PP
      exact extendOne_inv _ (blockTri_blkOf_le _ _ (hG PP.1 PP.2))
    rw [e]
    exact inv_mem hP
  unfold omegaG
  by_cases hy : Cond L y
  · have hy' : Cond L (fun PP => y PP * (G PP).val) := cond_mul L G hG hP y _ (fun _ => rfl) hy
    rw [dif_pos hy', dif_pos hy]
    have key : ∀ PP : ↥L.Pg, hy'.2.choose PP = hy.2.choose PP * G PP.1 := fun PP => Units.ext (by
      rw [Units.val_mul, hy'.2.choose_spec.1 PP, hy.2.choose_spec.1 PP, topL_mul])
    have hc : (⟨fun PP => upperLeftBlock L.hr (hy'.2.choose PP), hy'.2.choose_spec.2.2⟩ : L.P.H) =
        ⟨fun PP => upperLeftBlock L.hr (hy.2.choose PP), hy.2.choose_spec.2.2⟩ * ⟨_, hP⟩ :=
      Subtype.ext (funext fun PP => by
        show upperLeftBlock L.hr (hy'.2.choose PP) = upperLeftBlock L.hr (hy.2.choose PP) * upperLeftBlock L.hr (G PP.1)
        rw [key]
        exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (hy.2.choose_spec.2.1 PP)) (blockTri_blkOf_le _ _ (hG PP.1 PP.2)))
    have hd : ∀ PP : ↥L.Pg, ∀ c : ℕ, dBlk (blkOf L.r L.t) c (hy'.2.choose PP) =
        dBlk (blkOf L.r L.t) c (hy.2.choose PP) * dBlk (blkOf L.r L.t) c (G PP.1) := fun PP c => by
      rw [key]; exact diag_block_det_mul (hy.2.choose_spec.2.1 PP) (hG PP.1 PP.2)
    rw [hc, map_mul]
    simp only [hd]
    simp only [key, map_mul, Units.val_mul, mul_inv, Finset.prod_mul_distrib, Units.val_inv_eq_inv_val, Units.coe_prod]
    rw [← Finset.prod_coe_sort L.Pg (fun PP => ((χ PP (Matrix.GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ)⁻¹),
      ← Finset.prod_coe_sort L.Pg (fun PP => ∏ i ∈ Finset.range L.s, ((L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP)) : ℂˣ) : ℂ))]
    ring
  · have hy' : ¬ Cond L (fun PP => y PP * (G PP).val) := fun h => hy (cond_mul L (fun PP => (G PP)⁻¹) hGi hPi _ y
      (fun PP => by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]) h)
    rw [dif_neg hy', dif_neg hy, mul_zero]

end GlobalTheory.ChainOnto.RightMove
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPlacesDatum_mul_right_source_level : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  atlas_forward_decl GlobalTheory.ChainOnto.RightMove.omegaG_mul_right
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepLevLaw

theorem omegaQ_empty {D : D7} {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dif_pos (fun PP hP => absurd hP (Finset.notMem_empty PP))]
  simp

set_option maxHeartbeats 1000000 in
open Classical in

theorem stepLevLaw : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → ∀ ω, IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω → ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → ∀ κ ∈ levS s.V s.β s.L, κ ∈ GfC s.V ∧ ω (κ, 1) f = Lev.levChi s.V s.β s.L κ • f := by
  intro D c hc k s s' hs hs' ω hW ξ f₀ f hv κ hκ
  refine ⟨hκ.1, ?_⟩
  have hPg : s.L.Pg = c.Pg := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← hPg, ← Finset.union_empty s.L.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hc k k.isLt
  have hlev : Lev.finE s.V κ ∈ lev D.sp.cm s.V.gram s.β s.L := hκ.2
  have sg : Lev.finE s.V κ ∈ St s.β := parLev_St hlev.1
  have sh : Lev.finE s'.V 1 ∈ St s'.β := by rw [map_one]; exact Subgroup.one_mem _
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
    hs.selfDual hs'.selfDual hs.frame hs'.frame hf he' (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT
    hκ.1 (Subgroup.one_mem _) sg sh
  set G : ∀ PP : Pl D.host.E, GL (Fin s.V.rank) (kP PP) := fun PP => redFn s.β PP (Lev.finE s.V κ) with hG
  have h1' : ω (κ, 1) f₀ = ((∏ PP ∈ c.Pg, c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_inv, mul_one, hG]
  have hoG := GlobalTheory.T.levelPlacesDatum_mul_right_source_level D s.V.rank s'.V.rank s.L (c.chi (↑k + 1)) G (fun PP hP => parLev_g hlev.1 hP) hlev.2
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame κ 1 sg sh) _
    ((s.L.P.chi ⟨_, hlev.2⟩ * (∏ PP ∈ s.L.Pg, ∏ i ∈ Finset.range s.L.s, s.L.cg (i + 1) PP (dBlk (blkOf s.L.r s.L.t) (i + 1) (G PP))) *
      ∏ PP ∈ s.L.Pg, (c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D s.V s'.V s.β s'.β κ 1 sg sh x
      have i0 : IsHalf e (actO s.V s'.V κ⁻¹ 1⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H,
          fun H => GlobalTheory.SplitHecke.isHalf_actO _ _ H⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), omegaQ_empty, omegaQ_empty, mul_one, mul_one]
        simp only [map_one, redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        exact hoG (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H => hx ⟨i0.1 H.1, i1.1 H.2⟩, mul_zero])
  rw [h2]
  congr 1
  unfold Lev.levChi levFn
  rw [hQ, Finset.prod_empty, mul_one, extendOne_of_mem _ hlev.2, ← Units.val_mul, ← hPg, Finset.prod_inv_distrib]
  congr 1
  rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]

end GlobalTheory.ChainOnto.StepLevLaw

end
end
