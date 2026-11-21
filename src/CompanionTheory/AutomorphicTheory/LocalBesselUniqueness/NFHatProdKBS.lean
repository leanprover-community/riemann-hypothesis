import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.HatProd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpRFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHatProdKBStmt

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSectionVars false

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

open Formalism.FourierDecayAlt.P.CutMP

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem trJB_eq_trR (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    Gauge.trJB P Bs e J = Gauge.VLem.trR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) := by
  funext ρ
  show MA.toSm _ (Gauge.rawJ P Bs e J ρ) = _
  rw [Gauge.tc_rawJ]
  rfl

theorem trJB_of_res (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (F : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (h : ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
      Q.resG P.k P.r (Fin.last P.r) J c g = F c g) :
    Gauge.trJB P Bs e J = Gauge.VLem.trR P Bs.μsec e F := by
  funext ρ
  show MA.toSm _ (Gauge.rawJ P Bs e J ρ) = _
  rw [Gauge.tc_rawJ]
  show MA.toSm _ _ = MA.toSm _ _
  congr 1
  funext q
  have hmu := Gauge.tc_mu P Bs hpl q
  simp only [Gauge.rawR]
  rw [h q.1.1 q.2.1 _ hmu.1 hmu.2]

theorem commutes_of_real {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (ε : ℂ)
    (G : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)) (hO : B.opOrder Θ = r + k)
    (hR : ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
      ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • G F g)
    (hI : ∀ p : B.SS k r, D.inSS p → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, G (B.rho D p F) g = B.rho D p (G F) g) : B.Commutes D (B.GPos D) Θ := by
  intro p hp F hF g hg
  rw [hO] at hF
  have hgG : g ∈ B.GV k r := hg.1
  have hsg : B.sgs p g ∈ B.GV k r := sgs_gv D hp hgG
  rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG, hI p hp F hF g hg]
  simp only [B.rho]
  rw [hR _ _ hF _ hsg hsg]
  simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]

end place

theorem cap_A_bound : CapAB := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL y
  obtain ⟨Θ, Θv, hP, hPv, hO, hOv, hA, hAv⟩ := capelli_representation_holds P.k P.r Wp Wq y
  refine ⟨⟨Θ, ⟨hP, (capelli_invariance_criterion _ _ P Bs hpl hk y Θ hO.ge).1 hA⟩, fun J hJ => ?_⟩,
    ⟨Θv, ⟨hPv, (capelli_invariance_criterion _ _ P Bs hpl hk y Θv hOv.ge).2 hAv⟩, fun J hJ => ?_⟩⟩
  · have hF := Gauge.tc_famR P Bs hpl J hJ
    obtain ⟨⟨hA1, tA⟩, -⟩ := capelli_transition_holds _ _ P Bs hpl hk e he L hL _ _ hF y
    rw [trJB_of_res hpl e _ (dMul (drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)))
      (fun c hc g hg hcg => by
      obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg (B.opOrder Θ)
      rw [← jda_capelli_toda_proof _ _ P Bs hpl hk y J hJ c hc g hg hcg]
      simp only [Q.resG]
      rw [hA J _ hGV hCk]), trJB_eq_trR]
    funext ρ
    show MA.toSm _ (Gauge.rawR _ _ e (dMul (drF _) _) ρ) = _
    rw [(residue_derivative_transition _ _ P Bs hpl hk e he L hL _ _ hA1).2 ρ, R.LevelData.Ahat, Gauge.actA_mul, ← tA]
    rfl
  · have hF := Gauge.tc_famR P Bs hpl J hJ
    obtain ⟨-, ⟨hA1, tA⟩⟩ := capelli_transition_holds _ _ P Bs hpl hk e he L hL _ _ hF y
    rw [trJB_of_res hpl e _ (dMul (drbF P.r) (Q.crd (Q.cmp (vABm P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)))
      (fun c hc g hg hcg => by
      obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg (B.opOrder Θv)
      rw [← jda_capelli_toda_mirror_proof _ _ P Bs hpl hk y J hJ c hc g hg hcg]
      simp only [Q.resG]
      rw [hAv J _ hGV hCk]), trJB_eq_trR]
    funext ρ
    show MA.toSm _ (Gauge.rawR _ _ e (dMul (drbF _) _) ρ) = _
    rw [(residue_derivative_transition _ _ P Bs hpl hk e he L hL _ _ hA1).1 ρ, R.LevelData.Ahatv, Gauge.actA_mul, ← tA]
    rfl

theorem radP : JDRRadP := jDRRadP_of_steps residue_first_move_holds residue_second_move_holds

theorem radM : JDRRadM :=
  jDRRadM_of_parts mirror_residue_beta_holds mirror_residue_top_holds GrpMA.mirror_residue_first_move mirror_residue_second_move (jDRvConseq_of mirror_residue_continuity)

theorem cap_R_bound : CapRB := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he hQ L hL y
  have hD := isDom_omB Bs
  constructor
  · obtain ⟨ε, hε⟩ := radP P.k P.r
    obtain ⟨Θ, hP, hO, hR⟩ := ri_real (Wp := Wp) (Wq := Wq) Bs.z Bs.z' (y : ℂ) ε
    refine ⟨Θ, ⟨polyOp_mono (by omega) (Nat.le_mul_of_pos_left _ (by omega)) hP,
      commutes_of_real Bs Θ ε _ hO hR (inverse_function_positive_holds P.k P.r Wp Wq Bs (y : ℂ))⟩, fun J hJ => ?_⟩
    have hF := Gauge.tc_famR P Bs hpl J hJ
    rw [trJB_of_res hpl e _ (rhGrp P.k P.r Bs.z Bs.z' (y : ℂ) (Q.resG P.k P.r (Fin.last P.r) J))
      (fun c hc g hg hcg => by
      obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg ((P.r + P.k : ℕ) : ℕ∞)
      rw [← hε Wp Wq Bs.z Bs.z' Bs.π Bs.π' _ (y : ℂ) Bs.z_mem Bs.z'_mem hD J hJ c hc g hg hcg]
      simp only [Q.resG]
      rw [hR _ J hCk _ rfl hGV]), trJB_eq_trR]
    exact (jdr_tr_at residue_derivative_transition mirror_residue_model_holds P Bs hpl hk e he hQ L hL _ _ hF y).1
  · obtain ⟨ε, hε⟩ := radM P.k P.r
    obtain ⟨Θ, hP, hO, hR⟩ := rim_real (Wp := Wp) (Wq := Wq) Bs.z Bs.z' (y : ℂ) ε
    refine ⟨Θ, ⟨polyOp_mono (by omega) (Nat.le_mul_of_pos_left _ (by omega)) hP,
      commutes_of_real Bs Θ ε _ hO hR (inverse_function_minus_holds P.k P.r Wp Wq Bs (y : ℂ))⟩, fun J hJ => ?_⟩
    have hF := Gauge.tc_famR P Bs hpl J hJ
    rw [trJB_of_res hpl e _ (rhvGrp P.k P.r Bs.z Bs.z' (y : ℂ) (Q.resG P.k P.r (Fin.last P.r) J))
      (fun c hc g hg hcg => by
      obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg ((P.r + P.k : ℕ) : ℕ∞)
      rw [← hε Wp Wq Bs.z Bs.z' Bs.π Bs.π' _ (y : ℂ) Bs.z_mem Bs.z'_mem hD J hJ c hc g hg hcg]
      simp only [Q.resG]
      rw [hR _ J hCk _ rfl hGV]), trJB_eq_trR]
    exact (jdr_tr_at residue_derivative_transition mirror_residue_model_holds P Bs hpl hk e he hQ L hL _ _ hF y).2

theorem hat_product_bound : HatProdB :=
  hatProdB_of cap_A_bound cap_R_bound hat_bounded_decay_holds residue_splitting_holds mirror_residue_splitting_holds hat_lagrange_decay_holds
    hat_nodes_decay_holds

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
end
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

open Formalism.FourierDecayAlt.P.CutMP

theorem kbs_arith (R n N o A : ℝ) (hR : 0 ≤ R) (hn : 1 ≤ n) (hN : 0 ≤ N) (ho : o ≤ N * n)
    (hA : 18 * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A) : 12 * (R + 1) * n ^ 2 + 6 * R * o + 0 ≤ A := by
  have hρ4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hn2 : n ≤ n ^ 2 := le_self_pow₀ hn (by norm_num)
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by norm_num)
  have h1 : (R + 1) * n ^ 2 ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul hρ4 hn23 (by positivity) (by positivity)
  have h2 : R * o ≤ (R + 1) ^ 4 * (N * n ^ 2) :=
    calc R * o ≤ R * (N * n) := mul_le_mul_of_nonneg_left ho hR
      _ ≤ (R + 1) ^ 4 * (N * n ^ 2) :=
        mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hn2 hN) (by positivity) (by positivity)
  have h3 : 0 ≤ (R + 1) ^ 4 * n ^ 3 := by positivity
  have h4 : 0 ≤ (R + 1) ^ 4 * (N * n ^ 2) := by positivity
  nlinarith

theorem hatProdJB (hH : HatProdB) (hPoly : JDPolyOK) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (he : Gauge.IsFrameB P Bs e)
    (hQ : IsGaugeQQB P Bs e) (hL : MA.IsModelLevel P (MA.DQ P) L) (N : ℕ) (u : List (MA.A P (MA.DQ P)))
    (hN : u.length ≤ N) (hu : ∀ a ∈ u, a ∈ MA.hatSet P L) :
    ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (Th : Fin m → B.DiffOp P.k P.r Wp Wq),
      (∀ k, b k ∈ Submonoid.closure (MA.bddSet P L)) ∧
      (∀ k, B.SmoothCoef (B.GPos Bs) (Th k) ∧ B.Commutes Bs (B.GPos Bs) (Th k) ∧
        GlobCoef (Th k) (1 * ((P.r : ℝ) + 1) * nDim P.k P.r * ((N : ℝ) + 1)) ∧
        (B.opOrder (Th k) : ℝ) ≤ 1 * nDim P.k P.r * ((N : ℝ) + 1)) ∧
      ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
        18 * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
        B.JF Bs F ∈ FFB P Bs →
        MA.actA P u.prod (Gauge.trJB P Bs e (B.JF Bs F)) =
          ∑ k, MA.actA P (b k) (Gauge.trJB P Bs e (B.JF Bs (B.opApply (Th k) F))) := by
  obtain ⟨ts, hts, hJ⟩ := hH Wp Wq P Bs hpl hk e he hQ L hL u hu
  have hn : (1 : ℝ) ≤ nDim P.k P.r := by
    unfold nDim; exact_mod_cast Nat.le_add_left 1 _
  have hNr : (u.length : ℝ) ≤ N := by exact_mod_cast hN
  have hord : ∀ t ∈ ts, (B.opOrder t.2 : ℝ) ≤ (N : ℝ) * nDim P.k P.r := fun t ht => by
    have h := (hPoly _ _ _ _ _ _ _ (hts t ht).2.1).2.2
    have h' : (B.opOrder t.2 : ℝ) ≤ (u.length : ℝ) * nDim P.k P.r := by unfold nDim; exact_mod_cast h
    exact h'.trans (mul_le_mul_of_nonneg_right hNr (by linarith))
  refine ⟨ts.length, fun i => (ts.get i).1, fun i => (ts.get i).2, fun i => (hts _ (List.get_mem ts i)).1,
    fun i => ?_, fun F A _ hCC hA hJF => ?_⟩
  · have ht := List.get_mem ts i
    obtain ⟨hs, hg, -⟩ := hPoly _ _ _ _ _ _ _ (hts _ ht).2.1
    refine ⟨hs _, (hts _ ht).2.2, hg _ ?_, (hord _ ht).trans ?_⟩
    · have e1 : ((u.length * ((P.r + 1) * (2 * P.r + P.k + 1)) : ℕ) : ℝ) =
          (u.length : ℝ) * (((P.r : ℝ) + 1) * nDim P.k P.r) := by unfold nDim; push_cast; ring
      have h0 : 0 ≤ ((P.r : ℝ) + 1) * nDim P.k P.r := by positivity
      rw [e1]
      nlinarith
    · nlinarith
  · have hid : MA.actA P u.prod (Gauge.trJB P Bs e (B.JF Bs F)) = _ := hJ _ hJF
    show MA.actA P u.prod (Gauge.trJB P Bs e (B.JF Bs F)) =
      ∑ k : Fin ts.length, MA.actA P (ts.get k).1
        (Gauge.trJB P Bs e (B.JF Bs (B.opApply (ts.get k).2 F)))
    rw [hid, ← Fin.sum_univ_fun_getElem]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ht := List.get_mem ts i
    have hnE : nDim P.k P.r = 2 * (P.r : ℝ) + P.k + 1 := by unfold nDim; push_cast; ring
    have hT := jdc_thrW (k := P.k) (r := P.r) (B.opOrder (ts.get i).2) A 0 le_rfl
      (kbs_arith _ _ N _ A (Nat.cast_nonneg _) hn (Nat.cast_nonneg _) (hord _ ht) (by rw [hnE]; exact hA))
    have hth := Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ Bs A _ F (ts.get i).2 _ subset_rfl le_rfl hT (hCC _)
      (fun s hs f' hf' g hg => (hts _ ht).2.2 s hs f' hf' g (jdc_om_sub_gpos _ hg))
    exact congrArg _ (trJB_congr hpl e fun g hg => hth g (jdc_om_of _ _ hg.1 hg.2))

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
end
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

open Formalism.FourierDecayAlt.P.CutMP

theorem normal_form_hat_product_bessel : NFHatProdKBS := by
  refine ⟨1, 18, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p e L he hQ hL N u hN hu
  exact hatProdJB hat_product_bound polynomial_decay_admissible P p.T.base p.hP p.hl.2.2 e L he hQ hL N u hN hu

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
end
