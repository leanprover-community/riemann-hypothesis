import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.TwistedTransfer

theorem fsv_mul_conj (s t : ℂ) : fsv s t * conj (fsv s t) = 1 := by
  unfold fsv
  rw [← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_sub, map_mul, Complex.conj_conj]
  ring

theorem fsv_zero (t : ℂ) : fsv 0 t = 1 := by
  simp [fsv]

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem hsInner_smul_right (a : ℂ) (U V : Wq →L[ℂ] Wp) : B.hsInner U (a • V) = conj a * B.hsInner U V := by
  have e : Formalism.FourierDecayAlt.B.hsVec (a • V) = a • Formalism.FourierDecayAlt.B.hsVec V := by
    unfold Formalism.FourierDecayAlt.B.hsVec
    rw [← WithLp.toLp_smul]
    rfl
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [e, inner_smul_left]

theorem pairAt_mulOp_right (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Φ (Wv Ψ) c = conj (fsv s (c l)) * pairAt μ Φ Ψ c := by
  unfold pairAt
  simp only [hW Ψ c, hsInner_smul_right]
  exact integral_const_mul _ _

theorem form_mulOp_right (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ u (act (io (mkP Wv Wv')) y) (Function.update c l t) =
      conj (fsv s t) * form μ l.succ u y (Function.update c l t) := by
  unfold form
  rw [← integral_const_mul]
  congr 1
  funext c'
  simp only [act_io]
  change _ * ∑ a, pairAt μ (u a) (Wv (y a)) _ = _
  simp only [pairAt_mulOp_right μ l s Wv hW, glue_succ_update, ← Finset.mul_sum]
  ring

theorem act_Vw_zero (w : List (Letter ℂ S)) (x : Ix S → RadSp k r z z' π π') :
    act (Vw (mkP (1 : Module.End ℂ (RadSp k r z z' π π')) 1) 0 w) x = x := by
  have hU : ∀ w : List (Letter ℂ S), (UUiw (0 : ℂ) w : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) = 1 := by
    intro w
    induction w with
    | nil => rfl
    | cons l w ih =>
      rw [UUiw, ih, mul_one]
      have h0 : (Uinv (A := Pr (RadSp k r z z' π π')) (if l.plus then (0 : ℂ) else star 0)) = 1 := by
        rw [star_zero, ite_self]
        unfold Uinv
        rw [map_zero]
        exact Matrix.one_fin_two.symm
      rw [h0, Formalism.FourierDecayAlt.P.Wd11.liftMatrix_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]
  have h1 : (mkP (1 : Module.End ℂ (RadSp k r z z' π π')) 1) = 1 := rfl
  funext a
  rw [Vw, hU, mul_one, h1, act_io]
  rfl

theorem isMulOp_one_c (l : Fin r) :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun c _ => fsv 0 (c l)) := by
  intro Φ c g
  simp [fsv_zero]

theorem isMulOp_one_c' (l : Fin r) :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun c _ => fsv (-0) (c l)) := by
  intro Φ c g
  simp [fsv_zero]

theorem isMulOp_one_zeta :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun _ g => fsv 0 (P5.zeta k r z z' g)) := by
  intro Φ c g
  simp [fsv_zero]

theorem isMulOp_one_zeta_conj :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun _ g => fsv (-0) (P5.zeta k r z z' g)) := by
  intro Φ c g
  simp [fsv_zero]

end Wave

section Step

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)

theorem ph_wave_right (hD : IsData P z z' π π' X μ L st l0) (w : List (Letter ℂ S))
    (hnd : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (l : Fin P.r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (t : ℂ) :
    ph L st μ l w x (act (Vw (mkP Wv Wv') s w) y) c t = conj (fsv s t) * ph L st μ l w x y c t := by
  obtain ⟨hwave, hc1, hc2, hp⟩ := waveSiteAll Wp Wq P z z' π π' X L hD.2.2.1 l s Wv Wv' hW hW'
  have hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w :=
    Formalism.FourierDecayAlt.P.plane_wave_vector_identity ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hnd
  simp only [P5.ph, RRform]
  rw [← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) y, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) y,
    form_mulOp_right μ l s Wv Wv' hW]
  ring

theorem rr_wave_A (hD : IsData P z z' π π' X μ L st l0) (hOn : ThmPOn (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (hr : 0 < P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c ⟨0, hr⟩))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c ⟨0, hr⟩)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K 0) x) (hy : InK (K 0) y)
    (hVy : InK (K 0) (act (Vw (mkP Wv Wv') s w) y)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) :
    RRform L st μ 0 w (act (Vw (mkP Wv Wv') s w) x) (act (Vw (mkP Wv Wv') s w) y) c = RRform L st μ 0 w x y c := by
  have hl : (⟨0, hr⟩ : Fin P.r).castSucc = 0 := Fin.ext rfl
  have hstep := (hOn w hw).2.1 ⟨0, hr⟩
  unfold StepP at hstep
  rw [hl] at hstep
  obtain ⟨φ, -, hφ, -, hφs⟩ := hstep x (act (Vw (mkP Wv Wv') s w) y) hx hVy c hc
  obtain ⟨ψ, -, hψ, -, hψs⟩ := hstep x y hx hy c hc
  have h1 := hφs s Wv Wv' hW hW'
  have h0 := hψs 0 1 1 (isMulOp_one_c _) (isMulOp_one_c' _)
  rw [act_Vw_zero] at h0
  rw [← h1, ← h0]
  have hae : ∀ᵐ t : ℂ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℂ) : volume ({0} : Set ℂ) = 0)
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [hφ t ht, hψ t ht, ph_wave_right P z z' π π' X μ L st l0 hD w hw.1.1 ⟨0, hr⟩ s Wv Wv' hW hW',
    fsv_zero, ← mul_assoc, fsv_mul_conj, one_mul]

theorem topDens_wave_right (hD : IsData P z z' π π' X μ L st l0) (w : List (Letter ℂ S))
    (hw : Fr.admitted st w) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun _ g => fsv s (P5.zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (P5.zeta P.k P.r z z' g)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r) :
    topDens L st w x (act (Vw (mkP Wv Wv') s w) y) c g =
      conj (fsv s (P5.zeta P.k P.r z z' g)) * topDens L st w x y c g := by
  obtain ⟨hP, -, hAL, hQQ, -, -, hSL, hLS⟩ := hD
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (P5.zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (P5.zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]
  have f_fi : mkP Wv Wv' * mkP Wv' Wv = 1 := pr_ext (by simpa using hWW') (by simpa using hWW')
  have fi_f : mkP Wv' Wv * mkP Wv Wv' = 1 := pr_ext (by simpa using hW'W) (by simpa using hW'W)
  have hfn : ∀ g ∈ Fr.zfns L, Commute (mkP Wv Wv') g := by
    obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hAL
    have key : ∀ j j' : Fin 6, Commute (mkP Wv Wv') (mkP (X.fn j) (X.fn j')) := by
      intro j j'
      show _ * _ = _ * _
      exact pr_ext (by simpa using mulOp_comm_fn X Wv _ hW j) (by simpa using (mulOp_comm_fn X Wv' _ hW' j').symm)
    intro g hg
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact key _ _
    · rw [hzi]; exact key _ _
    · rw [hzb]; exact key _ _
    · rw [hzbi]; exact key _ _
    · rw [hG]; exact key _ _
    · rw [hGi]; exact key _ _
  have hGG : Commute (mkP Wv Wv') L.GG := hfn _ (mem_zfns L).2.2.2.2.1
  have hfiGG : Commute (mkP Wv' Wv) L.GG := (commute_inv hGG.symm f_fi fi_f).symm
  obtain ⟨e11, e10⟩ := zeta_entries Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt hP X st l0 hQQ s Wv Wv' hW hW'
  have hx : ∀ Y, Commute (mkP Wv Wv') (st.x Y) := by
    intro Y
    have h := e11 Y
    rw [hLS.tau Y] at h
    have h1 : L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv') = L.GG * st.x Y := by
      conv_rhs => rw [← h]
      rw [← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq]
      simp only [mul_assoc]
    have h2 : mkP Wv' Wv * st.x Y * mkP Wv Wv' = st.x Y := by
      calc mkP Wv' Wv * st.x Y * mkP Wv Wv' = L.GGi * (L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv')) := by
            rw [← mul_assoc, L.GGi_GG, one_mul]
        _ = L.GGi * (L.GG * st.x Y) := by rw [h1]
        _ = st.x Y := by rw [← mul_assoc, L.GGi_GG, one_mul]
    show mkP Wv Wv' * st.x Y = st.x Y * mkP Wv Wv'
    calc mkP Wv Wv' * st.x Y = mkP Wv Wv' * (mkP Wv' Wv * st.x Y * mkP Wv Wv') := by rw [h2]
      _ = st.x Y * mkP Wv Wv' := by rw [← mul_assoc, ← mul_assoc, f_fi, one_mul]
  have hl : ∀ Y ∈ st.inv, mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv' =
      L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ _ s := by
    intro Y hY
    have h := e10 Y
    rw [hLS.low Y hY, hLS.tau Y] at h
    have hfix : Commute (mkP Wv' Wv) (st.x Y) := (commute_inv (hx Y).symm f_fi fi_f).symm
    have cancel : ∀ T, st.xi Y * L.GGi * (L.GG * st.x Y * T) = T := by
      intro T
      calc st.xi Y * L.GGi * (L.GG * st.x Y * T) = st.xi Y * (L.GGi * L.GG) * st.x Y * T := by
            simp only [mul_assoc]
        _ = T := by rw [L.GGi_GG, mul_one, (hLS.x_xi Y hY).2, one_mul]
    have h3 : mkP Wv' Wv * (L.GG * st.x Y * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)) * mkP Wv Wv' =
        L.GG * st.x Y * (mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv') := by
      rw [← mul_assoc (mkP Wv' Wv) (L.GG * st.x Y), ← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq,
        mul_assoc L.GG (mkP Wv' Wv), hfix.eq]
      simp only [mul_assoc]
    rw [h3, ← mul_sub] at h
    rw [← cancel (mkP Wv' Wv * _ * mkP Wv Wv'), h, cancel]
  have hWH : WaveHyp L st (mkP Wv Wv') (mkP Wv' Wv) s := ⟨f_fi, fi_f, rfl, hfn, hx, hl⟩
  obtain ⟨hFV, -⟩ := frame_twist_F hSL hLS hWH w hw
  unfold topDens
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← act_mul, hFV, act_mul (io (mkP Wv Wv')) (Fr.ofWord L st w).F y, act_io, mkPair_fst', hW1, hsInner_smul_right]

theorem rr_wave_B (hD : IsData P z z' π π' X μ L st l0) (hOn : ThmPOn (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (hr : P.r = 0) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun _ g => fsv s (P5.zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (P5.zeta P.k P.r z z' g)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K 0) x) (hy : InK (K 0) y)
    (hVy : InK (K 0) (act (Vw (mkP Wv Wv') s w) y)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) :
    RRform L st μ 0 w (act (Vw (mkP Wv Wv') s w) x) (act (Vw (mkP Wv Wv') s w) y) c = RRform L st μ 0 w x y c := by
  have hl : (0 : Fin (P.r + 1)) = Fin.last P.r := Fin.ext (by simp [hr])
  obtain ⟨hTop, -, -⟩ := hOn w hw
  rw [hl] at hx hy hVy ⊢
  obtain ⟨-, hφs, -⟩ := hTop x (act (Vw (mkP Wv Wv') s w) y) hx hVy c hc
  obtain ⟨-, hψs, -⟩ := hTop x y hx hy c hc
  have h0 := hψs 0 1 1 isMulOp_one_zeta isMulOp_one_zeta_conj
  rw [act_Vw_zero] at h0
  rw [← hφs s Wv Wv' hW hW', ← h0]
  congr 1
  funext g
  rw [topDens_wave_right P z z' π π' X μ L st l0 hD w hw.1 s Wv Wv' hW hW', fsv_zero, ← mul_assoc, fsv_mul_conj,
    one_mul]

end Step

end Formalism.FourierDecayAlt.P.PBFV
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

section Lift

variable {A : Type} [Ring A] {n : ℕ}

theorem sum_ix_succ {M : Type*} [AddCommMonoid M] (f : Ix (Fin (n + 1)) → M) :
    ∑ z, f z = ∑ i : Fin 2, ∑ e : Ix (Fin n), f (Fin.cons i e) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective (fun p : Fin 2 × Ix (Fin n) => (Fin.cons p.1 p.2 : Ix (Fin (n + 1)))) ⟨?_, ?_⟩ _ _
    (fun p => rfl)
  · rintro ⟨i, e⟩ ⟨i', e'⟩ h
    have h' := Fin.cons_injective2 h
    simp only at h'
    rw [h'.1, h'.2]
  · intro z
    exact ⟨(z 0, Fin.tail z), Fin.cons_self_tail z⟩

theorem ix_ext_iff (z z' : Ix (Fin (n + 1))) : z = z' ↔ z 0 = z' 0 ∧ Fin.tail z = Fin.tail z' := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail z', h0, ht]

def liftM (M : SlopeTestRemainingChoices (Fin n) A) : SlopeTestRemainingChoices (Fin (n + 1)) A :=
  Matrix.of fun z z' => if z 0 = z' 0 then M (Fin.tail z) (Fin.tail z') else 0

theorem liftM_apply (M : SlopeTestRemainingChoices (Fin n) A) (z z' : Ix (Fin (n + 1))) :
    liftM M z z' = if z 0 = z' 0 then M (Fin.tail z) (Fin.tail z') else 0 := rfl

theorem liftM_one : liftM (1 : SlopeTestRemainingChoices (Fin n) A) = 1 := by
  ext z z'
  rw [liftM_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h0 : z 0 = z' 0
  · by_cases ht : Fin.tail z = Fin.tail z'
    · rw [if_pos h0, if_pos ht, if_pos ((ix_ext_iff z z').2 ⟨h0, ht⟩)]
    · rw [if_pos h0, if_neg ht, if_neg (fun h => ht ((ix_ext_iff z z').1 h).2)]
  · rw [if_neg h0, if_neg (fun h => h0 ((ix_ext_iff z z').1 h).1)]

theorem liftM_zero : liftM (0 : SlopeTestRemainingChoices (Fin n) A) = 0 := by
  ext z z'; simp [liftM_apply]

theorem liftM_add (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M + N) = liftM M + liftM N := by
  ext z z'; simp only [liftM_apply, Matrix.add_apply]; split_ifs <;> simp

theorem liftM_mul (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M * N) = liftM M * liftM N := by
  ext z z''
  rw [Matrix.mul_apply, sum_ix_succ]
  simp only [liftM_apply, Fin.cons_zero, Fin.tail_cons, Matrix.mul_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Fin.sum_univ_two]
  by_cases h0 : z 0 = 0 <;> by_cases h1 : z'' 0 = 0
  · simp [h0, h1]
  · have h1' : z'' 0 = 1 := by omega
    simp [h0, h1']
  · have h0' : z 0 = 1 := by omega
    simp [h0', h1]
  · have h0' : z 0 = 1 := by omega
    have h1' : z'' 0 = 1 := by omega
    simp [h0', h1']

def liftRingHomSucc : SlopeTestRemainingChoices (Fin n) A →+* SlopeTestRemainingChoices (Fin (n + 1)) A where
  toFun := liftM
  map_one' := liftM_one
  map_mul' := liftM_mul
  map_zero' := liftM_zero
  map_add' := liftM_add

theorem liftRingHom_apply_eq_liftM (M : SlopeTestRemainingChoices (Fin n) A) : (liftRingHomSucc M : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM M := rfl

theorem eU_succ (a : Fin n) (i j : Fin 2) : (eU a.succ i j : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (eU a i j) := by
  ext x y
  rw [liftM_apply]
  simp only [eU, Matrix.of_apply]
  have key : (x a.succ = i ∧ y a.succ = j ∧ ∀ b, b ≠ a.succ → x b = y b) ↔
      (x 0 = y 0 ∧ (Fin.tail x a = i ∧ Fin.tail y a = j ∧ ∀ b, b ≠ a → Fin.tail x b = Fin.tail y b)) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h3 0 (Fin.succ_ne_zero a).symm, h1, h2, fun b hb => h3 b.succ (fun h => hb (Fin.succ_injective _ h))⟩
    · rintro ⟨h0, h1, h2, h3⟩
      refine ⟨h1, h2, fun b hb => ?_⟩
      exact Fin.cases (motive := fun b => b ≠ a.succ → x b = y b) (fun _ => h0)
        (fun b' hb' => h3 b' (fun h => hb' (by rw [h]))) b hb
  by_cases h0 : x 0 = y 0
  · rw [if_pos h0]
    by_cases h : Fin.tail x a = i ∧ Fin.tail y a = j ∧ ∀ b, b ≠ a → Fin.tail x b = Fin.tail y b
    · rw [if_pos h, if_pos (key.2 ⟨h0, h⟩)]
    · rw [if_neg h, if_neg (fun h' => h (key.1 h').2)]
  · rw [if_neg h0, if_neg (fun h' => h0 (key.1 h').1)]

theorem io_succ (x : A) : (io x : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (io x) := by
  ext z z'
  rw [liftM_apply]
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h0 : z 0 = z' 0
  · by_cases ht : Fin.tail z = Fin.tail z'
    · rw [if_pos h0, if_pos ht, if_pos ((ix_ext_iff z z').2 ⟨h0, ht⟩)]
    · rw [if_pos h0, if_neg ht, if_neg (fun h => ht ((ix_ext_iff z z').1 h).2)]
  · rw [if_neg h0, if_neg (fun h => h0 ((ix_ext_iff z z').1 h).1)]

theorem liftZero_succ_eq_map (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices (Fin (n + 1)) A)) = (lift0 M).map liftM := by
  ext i j; simp [lift0, io_succ]

theorem ins_succ (a : Fin n) (M : M2 (SlopeTestRemainingChoices (Fin n) A)) : ins a.succ (M.map liftM) = liftM (ins a M) := by
  simp only [ins]
  rw [← liftRingHom_apply_eq_liftM, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, liftRingHom_apply_eq_liftM, liftRingHom_apply_eq_liftM, eU_succ, Matrix.map_apply]

def upL (l : Letter ℂ (Fin n)) : Letter ℂ (Fin (n + 1)) := ⟨l.plus, l.intersection_update_fsHerm_neg_one.succ, l.pt⟩

theorem UUiw_succ [Algebra ℂ A] [StarRing A] (s : ℂ) (u : List (Letter ℂ (Fin n))) :
    (UUiw s (u.map upL) : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (UUiw s u) := by
  induction u with
  | nil => exact liftM_one.symm
  | cons l u ih =>
    simp only [List.map_cons, UUiw]
    rw [ih, liftM_mul]
    congr 1
    show ins l.intersection_update_fsHerm_neg_one.succ (lift0 (Uinv (if l.plus then s else star s))) = _
    rw [liftZero_succ_eq_map, ins_succ]

theorem positioned_cons (l : C.Letter) (w : List C.Letter) :
    D.positionted (l :: w) = (⟨l.1, 0, (l.2 : ℂ)⟩ : Letter ℂ (Fin (w.length + 1))) :: (D.positionted w).map upL := by
  simp only [D.positionted, List.ofFn_succ, List.map_ofFn]
  rfl

end Lift

section ActU

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {n : ℕ}

theorem act_liftM (M : SlopeTestRemainingChoices (Fin n) (Pr (RadSp k r z z' π π'))) (X : Ix (Fin (n + 1)) → RadSp k r z z' π π')
    (i : Fin 2) (e : Ix (Fin n)) :
    act (liftM M) X (Fin.cons i e) = act M (fun e' => X (Fin.cons i e')) e := by
  have key : ∀ (i' : Fin 2) (e' : Ix (Fin n)), (liftM M (Fin.cons i e) (Fin.cons i' e')).1 (X (Fin.cons i' e')) =
      if i = i' then (M e e').1 (X (Fin.cons i' e')) else 0 := by
    intro i' e'
    rw [liftM_apply, Fin.cons_zero, Fin.cons_zero, Fin.tail_cons, Fin.tail_cons]
    split_ifs <;> rfl
  simp only [act]
  rw [sum_ix_succ]
  simp only [key]
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp

theorem cons_ne_zero_iff (i0 i' : Fin 2) (e e' : Ix (Fin n)) :
    (∀ b : Fin (n + 1), b ≠ 0 → (Fin.cons i0 e : Ix (Fin (n + 1))) b = (Fin.cons i' e' : Ix (Fin (n + 1))) b) ↔
      e = e' := by
  constructor
  · intro h; funext t; exact h t.succ (Fin.succ_ne_zero t)
  · rintro rfl b hb
    obtain ⟨s, rfl⟩ := Fin.exists_succ_eq.2 hb
    simp only [Fin.cons_succ]

theorem insert_unit_matrix_zero_apply {B : Type} [Ring B] (i j i0 : Fin 2) (e : Ix (Fin n)) (z' : Ix (Fin (n + 1))) :
    (eU (0 : Fin (n + 1)) i j : SlopeTestRemainingChoices (Fin (n + 1)) B) (Fin.cons i0 e) z' =
      if i0 = i ∧ z' = Fin.cons j e then 1 else 0 := by
  simp only [eU, Matrix.of_apply, Fin.cons_zero]
  have : (i0 = i ∧ z' 0 = j ∧ ∀ b, b ≠ 0 → (Fin.cons i0 e : Ix (Fin (n + 1))) b = z' b) ↔
      (i0 = i ∧ z' = Fin.cons j e) := by
    rw [← Fin.cons_self_tail z', cons_ne_zero_iff, Fin.cons_zero]
    constructor
    · rintro ⟨h1, h2, h3⟩; rw [h2, ← h3]; exact ⟨h1, rfl⟩
    · rintro ⟨h1, h2⟩
      have h2' := Fin.cons_injective2 h2
      exact ⟨h1, h2'.1, h2'.2.symm⟩
  simp only [this]

theorem act_addM (M N : SlopeTestRemainingChoices (Fin (n + 1)) (Pr (RadSp k r z z' π π'))) (X : Ix (Fin (n + 1)) → RadSp k r z z' π π') :
    act (M + N) X = act M X + act N X := by
  funext a
  simp only [act, Matrix.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  rfl

theorem act_zeroM (X : Ix (Fin (n + 1)) → RadSp k r z z' π π') :
    act (0 : SlopeTestRemainingChoices (Fin (n + 1)) (Pr (RadSp k r z z' π π'))) X = 0 := by
  funext a
  simp only [act, Matrix.zero_apply, Pi.zero_apply]
  exact Finset.sum_eq_zero fun _ _ => rfl

theorem act_sumM {ι : Type} (s : Finset ι) (M : ι → SlopeTestRemainingChoices (Fin (n + 1)) (Pr (RadSp k r z z' π π')))
    (X : Ix (Fin (n + 1)) → RadSp k r z z' π π') : act (∑ i ∈ s, M i) X = ∑ i ∈ s, act (M i) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact act_zeroM X
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, act_addM, ih]

theorem act_unit_matrix_zero_radial (i j i0 : Fin 2) (W : Ix (Fin (n + 1)) → RadSp k r z z' π π') (e : Ix (Fin n)) :
    act (eU (0 : Fin (n + 1)) i j : SlopeTestRemainingChoices (Fin (n + 1)) (Pr (RadSp k r z z' π π'))) W (Fin.cons i0 e) =
      if i0 = i then W (Fin.cons j e) else 0 := by
  simp only [act, insert_unit_matrix_zero_apply]
  have key : ∀ q : Ix (Fin (n + 1)),
      ((if i0 = i ∧ q = Fin.cons j e then (1 : Pr (RadSp k r z z' π π')) else 0).1) (W q) =
      if q = Fin.cons j e then (if i0 = i then W q else 0) else 0 := by
    intro q
    by_cases h1 : i0 = i <;> by_cases h2 : q = Fin.cons j e <;> simp [h1, h2] <;> rfl
  simp only [key]
  rw [Finset.sum_eq_single (Fin.cons j e) (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
  simp

theorem act_insert_numeric_matrix_zero (U : M2 (Pr (RadSp k r z z' π π'))) (W : Ix (Fin (n + 1)) → RadSp k r z z' π π')
    (i0 : Fin 2) (e : Ix (Fin n)) :
    act (ins (0 : Fin (n + 1)) (lift0 U)) W (Fin.cons i0 e) = ∑ j, (U i0 j).1 (W (Fin.cons j e)) := by
  simp only [ins, lift0, Matrix.map_apply]
  rw [act_sumM, Finset.sum_apply]
  simp only [act_sumM, Finset.sum_apply, act_mul, act_unit_matrix_zero_radial, act_io]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i0 <;> simp

theorem pr_alg_fst_apply (c : ℂ) (Φ : RadSp k r z z' π π') :
    (algebraMap ℂ (Pr (RadSp k r z z' π π')) c).1 Φ = c • Φ := rfl

theorem pr_one_fst_apply (Φ : RadSp k r z z' π π') : (1 : Pr (RadSp k r z z' π π')).1 Φ = Φ := rfl

theorem pr_zero_fst_apply (Φ : RadSp k r z z' π π') : (0 : Pr (RadSp k r z z' π π')).1 Φ = 0 := rfl

theorem uInv_cons {X : Type} [AddCommGroup X] [Module ℂ X] (s : ℂ) (l : C.Letter) (w : List C.Letter)
    (x : Ix (Fin (l :: w).length) → X) (e : Ix (Fin (l :: w).length)) :
    KB.uInv s (l :: w) x e = if e 0 = 0 then KB.uInv s w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons 1 e')) (fun a => e a.succ) +
        (if l.1 then s else conj s) • KB.uInv s w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ) := rfl

theorem act_UUiw (s : ℂ) : ∀ (w : List C.Letter) (Φ : Ix (Fin w.length) → RadSp k r z z' π π'),
    act (UUiw s (D.positionted w)) Φ = KB.uInv s w Φ
  | [], Φ => by
    funext a
    show act 1 Φ a = Φ a
    simp only [act, Matrix.one_apply]
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb)]; rfl) (fun h => absurd (Finset.mem_univ a) h)]
    simp
  | l :: w, Φ => by
    funext z0
    obtain ⟨i, e, rfl⟩ : ∃ i e, z0 = (Fin.cons i e : Ix (Fin (w.length + 1))) :=
      ⟨z0 0, Fin.tail z0, (Fin.cons_self_tail z0).symm⟩
    rw [positioned_cons]
    simp only [UUiw]
    rw [UUiw_succ, act_mul, act_insert_numeric_matrix_zero]
    simp only [act_liftM, act_UUiw s w]
    rw [uInv_cons, Fin.sum_univ_two]
    simp only [Fin.cons_zero, Fin.cons_succ]
    fin_cases i
    · simp [Uinv, pr_one_fst_apply, pr_zero_fst_apply]
    · simp [Uinv, pr_one_fst_apply, pr_alg_fst_apply]
      rw [add_comm]

end ActU

theorem uInv_map {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : X →ₗ[ℂ] Y) (s : ℂ) :
    ∀ (w : List C.Letter) (x : Ix (Fin w.length) → X) (e : Ix (Fin w.length)),
      T (KB.uInv s w x e) = KB.uInv s w (fun e => T (x e)) e
  | [], x, e => rfl
  | l :: w, x, e => by
    unfold KB.uInv
    split_ifs
    · exact uInv_map T s w _ _
    · rw [map_add, map_smul, uInv_map T s w, uInv_map T s w]
    · rw [map_add, map_smul, uInv_map T s w, uInv_map T s w]

end Formalism.FourierDecayAlt.P.PBFV
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

section Pic

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem JF_mul_inv (Bs : B.RealPlaceData k r Wp Wq) (m : B.Mat k r → ℂ)
    (hm : ∀ p : B.SS k r, Bs.inSS p → ∀ g, m (B.sgs p g) = m g) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h : B.Mat k r) : B.JF Bs (fun g => m g • F g) h = m h • B.JF Bs F h := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun g => m g • F g) h ∂Bs.μSS = m h • ∫ p, JF.xiP Bs p • B.rho Bs p F h ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hm p hp h]
  exact smul_comm _ _ _

theorem JF_uInv (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) {h : B.Mat k r} (hh : h ∈ JF.Om k r Bs.z Bs.z') :
    ∀ (w : List C.Letter) (x : Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)), (∀ e, JC.NiceCoef Bs ε (x e)) →
      ∀ e, B.JF Bs (KB.uInv s w x e) h = KB.uInv s w (fun e => B.JF Bs (x e) h) e
  | [], x, _, e => rfl
  | l :: w, x, hx, e => by
    rw [uInv_cons, uInv_cons]
    by_cases h0 : e 0 = 0
    · rw [if_pos h0, if_pos h0]
      exact JF_uInv Bs ε s hh w _ (fun e' => hx _) _
    · rw [if_neg h0, if_neg h0]
      generalize (if l.1 = true then s else (starRingEnd ℂ) s) = c
      have h1 := uInv_nice Bs ε s w (fun e' => x (Fin.cons 1 e')) (fun e' => hx _) (fun a => e a.succ)
      have h2 := uInv_nice Bs ε s w (fun e' => x (Fin.cons 0 e')) (fun e' => hx _) (fun a => e a.succ)
      have e1 := JCx2.bc_JF_add h1 (JCx2.mn_nice_smul c h2) hh
      calc B.JF Bs ((KB.uInv s w (fun e' => x (Fin.cons 1 e')) fun a => e a.succ) +
            c • (KB.uInv s w (fun e' => x (Fin.cons 0 e')) fun a => e a.succ)) h
          = B.JF Bs (fun g => (KB.uInv s w (fun e' => x (Fin.cons 1 e')) fun a => e a.succ) g +
            (fun g => c • (KB.uInv s w (fun e' => x (Fin.cons 0 e')) fun a => e a.succ) g) g) h := rfl
        _ = _ := e1
        _ = _ := by
          rw [JCx2.bc_JF_smul, JF_uInv Bs ε s hh w _ (fun e' => hx _), JF_uInv Bs ε s hh w _ (fun e' => hx _)]

end Pic

section Minor

variable {k r : ℕ}

theorem first_minor_cell_eq_coord {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hr : 0 < r)
    (c : Fin r → ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (h1 : 1 < r + 2) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, h1⟩ = c ⟨0, hr⟩ := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ := by
    rw [Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  rw [e]
  have hmin := (big_cell_minors_holds k r z z' c μ hz hz').1 ⟨1, by omega⟩
  have hl : (⟨(⟨1, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = ⟨1, h1⟩ := Fin.ext rfl
  rw [hl] at hmin
  rw [hmin]
  have hs : (Finset.univ.filter fun a : Fin r => a.val < (⟨1, by omega⟩ : Fin (r + 1)).val) = {⟨0, hr⟩} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ha; exact Fin.ext (by simp at ha; omega)
    · rintro rfl; simp
  rw [Finset.prod_filter, ← Finset.prod_filter, hs, Finset.prod_singleton]

theorem first_minor_top_eq_zeta {z z' : Fin (2 * r + k + 1) → ℂ} (hr : r = 0) (c : Fin r → ℂ) (g : Mx k r) (h1 : 1 < r + 2) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, h1⟩ = P5.zeta k r z z' g := by
  subst hr
  have hw : wCell k 0 (Fin.last 0) c = 1 := Formalism.FourierDecayAlt.P.Qx6.wCell_zero c
  rw [hw, one_mul, dmin_one]
  simp [P5.zeta, zetaL, fvec]

end Minor

section Rad

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem radPic_wave (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (w : List C.Letter)
    (x : Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e))
    (Φ : Ix (Fin w.length) → RadSp k r Bs.z Bs.z' Bs.π Bs.π')
    (hΦ : ∀ e, ∀ y ∈ DomR k r Bs.z Bs.z',
      (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF Bs (x e)) y.1 y.2)
    (m : (Fin r → ℂ) → Mx k r → ℂ) (h1 : 1 < r + 2)
    (hm : ∀ y ∈ DomR k r Bs.z Bs.z', m y.1 y.2 = fsv s (Dmin k r Bs.z Bs.z' (wCell k r (Fin.last r) y.1 * y.2) ⟨1, h1⟩))
    (Wv Wv' : Module.End ℂ (RadSp k r Bs.z Bs.z' Bs.π Bs.π')) (hW : multiplicationOperator Wv m) :
    ∀ e, ∀ y ∈ DomR k r Bs.z Bs.z', (act (Vw (mkP Wv Wv') s (D.positionted w)) Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG k r (Fin.last r) (B.JF Bs (KB.waveG Bs s w x e)) y.1 y.2 := by
  intro e y hy
  have hGV : wCell k r (Fin.last r) y.1 * y.2 ∈ B.GV k r := by
    rw [Rad.wCell_last_eq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
  have hh : wCell k r (Fin.last r) y.1 * y.2 ∈ JF.Om k r Bs.z Bs.z' :=
    ⟨hGV, Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hy.1 hy.2.1 hy.2.2⟩
  set h := wCell k r (Fin.last r) y.1 * y.2 with hhdef
  rw [Vw, act_mul, act_io]
  change (Wv (act (UUiw s (D.positionted w)) Φ e) : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = _
  rw [hW, act_UUiw]
  let ev : RadSp k r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
    { toFun := fun Ψ => (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ((KB.uInv s w Φ e : RadSp k r Bs.z Bs.z' Bs.π Bs.π') : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      KB.uInv s w (fun e => (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) e := uInv_map ev s w Φ e
  rw [hev]
  have hfun : (fun e => (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) = fun e => resG k r (Fin.last r) (B.JF Bs (x e)) y.1 y.2 :=
    funext fun e => hΦ e y hy
  rw [hfun]
  simp only [resG]
  set gau : ℂ := ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖y.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ)
    with hgau
  have hsm := uInv_map ((gau • LinearMap.id : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))) s w (fun e => B.JF Bs (x e) h) e
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hsm
  rw [← hsm]
  unfold KB.waveG
  rw [JF_mul_inv Bs (fun g => P5.fsv s (Dmin k r Bs.z Bs.z' g ⟨1, h1⟩))
    (fun p hp g => by rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g]),
    JF_uInv Bs ε s hh w x hx e, hm y hy, smul_comm]

end Rad

end Formalism.FourierDecayAlt.P.PBFV
end
end
