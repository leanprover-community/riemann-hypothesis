import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsClassSelOfRowL
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfPrimesRel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProofStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitOfPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightWindowRequirementHostOfPoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsWeightsInWindows
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasWithDutyWallAndChoices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FixAndWinOfNumAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlotStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberTopFinalContextParameters

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

namespace UpperTheory.Top.PolynomialHostPrimeBound

open GlobalTheory.EX.DC

private theorem smallest_prime_polynomial_bound {A C : ℝ} (hA : 1 ≤ A)
    (hS : ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A)
    {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (h1 : (H.pde : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C)
    (h2 : (H.pde' : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C) :
    (q0H H : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ ((3 + 2 * C) * A) := by
  obtain ⟨p, hp, hm, hle⟩ := hS _ (one_lt_rPrH_mul H)
  have hq : (q0H H : ℝ) ≤ p := by exact_mod_cast globalTwisting_le_fact H hc hp hm
  have hN : 2 ≤ H.QS * H.q * H.d :=
    H.hyp.2.1.one_lt.trans_le (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))
  have e : ((H.QS : ℝ) * H.q * H.d) = ((H.QS * H.q * H.d : ℕ) : ℝ) := by push_cast; ring
  rw [e] at h1 h2 ⊢
  have a2 : 0 < H.pde - 1 := Nat.sub_pos_of_lt H.pde_prime.one_lt
  have a3 : 0 < H.pde' - 1 := Nat.sub_pos_of_lt H.pde'_prime.one_lt
  have hr : rPrH H ≤ 2 * (H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1)) := by
    have hM : 0 < H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) a2) a3
    obtain ⟨r, hr, hr1, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul _ hM.ne'
    refine (rPrH_le H hr ?_).trans hr2
    rw [hc, Ideal.absNorm_top, mul_one]
    exact Nat.not_dvd_of_pos_of_lt hM hr1
  generalize H.QS * H.q * H.d = N at *
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hr' : rPrH H ≤ N * (N * H.pde * H.pde') := hr.trans (by gcongr <;> omega)
  have hr'' : (rPrH H : ℝ) ≤ N * (N * H.pde * H.pde') := by exact_mod_cast hr'
  have hb : ((rPrH H * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (3 + 2 * C) := by
    have : (N : ℝ) ^ (3 + 2 * C) = N * (N * N ^ C * N ^ C) * N := by
      rw [show 3 + 2 * C = ((3 : ℕ) : ℝ) + C + C by push_cast; ring, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
      ring
    rw [this, Nat.cast_mul]
    refine mul_le_mul_of_nonneg_right (hr''.trans ?_) hN0.le
    gcongr
  rw [Real.rpow_mul hN0.le]
  exact hq.trans (hle.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by linarith)))

private noncomputable def relevel {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (q0 : ℕ) (h0 : Nat.Coprime q0 H.QS) : Host R :=
  { H with
    levelPrimes := {H.g 0, H.g 1, H.pde, H.pde', q0}
    g_level := by intro i; fin_cases i <;> simp
    pde_level := by simp
    level_coprimeS := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h | h <;> rw [h]
      · exact H.level_coprimeS _ (H.g_level 0)
      · exact H.level_coprimeS _ (H.g_level 1)
      · exact H.level_coprimeS _ H.pde_level.1
      · exact H.level_coprimeS _ H.pde_level.2
      · exact h0
    ccK_coprime := fun p _ => by rw [hc, Ideal.absNorm_top]; exact Nat.coprime_one_left p }

end UpperTheory.Top.PolynomialHostPrimeBound

open GlobalTheory.EX.DC UpperTheory.Top.PolynomialHostPrimeBound in
theorem UpperTheory.Top.hostQ :
    SmallPrimeOne → ∀ (la : ℝ) (G : FReq), HostExW la G.req → DC.HostExQW la G.req := by
  intro hS la G hH
  obtain ⟨A, hA, hS⟩ := hS
  intro eps he he'
  obtain ⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, hH⟩ := hH eps he he'
  have hC : C8 ≤ (3 + 2 * C8) * A := by nlinarith
  refine ⟨CT2, (3 + 2 * C8) * A, C5, c6, Cb, x0, h8.trans hC, h5, h6, hb, S, fun s hs hx hm => ?_⟩
  obtain ⟨R, H, q0, hR, hT, ⟨hv, har, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, -, -⟩, hG⟩ := hH s hs hx hm
  have hc : H.ccK = ⊤ := hv.2.2.2.2.2.2.1
  have h0 : Nat.Coprime (q0H H) H.QS := by
    have h1 : q0H H ≡ 1 [MOD H.QS * H.q * H.d] := by
      have := mod_cond H
      have h2 : 1 < H.QS * H.q * H.d := by
        by_contra h3
        have h4 : H.QS * H.q * H.d = 1 := by have := cond_pos H; omega
        rw [h4] at this
        omega
      unfold Nat.ModEq
      rw [this, Nat.mod_eq_of_lt h2]
    have h5 : Nat.Coprime (q0H H) (H.QS * H.q * H.d) := by
      rw [Nat.Coprime, h1.gcd_eq]
      simp
    exact Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) h5
  have hv' : HostVal s ((3 + 2 * C8) * A) (relevel H hc (q0H H) h0) := (hv.mono hC :)
  have hq := smallest_prime_polynomial_bound hA hS H hc hv.2.2.2.1.1 hv.2.2.2.1.2
  have har' : HostArith (relevel H hc (q0H H) h0) := by
    refine ⟨har.1, har.2.1, har.2.2.1, fun l hl => ?_⟩
    have hl' : l ∈ ({H.g 0, H.g 1, H.pde, H.pde', q0H H} : Finset ℕ) := hl
    show H.cls l = .splitK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with h | h | h | h | h <;> rw [h]
    · exact har.2.2.2 _ (H.g_level 0)
    · exact har.2.2.2 _ (H.g_level 1)
    · exact har.2.2.2 _ H.pde_level.1
    · exact har.2.2.2 _ H.pde_level.2
    · exact (GlobalTheory.HostSplit.split_of_one_mod R H _ (globalTwisting_spec_fact H).1 (mod_cond H)).2
  exact ⟨R, relevel H hc (q0H H) h0, q0H H, hR, hT, ⟨hv', har', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
    ⟨(globalTwisting_spec_fact H).1, mod_cond H, hq, q0H_ne_pde_and_ne_pde' H⟩, rfl⟩, globalTwisting_congr_fact _ rfl rfl rfl rfl rfl rfl, hG⟩
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

private theorem gk_nonneg {C : FC} (h : Std C) : C.GK.Nonneg := by
  obtain ⟨⟨f1, f2, f3, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, hm, hl⟩ := h
  have hm' : ∀ c ∈ C.cMid C.P.CF, 0 ≤ c := fun c hc => zero_le_one.trans (hm c hc)
  have hl' : ∀ c ∈ C.cLast, 0 ≤ c := fun c hc => zero_le_one.trans (hl c hc)
  refine ⟨hm' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_, hl' _ ?_,
    by rw [f2]; norm_num, by rw [f3]; norm_num, by rw [f1]; norm_num, hl' _ ?_⟩ <;> simp [FC.cMid, FC.cLast]

private theorem large_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
    fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
   ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
    fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

private theorem scale_ext {s s' : Scale} (h1 : s.x = s'.x) (h2 : s.eps = s'.eps) (h3 : s.J = s'.J) : s = s' := by
  cases s; cases s'; simp_all

theorem UpperTheory.Top.hostWW :
    ∀ (Q : PtProp) (la : ℝ) (P : HostReq), 1 < la → DC.HostExQW la P → DC.ObjC Q → DC.WClosed → DC.HostWW la P := by
  rintro Q la P hla hH ⟨ε0, hε0, hO⟩ ⟨ε1, hε1, hW⟩
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps he hle he52 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, xH, h8, h5, h6, hb, S, hH⟩ := hH eps he he52
  obtain ⟨K0, hO⟩ := hO eps C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) he52 h8
  obtain ⟨K1, hW⟩ := hW eps he (hle.trans (min_le_right _ _))
  refine ⟨CT2, C8, C5, c6, Cb, K0.sup K1, h8, h5, h6, hb, fun C hStd hCT2 hCp hL => ?_⟩
  obtain ⟨hL0, hL1⟩ := large_sup hL
  obtain ⟨c1, hO⟩ := hO C hStd hCp hL0
  obtain ⟨c1', hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hO⟩ := hO cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hN⟩ := hN cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hO⟩ := hO ch ((le_max_left _ _).trans hch)
  obtain ⟨xN, hN⟩ := hN ch ((le_max_right _ _).trans hch)
  have hmid := hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCF : (0 : ℝ) ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hCG : (0 : ℝ) ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xw, hw⟩ := exists_weights_in_windows eps C he he52 hStd
  obtain ⟨xc, hc⟩ := exists_injective_words eps C.CGam C.P.CF he he52 hCG hCF
  obtain ⟨x1, hx1, a1, a2, a3, a5, a6⟩ : ∃ x1 : ℝ, 1 < x1 ∧ xH ≤ x1 ∧ xO ≤ x1 ∧ xN ≤ x1 ∧ xw ≤ x1 ∧ xc ≤ x1 :=
    ⟨max 2 (max xH (max xO (max xN (max xw xc)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  let G : Scale → Prop := fun s => ∃ (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ),
    RankVal s R ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧ q0 = DC.q0H H ∧ (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) ∧
      WinOK s C.GK H a b ∧ WOK s cD ch C.GK H a b ∧ P C5 s R H q0
  let Q' : PtProp := fun D L _ Gx _ K _ _ _ => AuxBlock8.WeightVectorExists D L Gx K → G L.sc
  have hK : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → ∃ k : Kit C cD ch s, ∀ i, (k.pt i).Has Q' := by
    intro s hs hx hm
    obtain ⟨R, H, q0, hRV, hHT, hHG, hq, hP⟩ := hH s hs (a1.trans hx) hm
    obtain ⟨a, b, hab⟩ := hw s R H hs (a5.trans hx) hRV
    obtain ⟨c, hci, -⟩ := hc s R hs (a6.trans hx) hRV
    obtain ⟨k, hk⟩ := DC.kit_of_points Q C cD ch s R H a b _ c fun u0 hu =>
      hO s R H q0 a b _ c u0 hs (a2.trans hx) hRV (hHT.trans hCT2.symm) hHG hq hab rfl hci hu
    refine ⟨k, fun i hp => ?_⟩
    obtain ⟨⟨u0, hF⟩, hI, -⟩ := hk i
    obtain ⟨a', b', e1, e2, e3⟩ := weightWindowRequirement_host_of_point C cD ch (k.pt i) R H a b _ c u0 hStd (k.val i) hF hI hp
    rw [k.sc_eq i] at e2 e3 ⊢
    exact ⟨R, H, q0, a', b', hRV, hHT, hHG, hq, e1, e2, e3, hP⟩
  choose k hk using hK
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) := by
    intro s h h' h'' i
    refine (hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)).1
    · rw [(k s h h' h'').sc_eq i]; exact h
    · rw [(k s h h' h'').sc_eq i]; exact a3.trans h'
  obtain ⟨Fm, hFx, hPre, hOut, hMid, hLast, -, hQ, -, hJ, hWin, -⟩ :=
    exists_famP_of_kits eps C cD ch x1 la S he he52 hx1 hla.le hStd (gk_nonneg hStd) k hnum
  have hFL : Fm.Large K1 C.P.CF := by
    unfold FamP.Large
    rw [hPre, hOut, hMid, hLast]
    exact hL1
  obtain ⟨xW, hW⟩ := hW Fm C.P.CF trivial hFL
  refine ⟨max (Fm.x1 + 1) xW, S, fun s hs hx hm => ?_⟩
  have hx' : Fm.x1 < s.x := by have := (le_max_left _ _).trans hx; linarith
  obtain ⟨i⟩ := Fm.Ix_win s.x (by rw [hWin]; exact hm.2)
  have hG : G (Fm.L s.x i).sc := hQ Q' hk s.x hx' i (hW s.x ((le_max_right _ _).trans hx) i)
  have e : (Fm.L s.x i).sc = s :=
    scale_ext (Fm.L_x _ i hx') ((Fm.L_eps _ i).trans hs.symm) ((Fm.L_J _ i).trans (hJ.trans hm.1.symm))
  rw [e] at hG
  exact hG
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

open GlobalTheory.Fc

theorem kitS : ∀ (Q : Par → PtProp) (la : ℝ) (G : FReq), DC.HostWW la G.req → ObjCP Q →
    KitCPW la (fun κ => ((withDuty (Q κ)).and DC.WallPt).and G.pt) := by
  intro Q la G hHost hObj
  obtain ⟨εH, hεH, hHost⟩ := hHost
  obtain ⟨εO, hεO, hObj⟩ := hObj
  refine ⟨min εH εO, lt_min hεH hεO, fun eps he he0 he1 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, KW, h8, h5, h6, hb, hHost⟩ := hHost eps he (he0.trans (min_le_left _ _)) he1
  obtain ⟨KO, hObj⟩ := hObj eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he1 h8
  refine ⟨CT2, C8, C5, c6, Cb, KW.sup KO, h8, h5, h6, hb, fun C hC hT hP hL => ?_⟩
  obtain ⟨hLW, hLO⟩ := fc_large_of_sup hL
  obtain ⟨c1, hObj⟩ := hObj C hC hP hLO
  obtain ⟨c1', hHost⟩ := hHost C hC hT hP hLW
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hObj⟩ := hObj cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hHost⟩ := hHost cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hObj⟩ := hObj ch ((le_max_left _ _).trans hch)
  obtain ⟨xH, S, hHost⟩ := hHost ch ((le_max_right _ _).trans hch)
  have hmid := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hG : 0 ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hF : 0 ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xC, hCode⟩ := exists_injective_words eps C.CGam C.P.CF he he1 hG hF
  obtain ⟨xq, hq⟩ := small_prime_lt eps C8 he h8
  refine ⟨max (max xH xO) (max xC xq), S, fun s hs hx hmem => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxH, hxO⟩, hxC, hxq⟩ := hx
  obtain ⟨R, H, q0, a, b, hRV, hHT, hH, hqH, h0, hWin, hW, hGq⟩ := hHost s hs hxH hmem
  obtain ⟨c, hc, -⟩ := hCode s R hs hxC hRV
  have hHT' : H.CT2 = C.CT2 := hHT.trans hT.symm
  have hn : 0 < R.n := R.toFrame.ord_pos
  have hq0 : (q0 : ℝ) < s.X' := by
    have hqp : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    have hn' : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    exact hq s _ q0 hs hxq (by positivity) hH.1.log_cond_le hH.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  choose pt hsc hval har hfrom hcan hhas using
    fun i : Fin R.n => hObj s R H q0 a b _ c i.1 hs hxO hRV hHT' (by show HostGood s C.P.Cpde C5 c6 Cb H q0; rw [hP]; exact hH) hqH hWin rfl hc i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ?_⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩
  · have hd := DC.has_withDuty_wall_and_choices (C8 := C8) (c6 := c6) (q0 := q0) (pt i) hC hHT' (by rw [hsc i]; exact hH)
      (by rw [hsc i]; exact hq0) h0 (by rw [hsc i]; exact hW) (hval i) (hfrom i) (hcan i) (hhas i)
    exact ⟨⟨hd.1, G.at_of_from (hfrom i) (by rw [hsc i]; exact hGq)⟩, hd.2⟩

end UpperTheory.Top
end

section
noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.DC GlobalTheory.Fc NumberField

theorem designS : ∀ (Q : Par → PtProp) (cT : ℝ → ℝ → ℝ) (la : ℝ) (G : FReq), 1 < la → DC.MinkDiv →
    KitCPW la (fun κ => ((withDuty (DC.withObj (Q κ))).and DC.WallPt).and G.pt) →
    DC.DesignChoices (DC.WithTw fun Fm => (∃ κ : Par, Link κ Fm ∧ DC.cls (Q κ) Fm) ∧ G.cls la Fm) 3 cT := by
  rintro Q cT la G hla hM ⟨ε0, hε0, hK⟩
  refine ⟨min ε0 (1 / 53), lt_min hε0 (by norm_num), fun eps he hle K => ?_⟩
  have he52 : eps < 1 / 52 := lt_of_le_of_lt (hle.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨CT2, C8, C5, c6, Cb, K0, hC8, hC5, hc6, hCb, hK⟩ := hK eps he (hle.trans (min_le_left _ _)) he52
  obtain ⟨C, hStd, hCT2, hCp, hLK, hLK0, hGK⟩ := exists_std_large (thrTu K (cT eps 9)) K0 CT2 C8 hC8
  obtain ⟨c1, hK⟩ := hK C hStd hCT2 hCp hLK0
  obtain ⟨c1', hN⟩ := szRow_numAt eps he he52 C hStd
  obtain ⟨c2, hK⟩ := hK (max c1 c1') (le_max_left _ _)
  obtain ⟨c2', hN⟩ := hN (max c1 c1') (le_max_right _ _)
  obtain ⟨x0, S, hK⟩ := hK (max c2 c2') (le_max_left _ _)
  obtain ⟨x0', hN⟩ := hN (max c2 c2') (le_max_right _ _)
  have hx1 : (1 : ℝ) < max 2 (max x0 x0') := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  have hK' : ∀ s : Scale, s.eps = eps → max 2 (max x0 x0') ≤ s.x → S.Mem s →
      ∃ k : Kit C (max c1 c1') (max c2 c2') s, ∀ i, (k.pt i).Has (((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt).and G.pt) ∧
        ThickSetLowerBound (k.pt i).L ∧ ChBad_at (k.pt i).ta.Gx Cb ∧ ChQD_at (k.pt i).D (k.pt i).L.sc.x (k.pt i).L.sc.eps C5 :=
    fun s hs hx hm => hK s hs (((le_max_left _ _).trans (le_max_right _ _)).trans hx) hm
  choose k hk using hK'
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) ∧ ChTT_at ((k s h h' h'').pt i).L ∧
      ChCode_at ((k s h h' h'').pt i).L 3 C.P.CF := by
    intro s h h' h'' i
    refine hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)
    · rw [(k s h h' h'').sc_eq i]; exact h
    · rw [(k s h h' h'').sc_eq i]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans h'
  obtain ⟨Fm, hFx, hPre, hOut, hMid, hLast, hTu, hQ, hR, -, hWn, -⟩ :=
    exists_famP_of_kits eps C _ _ _ la S he he52 hx1 hla.le hStd hGK k (fun s h h' h'' i => (hnum s h h' h'' i).1)
  replace hOut : Fm.cOut = C.cOut := hOut
  have hall := hR (fun D L Gx => (ThickSetLowerBound L ∧ ChBad_at Gx Cb ∧ ChQD_at D L.sc.x L.sc.eps C5) ∧
      (Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) ∧
      Fintype.card D.what₂.Word = ⌈3 * GamL L ^ 2 * L.sc.x ^ C.P.CF⌉₊)
    (fun s h h' h'' i => ⟨(hk s h h' h'' i).2, hnum s h h' h'' i, ((k s h h' h'').val i).words⟩)
  have hCF : (1 : ℝ) ≤ C.P.CF := hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hc := hQ ((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt) (fun s h h' h'' i => (hk s h h' h'' i).1.1)
  have hGc : G.cls la Fm := ⟨fun y => by
      obtain ⟨Y, a, b⟩ := S.windows y
      exact ⟨Y, a, fun x c d => hWn ▸ b x c d⟩,
    hQ G.pt (fun s h h' h'' i => (hk s h h' h'' i).1.2)⟩
  obtain ⟨hFix, hWin⟩ := fix_and_win_of_numAt eps C Fm hStd hOut (fun x i => (hall x i).2.1.1)
  have hCYL : Fm.CYL = 9 := hFix.2.2.2.2.2.2.2.1
  have hlt : ∀ x, x ≥ Fm.x1 + 1 → Fm.x1 < x := fun x hx => by linarith
  have hLarge : Fm.Large (thrTu K (cT eps 9)) C.P.CF := by
    unfold FamP.Large
    rw [hPre, hOut, hMid, hLast]
    exact hLK
  have hTw : TwGood Fm := classOf_twPt Fm fun x hx i => (hc x hx i).1.1.2.2.2
  have hQD : ChosenQD Fm C5 := by
    refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have := (hall x i).1.2.2
    rwa [Fm.L_x x i (hlt x hx), Fm.L_eps x i] at this
  have hreq := classOf_reqPt Fm fun x hx i => ⟨(hc x hx i).2, (hc x hx i).1.2.2.1, (hc x hx i).1.2.2.2.1⟩
  have hDG : DGamDvdF Fm := ⟨Fm.x1 + 1, fun x hx i u => (hc x (hlt x hx) i).1.1.2.2.1 _ (hM _) u⟩
  have hTame : TameDistinctF Fm := ⟨Fm.x1 + 1, fun x hx i => (hc x (hlt x hx) i).1.1.2.1⟩
  have hCFeq : Fm.CF = C.P.CF := by
    have := congrArg (fun f : ℝ → List ℝ => (f 0).getD 9 0) hMid
    simpa [FamP.cMid, FC.cMid] using this
  have hUp : CodeUpF Fm 3 C.P.CF := by
    refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h := (hall x i).2.2
    rw [Fm.L_x x i (hlt x hx)] at h
    have hx0 : (0 : ℝ) ≤ x := by have := Fm.one_lt_family_threshold; linarith
    rw [h]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hT2 : ThickSetEventually Fm := ⟨0, fun x _ i => (hall x i).1.1⟩
  have hTT : ChosenTT Fm := ⟨0, fun x _ i => (hall x i).2.1.2.1⟩
  have hBad : ChosenBad Fm Cb := ⟨0, fun x _ i => (hall x i).1.2.1⟩
  have hCode : ChosenCode Fm 3 C.P.CF := ⟨0, fun x _ i => (hall x i).2.1.2.2⟩
  have hLink : Link ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩ (setTu Fm (cT eps 9)) := by
    refine ⟨rfl, ⟨hC5, hc6, hCb⟩, hStd, hPre, ?_, hMid, hLast⟩
    show (setTu Fm C.CTu).cOut = _
    rw [← hTu]
    exact hOut
  refine ⟨setTu Fm (cT eps 9), C.P.CF, C5, Cb, ⟨⟨⟨_, hLink, (setTu_cls _ Fm _).2 ⟨hc, hFix, hWin⟩⟩, hGc⟩, hTw⟩, zero_le_one.trans hCF,
    (setTu_large Fm K _ _).2 hLarge, hC5, hCb, hT2, hTT, hBad, hQD, hCode, hreq.2.1, hreq.2.2, hDG, ?_, hTame, hCFeq, hUp,
    hCYL.le⟩
  show cT eps Fm.CYL ≤ cT eps 9
  rw [hCYL]

end UpperTheory.Top

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

theorem objC_true {Q : Par → PtProp} (h : ObjCP Q) : DC.ObjC (fun _ _ _ _ _ _ _ _ _ => True) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  refine ⟨x0, fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  obtain ⟨p, e1, e2, e3, e4, e5, -⟩ := h s R H q0 a b M c u0 d1 d2 d3 d4 (by rw [← b2] at d5; exact d5) d0 d6 d7 d8 d9
  exact ⟨p, e1, e2, e3, e4, e5, trivial⟩

theorem recS (QO : Par → ∀ D : D7, Obj D → Prop) (cT : ℝ → ℝ → ℝ) (hR : DC.MinkDiv → RecExP (fun κ => DQ.withQD (QO κ)))
    (hM : DC.MinkDiv) : ExD (clsP QO) cT := by
  intro la G hla hH
  have hS : SmallPrimeOne := GlobalTheory.EX.smallPrimeOne_of_primesRel GlobalTheory.Lin.primesRel_holds
  have hO := GlobalTheory.T.existsObjects_of_admissibleTwistDatum _ GlobalTheory.EX.normPrimes_and_levelPrime_unconditional.2 (hR hM)
  have hW : DC.HostWW la G.req := hostWW _ la _ hla (hostQ hS la G hH) (objC_true hO) GlobalTheory.T.windowShareRequirementClosedForm_proof
  exact designS (fun κ => ptO (DQ.withQD (QO κ))) cT la G hla hM (kitS _ la G hW hO)

end UpperTheory.Top
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

theorem classSel : StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Bd : BdT) (Lk : LkT Bd) (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧ GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') → ExBL KP Q Q' Lk → RowL KP Q Q' Lk H → ∃ (𝒜 : FamClass) (σ : RawSel Bd 𝒜), (DC.MinkDiv → ExD 𝒜 cT) ∧ (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → DQ.Duty7 Fm ∧ DQ.MtStableF Fm) ∧ IsSel Q' Lk (fun _ _ _ _ _ => True) 𝒜 σ ∧ H 𝒜 σ := by
  intro h1 h2 KP Q Q' Bd Lk H cT hc hx hr
  obtain ⟨R, r, hx', hr'⟩ := RowL.elim hx hr
  obtain ⟨E, hE, hH⟩ := Row.elim hx' hr'
  have hs : IsSel (sAnd Q' R) Lk (fun _ _ _ _ _ => True) (cls (sAnd Q' R) Lk E) (pick (sAnd Q' R) Lk E) :=
    IsSel.mono (fun _ _ _ _ _ _ => trivial) (pick_isSel (sAnd Q' R) Lk E)
  refine ⟨cls (sAnd Q' R) Lk E, pick (sAnd Q' R) Lk E, ?_, fun _ _ h => sevenDuties_of_class h,
    @isSel_of_sAnd Bd Q' R Lk _ (cls (sAnd Q' R) Lk E) (pick (sAnd Q' R) Lk E) hs, hH⟩
  refine recS (QOf (sAnd Q' R) Lk E) cT fun hm => ?_
  obtain ⟨a, b, c, d⟩ := hc hm
  have d' := GlobalTheory.T.secondG_sAnd_of_largeBase KP Q Q' R a (evG_of_ev r) d
  have h := memberTop_final_contextParameters h1 h2 KP Q (sAnd Q' R) (QOf (sAnd Q' R) Lk E) a b c d' hE
  have e : ∀ κ : Par, (fun D O => κ.Pos → QOf (sAnd Q' R) Lk E κ D O) = QOf (sAnd Q' R) Lk E κ :=
    fun κ => funext fun _ => funext fun _ => propext ⟨fun h' h0 => h' h0 h0, fun h' _ => h'⟩
  simpa only [e] using h

end UpperTheory.Top
end
