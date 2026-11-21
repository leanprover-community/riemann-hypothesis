import Mathlib
import Formalism.SharpRestriction.Divisibility.FlipOneTwo
import Formalism.DegreeFormula.PointDegree.FlagDeg
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.GelfandTransference.HadamardGelfand.Transference

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions

structure JetSit (D : D7) (P : ModuliIntegralCharts.Prov D) (l q DF : ℕ) where
  w : P.Dat
  y : (P.loc w l).Pt (P.loc w l).Xm
  nW : ℕ
  hq : ModuliIntegralCharts.NHyp D l q
  hDF : 3 * DF + 2 ≤ q
  sg : (P.loc w l).At y ((P.loc w l).latStd nW) q → (P.loc w l).Th y ((P.loc w l).latStd nW) q
  hsg : (P.loc w l).SymLift y ((P.loc w l).latStd nW) q sg
  ev : (P.loc w l).Jet y ((P.loc w l).latStd nW) q DF →ₗ[((P.loc w l).fld y).C] ((P.loc w l).fld y).C

namespace JetSit

variable {D : D7} {P : ModuliIntegralCharts.Prov D} {l q DF : ℕ} (S : JetSit D P l q DF)

def thetaNorms : Set ℝ :=
  Set.range fun x => ‖S.ev ((P.loc S.w l).jet S.y ((P.loc S.w l).latStd S.nW) q DF
    ((P.loc S.w l).act S.y ((P.loc S.w l).latStd S.nW) q (S.sg x)
      ((P.loc S.w l).vth S.y ((P.loc S.w l).latStd S.nW) q)))‖

def germNorms : Set ℝ :=
  (fun v => ‖S.ev v‖) '' ((P.loc S.w l).intJet S.y ((P.loc S.w l).latStd S.nW) q DF : Set _)

theorem depth_le (hl : l.Prime) (h : ModuliIntegralCharts.LinkConditions D P) (a b : ℝ)
    (ha : IsLUB S.thetaNorms ((l : ℝ) ^ (-a))) (hb : IsLUB S.germNorms ((l : ℝ) ^ (-b))) :
    a ≤ b + (P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y := by
  obtain ⟨_, H⟩ := h S.w l hl q DF S.nW S.hq S.hDF S.y
  obtain ⟨t, ht, hv⟩ := H S.sg S.hsg
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos hl0 _) ht
  have key : ∀ u ∈ ModuliIntegralCharts.Ospan (C := ((P.loc S.w l).fld S.y).C)
      ((P.loc S.w l).secJet S.y ((P.loc S.w l).latStd S.nW) q DF S.sg), ‖S.ev u‖ ≤ (l : ℝ) ^ (-a) := by
    intro u hu
    unfold ModuliIntegralCharts.Ospan at hu
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨α, hα, s, ⟨x, rfl⟩, rfl⟩ := hu
      rw [map_smul, smul_eq_mul, norm_mul]
      calc _ ≤ 1 * (l : ℝ) ^ (-a) := mul_le_mul hα (ha.1 ⟨x, rfl⟩) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    | zero => rw [map_zero, norm_zero]; exact (Real.rpow_pos_of_pos hl0 _).le
    | add u v _ _ hu hv =>
      rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
    | neg u _ hu => rwa [map_neg, norm_neg]
  have ub : (l : ℝ) ^ (-b) ≤ (l : ℝ) ^ (-a) / ‖t‖ := hb.2 (by
    rintro _ ⟨v, hv', rfl⟩
    rw [le_div_iff₀ htpos]
    have := key _ (hv v hv')
    rwa [map_smul, smul_eq_mul, norm_mul, mul_comm] at this)
  have h2 : (l : ℝ) ^ (-b) ≤
      (l : ℝ) ^ (-a + (P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y) := by
    refine ub.trans ?_
    rw [div_le_iff₀ htpos, Real.rpow_add hl0, mul_assoc]
    have h3 : 1 ≤ (l : ℝ) ^ ((P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y) * ‖t‖ := by
      calc (1 : ℝ) = (l : ℝ) ^ ((P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y) *
            (l : ℝ) ^ (-((P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y)) := by
              rw [← Real.rpow_add hl0]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left ht (Real.rpow_pos_of_pos hl0 _).le
    calc (l : ℝ) ^ (-a) = (l : ℝ) ^ (-a) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.rpow_pos_of_pos hl0 _).le
  have h4 := (Real.rpow_le_rpow_left_iff hl1).1 h2
  linarith

end JetSit

theorem phiCy_nonneg {D : D7} {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) :
    0 ≤ L.phiCy y := by
  unfold ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC
  apply Real.sInf_nonneg
  rintro x ⟨l, _, hpos, rfl⟩
  by_cases h0 : L.beS y = 0
  · rw [h0, map_zero]
  · refine (hpos _ (fun a => ?_) h0).le
    by_cases ha : a = 0
    · subst ha; simp
    · exact (L.be_pos y a ha).le

theorem one_le_absDiscr (D : D7) : (1 : ℝ) ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| := by
  have h : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs (NumberField.discr_ne_zero _)
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h
  simpa using h2

theorem one_le_rdE (D : D7) : 1 ≤ D.host.rdE := by
  unfold Host.rdE
  exact Real.one_le_rpow (one_le_absDiscr D) (by positivity)


section A5

variable {D : D7} (L : SizeData₂ D) {V : DivX D} {Lc : placeRankTwoOne.Loc D V} (X : sizeConstantAtParamsWeight.Loc D V Lc)

structure TieJet (P : ModuliIntegralCharts.Prov D) where
  sit : ∀ s : X.ThF, (X.thF s).l.Prime → Nat.Coprime (X.thF s).l (X.thF s).q →
    JetSit D P (X.thF s).l (X.thF s).q (X.thF s).DF
  phic_eq : ∀ s h1 h2, (X.thF s).phic = (P.loc (sit s h1 h2).w (X.thF s).l).phiCy (sit s h1 h2).y
  theta_def : ∀ s h1 h2, IsLUB (sit s h1 h2).thetaNorms (((X.thF s).l : ℝ) ^ (-(X.thF s).minVTheta))
  nuLoc_def : ∀ s h1 h2, IsLUB (sit s h1 h2).germNorms (((X.thF s).l : ℝ) ^ (-(X.thF s).nuLoc))
  rk_le : ∀ s h1 h2, (P.loc (sit s h1 h2).w (X.thF s).l).dP (sit s h1 h2).y ≤ 2 * D.R.f * D.R.r

def FieldSizeClauses (CP AP Crr : ℝ) : Prop :=
  (∀ s : X.ThF, (X.thF s).l.Prime → 0 < (X.thF s).q →
    (X.thF s).lamQ ^ 2 ≤ sizeConstantAtParamsWeight.RR D Crr * sizeConstantAtParamsWeight.PP D L CP AP * (X.thF s).phic ∧
    ((X.thF s).r1.Prime → (X.thF s).r1 ≠ 2 → jacobiSym (-(D.host.d : ℤ)) (X.thF s).r1 = 1 →
      Nat.Coprime (X.thF s).r1 (X.thF s).q → ((X.thF s).r1 : ℝ) ≤ L.sc.L →
      ((X.thF s).r1 : ℝ) ^ (-(4 : ℤ)) * (X.thF s).phic -
        (if (X.thF s).l = (X.thF s).r1 then sizeConstantAtParamsWeight.PP D L CP AP else 0) ≤ (X.thF s).vTau)) ∧
  (∀ s : X.ThA, 0 < (X.thA s).q → sizeConstantAtParamsWeight.QNorm D (X.thA s).q → sizeConstantAtParamsWeight.TheoremI2Hypotheses D L CP AP Crr (X.thA s).q (X.thA s).DF →
    -(sizeConstantAtParamsWeight.PP D L CP AP * (X.thA s).DF) -
        sizeConstantAtParamsWeight.RR D Crr * sizeConstantAtParamsWeight.PP D L CP AP * ((X.thA s).DF : ℝ) ^ 2 / ((X.thA s).q : ℝ) * (X.thA s).phic
      ≤ (X.thA s).logThetaMax ∧
    ((X.thA s).r1.Prime → (X.thA s).r1 ≠ 2 → jacobiSym (-(D.host.d : ℤ)) (X.thA s).r1 = 1 →
      Nat.Coprime (X.thA s).r1 (X.thA s).q → ((X.thA s).r1 : ℝ) ≤ L.sc.L →
      ((X.thA s).r1 : ℝ) ^ (-(4 : ℤ)) * (X.thA s).phic - sizeConstantAtParamsWeight.PP D L CP AP ≤ (X.thA s).cuspVal))




end A5

section A5F

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Y : sizeConstantAtParamsWeight.LocF Fm)


end A5F

section A5ab

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Y : sizeConstantAtParamsWeight.LocF Fm)
  (XF : IntegralModelsLocalData.ProvF Fm) (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (XF x hx i).P))

def BoundaryLocalHypothesesAlongFamily : Prop :=
  ∀ x hx (i : Fm.Ix x), BoundaryLocalData.adm3 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.ArchimedeanSignatureMatching (Fm.D x i) (XF x hx i).P (YF x hx i) ∧ BoundaryLocalData.adm5 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.adm6 (Fm.D x i) (XF x hx i).P ∧ BoundaryLocalData.adm7 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.adm8 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧ BoundaryLocalData.adm9 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.adm10 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧ BoundaryLocalData.adm11 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.adm12 (Fm.D x i) (XF x hx i).P (YF x hx i)




end A5ab


theorem two_le_rdE (D : D7) (_hq : 2 ≤ D.host.q) (_hd : 2 ≤ D.host.d) : 2 ≤ D.host.rdE := by
  have h0 := D.host.der.rd_sq_ge
  have h1 : (1 : ℝ) ≤ D.R.ord := by exact_mod_cast D.R.ord_pos
  have h2 : (0 : ℝ) ≤ D.host.rd := Real.rpow_nonneg (abs_nonneg _) _
  show 2 ≤ D.host.rd
  nlinarith

theorem two_le_of_log_pos (n : ℕ) (h : 0 < Real.log (n : ℝ)) : 2 ≤ n := by
  by_contra hn
  have h1 : n = 0 ∨ n = 1 := by omega
  rcases h1 with rfl | rfl <;> simp at h


section SizesF

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def CsFn (l : List ℝ) : ℝ := max (l.getD 6 0 + 1) (max (l.getD 13 0) (max (l.getD 1 0) 0))




end SizesF


section ParF

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)



end ParF





section L3F

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)



end L3F




theorem log_rdE_le_L (D : D7) (L : SizeData₂ D) (hCond : Formalism.MainNotions.SizeCond L) (hQD : Formalism.MainNotions.SizeQD L) :
    Real.log D.host.rdE ≤ L.sc.L := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hq2 : 2 ≤ D.host.q := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 : 2 ≤ D.host.d := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
  have hrd2 := two_le_rdE D hq2 hd2
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hc : D.host.rdE ≤ Formalism.MainNotions.szCond L := by
    refine hQD.2.2.2.2.2.2.2.trans ?_
    unfold Formalism.MainNotions.szCond
    have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hs (by positivity)
    have h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
    nlinarith
  have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by linarith
  have h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
  have h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (hCond.trans hsb)))
  have := Real.log_le_log (by linarith) hfin
  rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this






end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions

theorem bprime_le_half (D : D7) (L : SizeData₂ D) (hEta : Formalism.MainNotions.SizeEta L) (hlx : 2 ≤ Real.log L.sc.x) :
    2 * L.sc.b' ≤ L.sc.b := by
  have h := hEta.2.2.2.2.2.2.2.2
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hxe : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have hb' : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hd0 := L.thickDensity_pos
  have hd1 := L.thickDensity_le_one
  have hS0 := L.Sc_pos
  unfold Formalism.MainNotions.szlA at h
  have hmd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos (by linarith) hd0
  rw [← mul_div_assoc, div_le_iff₀ hmd] at h

  have l1 : (D.R.m : ℝ) * L.sc.b' ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) :=
    mul_le_mul hmr (by linarith) hb' (by linarith)
  have l2 : (D.R.m : ℝ) * L.sc.b' * 2 ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x :=
    mul_le_mul l1 hlx (by norm_num) (by positivity)
  have l3 : (D.R.m : ℝ) * 1 ≤ (D.R.k : ℝ) * L.sc.x ^ L.sc.eps := mul_le_mul hmk hxe (by norm_num) (by linarith)
  have l4 : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) ≤
      (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * ((D.R.k : ℝ) * L.sc.x ^ L.sc.eps) :=
    mul_le_mul l2 l3 (by positivity) (by positivity)

  have u1 : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) ≤ (D.R.m : ℝ) * D.R.m * L.sc.b := by
    have e : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) = (L.de2 * L.de2) * ((D.R.m : ℝ) * D.R.m * L.sc.b) := by
      ring
    rw [e]
    have : L.de2 * L.de2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_left (by positivity) this
  have fin : (D.R.m : ℝ) * D.R.m * (2 * L.sc.b') ≤ (D.R.m : ℝ) * D.R.m * L.sc.b := by
    have e : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) = (D.R.m : ℝ) * D.R.m * (2 * L.sc.b') := by ring
    linarith
  exact le_of_mul_le_mul_left fin (by positivity)




def sgR (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ℝ := ((DV.sigPar D τ i : ℚ) : ℝ)

theorem sigPar_low (D : D7) (τ : D.what₂.Tau) (a : ℕ) :
    DV.sigPar D τ (D.R.k - 1 + a) = -(if h : a < D.R.m then (D.hc τ).b ⟨a, h⟩ else 0) := by
  unfold DV.sigPar
  rw [dif_neg (by omega)]
  simp only [Nat.add_sub_cancel_left]
  split_ifs <;> simp

theorem sgR_cloud (D : D7) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k - 1) :
    sgR D τ i = (((D.hc τ).v ⟨i, h⟩ : ℚ) : ℝ) := by
  unfold sgR DV.sigPar
  rw [dif_pos h]

theorem sgR_low (D : D7) (τ : D.what₂.Tau) (a : ℕ) (h : a < D.R.m) :
    sgR D τ (D.R.k - 1 + a) = -(((D.hc τ).b ⟨a, h⟩ : ℚ) : ℝ) := by
  unfold sgR
  rw [sigPar_low, dif_pos h]
  push_cast
  rfl

theorem steps_sum (s : ℕ → ℝ) (lo r : ℕ) (G : ℝ) (hs : ∀ i, lo ≤ i → i + 1 < r → G ≤ s i - s (i + 1)) (i : ℕ) (hi : lo ≤ i) :
    ∀ l, i ≤ l → l < r → ((l : ℝ) - i) * G ≤ s i - s l := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => intro _; simp
  | succ l hl ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hs l (by omega) h
    push_cast
    linarith

theorem sgR_step (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (τ : D.what₂.Tau) (G : ℝ)
    (h1 : G ≤ 4 * ((D.s.Del : ℚ) : ℝ)) (h2 : G ≤ LevelStarExponents.h0 L)
    (h3 : ∀ hm : 0 < D.R.m, G ≤ (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) (i : ℕ) (hi : i + 1 < D.R.r) :
    G ≤ sgR D τ i - sgR D τ (i + 1) := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  rcases Nat.lt_trichotomy (i + 1) (D.R.k - 1) with h | h | h
  · rw [sgR_cloud D τ i (by omega), sgR_cloud D τ (i + 1) h]
    have e := D.s.cloud_gap D.u₀ τ i h
    rw [D.hcW_base] at e
    have e' := congrArg (fun q : ℚ => (q : ℝ)) e
    simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at e'
    rw [e']
    exact h1
  · have e0 : i + 1 = D.R.k - 1 + 0 := by omega
    rw [sgR_cloud D τ i (by omega), e0, sgR_low D τ 0 (by omega)]
    have := (L.cloud_v τ ⟨i, by omega⟩).1
    have := h3 (by omega)
    linarith
  · obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
    subst ha
    rw [sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]
    have := (P.nodes_gap τ a (by omega)).1
    push_cast at this
    linarith






theorem sgR_step_low (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (τ : D.what₂.Tau) (i : ℕ) (hlo : D.R.k - 1 ≤ i)
    (hi : i + 1 < D.R.r) : LevelStarExponents.h0 L ≤ sgR D τ i - sgR D τ (i + 1) := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
  subst ha
  rw [sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]
  have := (P.nodes_gap τ a (by omega)).1
  push_cast at this
  linarith

theorem r_cast (R : Ranks) : (R.r : ℝ) = (R.k : ℝ) + R.m - 1 := by
  have h : 1 ≤ R.k + R.m := by have := R.two_le_m; omega
  unfold Ranks.r
  push_cast [Nat.cast_sub h]
  ring

theorem wSz_eq (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    DV.wSz D j τ = (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
  unfold DV.wSz
  rw [dif_pos ⟨h1, h2⟩]


theorem minimalGap_le_first_lowerRowParameter (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (hw : L.sc.w'' D.R.n ≤ DV.wSz D j τ) (hm : 0 < D.R.m) : LevelStarExponents.h0 L ≤ (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
  have hb := abs_le.1 (L.be_close τ ⟨0, hm⟩ ⟨j - 1, by omega⟩)
  rw [wSz_eq D j h1 h2 τ] at hw
  push_cast at hb
  have he := L.etaSz_pos
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have h3 : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    refine mul_le_mul_of_nonneg_right ?_ he.le
    nlinarith
  have h4 := P.mteta
  have h5 : LevelStarExponents.h0 L ≤ L.etaSz := by
    unfold LevelStarExponents.h0
    exact div_le_self he.le (by linarith)
  linarith [hb.1]

theorem sgR_be (D : D7) (L : SizeData₂ D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (i : ℕ)
    (hlo : D.R.k - 1 ≤ i) (hi : i < D.R.r) : |sgR D τ i + DV.wSz D j τ| ≤ L.etaSz := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
  subst ha
  rw [sgR_low D τ a (by omega), wSz_eq D j h1 h2 τ]
  have hb := L.be_close τ ⟨a, by omega⟩ ⟨j - 1, by omega⟩
  push_cast at hb
  rw [← abs_neg]
  convert hb using 2
  ring

theorem TT_le_TO (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) (CP AP : ℝ)
    (h0 : 0 ≤ placeRankTwoOne.PP D L CP AP) (hPP : placeRankTwoOne.PP D L CP AP ≤ T.PP) :
    0 ≤ placeRankTwoOne.TT D L CP AP ∧ placeRankTwoOne.TT D L CP AP ≤ (T.TO : ℝ) := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hDe : (placeRankTwoOne.dimY D : ℝ) = (T.Dp : ℝ) := by
    have : placeRankTwoOne.dimY D = T.Dp := by rw [T.Dp_eq]; rfl
    exact_mod_cast this
  have hD1 : (1 : ℝ) ≤ (T.Dp : ℝ) := by
    have : 1 ≤ T.Dp := by
      rw [T.Dp_eq]
      have h1 : 0 < D.R.r.choose 2 := Nat.choose_pos hr2
      have h2 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
      exact Nat.mul_pos h2 h1
    exact_mod_cast this
  have hZ1 : (1 : ℝ) ≤ zBase L := by
    unfold zBase
    have : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  have hP1 : 1 ≤ T.PP := by
    rw [T.PP_eq]
    have h1 := Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)
    have h2 := T.one_le_CP
    nlinarith
  set p : ℝ := placeRankTwoOne.PP D L CP AP with hp
  have hxCp : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow hx1.le T.Cp_nonneg
  have hTTr : placeRankTwoOne.PP D L CP AP ^ 2 * (placeRankTwoOne.dimY D : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) =
      p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by rw [hDe]
  refine ⟨placeRankTwoOne.TT_nonneg D L CP AP, placeRankTwoOne.TT_le_nat D L CP AP T.TO ?_⟩
  refine le_trans ?_ T.TO_ge
  rw [hTTr]
  have a1 : p ^ 2 ≤ T.PP ^ 4 :=
    (pow_le_pow_left₀ h0 hPP 2).trans (pow_le_pow_right₀ hP1 (by norm_num))
  have a2 : (T.Dp : ℝ) ^ 2 ≤ (T.Dp : ℝ) ^ 3 := pow_le_pow_right₀ hD1 (by norm_num)
  have a3 : p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k := by gcongr
  have a4 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f :=
    le_mul_of_one_le_right (by positivity) hf1
  have a5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤
      T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp :=
    le_mul_of_one_le_right (by positivity) hxCp
  have hd : (D.R.m : ℝ) * L.de2 ≤ D.R.m := by
    have := L.thickDensity_le_one; nlinarith
  exact div_le_div₀ (by positivity) (a3.trans (a4.trans a5)) (mul_pos (by linarith) L.thickDensity_pos) hd

theorem Gc_le (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) (CP AP : ℝ)
    (h0 : 0 ≤ placeRankTwoOne.PP D L CP AP) (hPP : placeRankTwoOne.PP D L CP AP ≤ T.PP) :
    placeRankTwoOne.Gc D L CP AP + 1 ≤ 4 * ((D.s.Del : ℚ) : ℝ) ∧ placeRankTwoOne.Gc D L CP AP + 1 ≤ LevelStarExponents.h0 L := by
  obtain ⟨hT0, hTO⟩ := TT_le_TO D L P T CP AP h0 hPP
  have hDe : (placeRankTwoOne.dimY D : ℝ) = (T.Dp : ℝ) := by
    have : placeRankTwoOne.dimY D = T.Dp := by rw [T.Dp_eq]; rfl
    exact_mod_cast this
  have hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have h1 : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (T.Dp : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  unfold placeRankTwoOne.Gc
  rw [hDe]
  generalize placeRankTwoOne.TT D L CP AP = tt at hT0 hTO
  constructor
  · have g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        ((T.TO : ℝ) + T.Dp + 2) * ((T.TO : ℝ) + T.Dp + 2 + 2 * (D.R.N D.R.m : ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have g2 := T.Del_gap
    have g3 : (1 : ℝ) ≤ (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) := by nlinarith
    linarith
  · have q1 : 40 * ((T.Dp : ℝ) + 2) ≤ (T.TO : ℝ) := by exact_mod_cast T.TO_40
    have q2 : 2 * (D.R.r : ℝ) ≤ (T.TO : ℝ) := by
      exact_mod_cast le_trans (Nat.le_add_left _ _) T.TO_nW
    have g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        (41 / 40 * (T.TO : ℝ)) * (81 / 40 * (T.TO : ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have q3 : (80 : ℝ) ≤ (T.TO : ℝ) := by linarith
    have q4 := T.heightBound_ge_order_sq
    nlinarith

section Clauses

variable (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hK : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)

include P hK h1 h2







end Clauses


theorem one_le_nWn (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) : 1 ≤ T.nWn := by
  refine le_trans ?_ T.nW_lo.1
  have hf : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
  have hr : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact Nat.mul_pos (Nat.mul_pos hf hr) (Nat.succ_pos _)






end Formalism.MainNotions.DIV

end
