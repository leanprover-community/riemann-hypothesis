import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted

section
open NumberField GlobalTheory.AllWt

namespace GlobalTheory.CutNum

open Module Formalism.HermitianLatticesTheory

section Maj

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)

theorem fcoord_add' (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem fcoord_smul' (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem normAt_add_sq (x y : V) :
    normAt b X v (x + y) ^ 2 = normAt b X v x ^ 2 + normAt b X v y ^ 2 + 2 * (majAt b X v x y).re := by
  simp only [normAt, cnorm, majAt, fcoord_add']
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_smul_left' (a : K) (x y : V) :
    majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem majAt_add_right' (x y z : V) : majAt b X v x (y + z) = majAt b X v x y + majAt b X v x z := by
  simp only [majAt, fcoord_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem star_majAt' (x y : V) : star (majAt b X v x y) = majAt b X v y x := by
  simp only [majAt, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem selfAdj_of_pyth (hv : v.IsComplex) (e : V →ₗ[K] V)
    (h : ∀ x y, normAt b X v (e x + (y - e y)) ^ 2 = normAt b X v (e x) ^ 2 + normAt b X v (y - e y) ^ 2) (x y : V) :
    majAt b X v (e x) y = majAt b X v x (e y) := by
  have hre : ∀ x y, (majAt b X v (e x) (y - e y)).re = 0 := by
    intro x y
    have h1 := normAt_add_sq b X v (e x) (y - e y)
    have h2 := h x y
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply InfinitePlace.isComplex_iff.mp hv
    first
    | exact fun t => Complex.conj_eq_iff_im.mpr (hcon t)
    | (rw [ComplexEmbedding.isReal_iff]; ext t; exact Complex.conj_eq_iff_im.mpr (hcon t))
  have hzero : ∀ x y, majAt b X v (e x) (y - e y) = 0 := by
    intro x y
    have h0 := hre x y
    have h1 := hre (a • x) y
    rw [map_smul, majAt_smul_left'] at h1
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, h0] at h1
    have hm : (v.embedding a).im * (majAt b X v (e x) (y - e y)).im = 0 := by linarith
    refine Complex.ext (by simpa using h0) ?_
    rcases mul_eq_zero.mp hm with hm | hm
    · exact absurd hm ha
    · simpa using hm
  have hL : majAt b X v (e x) y = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e x) (e y) (y - e y)
    rw [hzero, add_zero, show e y + (y - e y) = y by abel] at this
    exact this
  have hR : majAt b X v x (e y) = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e y) (e x) (x - e x)
    rw [hzero, add_zero, show e x + (x - e x) = x by abel] at this
    rw [← star_majAt' b X v (e y) x, this, star_majAt']
  rw [hL, hR]

end Maj

theorem numeric {dg db μ μg m lg δ Q : ℝ} (hd : 0 < dg + db) (hdg : 0 ≤ dg) (hdb : 0 ≤ db)
    (hcut : (dg + db) * μ ≤ dg * μg + db * (m + lg)) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 12) (hb : db ≤ 3 * δ * (dg + db))
    (hm : m ≤ Q) (hμ : -Q ≤ μ) (hlg : lg ≤ Q) (hlg0 : 0 ≤ lg) : μ - 12 * δ * Q ≤ μg := by
  have hQ : 0 ≤ Q := by linarith
  have hδdb : δ * db ≤ 1 / 12 * db := mul_le_mul_of_nonneg_right hδ' hdb
  have hdg0 : 0 < dg := by
    rcases lt_or_eq_of_le hdg with h | h
    · exact h
    · subst h
      nlinarith
  have h4 : db ≤ 4 * δ * dg := by nlinarith
  have k1 : db * (-Q) ≤ db * μ := mul_le_mul_of_nonneg_left hμ hdb
  have k2 : db * Q ≤ 4 * δ * dg * Q := mul_le_mul_of_nonneg_right h4 hQ
  have k3 : db * m ≤ db * Q := mul_le_mul_of_nonneg_left hm hdb
  have k4 : db * lg ≤ db * Q := mul_le_mul_of_nonneg_left hlg hdb
  have key : dg * (μ - 12 * δ * Q) ≤ dg * μg := by nlinarith
  exact le_of_mul_le_mul_left key hdg0

theorem slope_good_ge : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L M : Submodule (𝓞 K) V) (e : V →ₗ[K] V) (g : ℕ) (δ Q : ℝ), HasGram N → M.FG → L ≤ M → L ≠ ⊥ → e ∘ₗ e = e → (∀ σ x y, N σ (e x + (y - e y)) ^ 2 = N σ (e x) ^ 2 + N σ (y - e y) ^ 2) → 1 ≤ g → (∀ x ∈ L, (g : K) • e x ∈ L) → 0 ≤ δ → δ ≤ 1 / 12 → (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ≤ 3 * δ * Formalism.HN.rkK L → slopeMax_sq N M ≤ Q → -Q ≤ slope_sq N L → 2 * Real.log g ≤ Q → slope_sq N L - 12 * δ * Q ≤ slope_sq N (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) := by
  intro K V _ _ _ _ _ _ _ N L M e g δ Q hGram hM hLM hL0 hee hpyth hg hint hδ hδ' hrk hmax hmin hlog
  letI : StarRing K := starRingOfComm
  obtain ⟨F⟩ := hGram
  obtain ⟨n, ⟨⟨b, X⟩, hG⟩⟩ := F
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  have hLfg : L.FG := Submodule.FG.of_le hM hLM
  have hRfg : (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)).FG :=
    Submodule.FG.of_le hM (inf_le_left.trans hLM)
  have hsa : ∀ v x y, majAt b X v (e x) y = majAt b X v x (e y) := by
    intro v
    apply selfAdj_of_pyth b X v (IsTotallyComplex.isComplex v) e
    intro x y
    simp only [(hG v).2]
    exact hpyth v.embedding x y
  obtain ⟨hrkadd, hcut, hmaj⟩ := Formalism.ExtensionFiltration.goodBadCut K V (Fin n) b X hX e g L hLfg hg hee hsa hint
  have hM0 : M ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hLM))
  rw [slope_sq_eq hG hLfg] at hmin ⊢
  rw [slope_sq_eq hG hRfg]
  rw [(slopeMax_slopeMin_eq hG hM hM0).1] at hmax
  have hne := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b L hL0
  have hrkR : (Formalism.HN.rkK L : ℝ) = (Formalism.HN.rkK (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) := by
    exact_mod_cast hrkadd.symm
  have hpos : (0 : ℝ) < Formalism.HN.rkK L := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hmj := hmaj M hM hLM
  have hlg0 : 0 ≤ 2 * Real.log g := by
    have : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have := Real.log_nonneg this
    linarith
  rw [hrkR] at hcut hrk hpos
  exact numeric hpos (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) hδ hδ' hrk hmax hmin hlog hlg0

end GlobalTheory.CutNum
end

section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology

namespace GlobalTheory.CovTop.Assembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tendsto_exp_mul_rpow {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-(x ^ c)) * x ^ A) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / c) 1 one_pos).comp (tendsto_rpow_atTop hc)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hx, mul_div_cancel₀ _ hc.ne', mul_comm, neg_mul, one_mul]

theorem exists_loss_le {c : ℝ} (hc : 0 < c) (A B C : ℝ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 12 * Real.exp (-(x ^ c)) * (x ^ A + x ^ B + C) ≤ 1 := by
  have h := ((((tendsto_exp_mul_rpow hc A).add (tendsto_exp_mul_rpow hc B)).add
    ((tendsto_exp_mul_rpow hc 0).mul_const C)).const_mul 12)
  have h1 : (12 : ℝ) * (0 + 0 + 0 * C) < 1 := by norm_num
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds h1))
  refine ⟨x0, fun x hx => ?_⟩
  have := hx0 x hx
  simp only [Real.rpow_zero] at this
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem lcv_le {A B PP C1 C2 : ℝ} (hx : 0 < L.sc.x) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2)
    (hs : 12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * (L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) ≤ 1)
    (hG : GramAt p i) (hR : RecAt p i) (hC : CutAt p i) (hB : BadAt p i) (hL : LamAt p i A) (hS : SizeAt p i PP B)
    (hK : CoreAt p i C1) (hW : LowAt p i C2) :
    Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤ mainT p i + (C1 + C2 + 1) * unitE p := by
  haveI : IsTotallyComplex D.what₂.LL := D.tcLL
  obtain ⟨g1, g2, g3, -⟩ := hG
  obtain ⟨c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, -, s4, -⟩ := hS
  unfold RecAt at hR
  unfold LamAt at hL
  unfold CoreAt at hK
  unfold LowAt at hW
  have hA := Real.rpow_pos_of_pos hx A
  have hB' := Real.rpow_pos_of_pos hx B
  have hδ := Real.exp_pos (-(L.sc.x ^ (L.sc.ez / 7)))
  have hm := (abs_le.1 s4).2
  have key := GlobalTheory.CutNum.slope_good_ge D.what₂.LL _ (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i)
    (latAll p.R.toRealDat i) (eGood p.R.toRealDat i) (Fintype.card p.P.Gp) (Real.exp (-(L.sc.x ^ (L.sc.ez / 7))))
    ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) g1 g2 inf_le_left
    (fun h => g3 (le_bot_iff.1 (h ▸ latGood_le p.R.toRealDat p.F.lv2 i))) c1 c2 Fintype.card_pos c3 hδ.le
  have key' : slope_sq (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i) -
      12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) ≤
      slope_sq (nrmR p.R.toRealDat i) (latGood p.R.toRealDat p.F.lv2 i) := by
    refine key ?_ hB ?_ ?_ ?_
    all_goals
      clear key hR
      generalize Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) = δ at *
      generalize L.sc.x ^ A = a at *
      generalize L.sc.x ^ B = b at *
      generalize unitE p = E at *
      have hE : 0 ≤ E := by linarith
      have ea := mul_le_mul_of_nonneg_left s2 hA.le
      have eb := mul_le_mul_of_nonneg_left s2 hB'.le
      have e1 := mul_nonneg h1 hE
      have e2 := mul_nonneg h2 hE
      have e3 := mul_nonneg hA.le hE
      have e4 := mul_nonneg hB'.le hE
    · nlinarith [mul_nonneg hδ.le hA.le, mul_nonneg hδ.le hB'.le, mul_nonneg hδ.le h1, mul_nonneg hδ.le h2]
    · linarith
    · linarith
    · linarith
  have hE : 0 ≤ unitE p := by linarith
  have := mul_le_mul_of_nonneg_right hs hE
  rw [mul_assoc] at this
  linarith

theorem covolX_of_steps : Gram → Rec → Cut → Bad → abelian₂ → Size → CoreLe → Low → CovolX := by
  intro hG hR hC hB hL hS hK hW
  refine Closed.imp (Closed.and (Closed.and (Closed.and hG hR) (Closed.and hC hB))
    (Closed.and (Closed.and hL hS) (Closed.and hK hW))) ?_
  rintro eps Fm CH he ⟨⟨⟨⟨_, -, g⟩, ⟨_, -, r⟩⟩, ⟨⟨_, -, c⟩, ⟨_, -, b⟩⟩⟩, ⟨⟨A, -, l⟩, ⟨B, -, s⟩⟩, ⟨C1, h1, k⟩, ⟨C2, h2, w⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  obtain ⟨x0, hx0⟩ := exists_loss_le (show 0 < Fm.ez / 7 by positivity) A B (C1 + C2 + 1)
  obtain ⟨x1, h⟩ := (((g.and r).and (c.and b)).and ((l.and s).and (k.and w)))
  refine ⟨C1 + C2 + 1, by linarith, max x0 x1, fun x hx hle ι p hp C hC i => ?_⟩
  obtain ⟨⟨⟨g, r⟩, c, b⟩, ⟨l, s⟩, k, w⟩ := h x hx ((le_max_right _ _).trans hle) ι p hp
  have ex := Fm.L_x x ι hx
  have ee := Fm.L_ez x ι
  have hs := hx0 x ((le_max_left _ _).trans hle)
  have hx' : 0 < x := (zero_lt_one.trans Fm.one_lt_family_threshold).trans hx
  have main := lcv_le p i (ex.symm ▸ hx') h1 h2 (by rw [ex, ee]; exact hs) (g i) (r i) (c i) (b i) (l i) (s i) (k i) (w i)
  have hE : 0 ≤ unitE p := by
    obtain ⟨s1, s2, -⟩ := s i
    linarith
  refine main.trans ?_
  show mainT p i + (C1 + C2 + 1) * unitE p ≤ mainT p i + C * unitE p
  have := mul_le_mul_of_nonneg_right hC hE
  linarith

end GlobalTheory.CovTop.Assembly

end
end
