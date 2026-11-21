import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector

section
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

theorem transv_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (Y : Data E r)
    (hX : Xx.toData = Y) (la : Wt Y.Ψ r) (M : ℝ) (hχ : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (htr : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b)) :
    ∀ v ∈ Xx.L', herm Y.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Y.Γ, Y.χ la γ = 1 ∧
        ∀ τ : Y.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Y.flowMat v τ ((M : ℂ) * τ.1 b) := by
  subst hX
  intro v hv hvv b hb hbi
  obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
  exact ⟨γ, hγ, hχ γ hγ, hγ'⟩

theorem lamSup_of_laws : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → F ≠ 0 → -lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U (xiR D) (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  classical
  intro D j H Dw l Xo c U dict h _ χ hχ a n ha F hF hval hF0
  have hσ₀ : GoodEmb c c.F.val.toRingHom := rfl
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hU := h.unf c.F.val.toRingHom hσ₀
  have hpq : Dw.p + Dw.q = D.R.r := hU.1.symm
  have hSD : SupDef Xo c U :=
    (Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp D.host.E H Dw l Xo c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (h.unf σ hσ)))
  set σ₀ := c.F.val.toRingHom with hσdef
  have hhol : rdU (U σ₀) F ∈ holSub (U σ₀).X (laU (U σ₀) a n) := ((mem_cusp _ _ _ _ _ F).1 hF).2 σ₀ hσ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ₀).X (laU (U σ₀) a n) hhol
  have hfin : supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) ≠ ⊤ := supE_cusp_ne_top hσ₀ hF
  have hpos : 0 < supN (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (hSD a n ha σ₀ hσ₀ F hF heq.symm) hF0
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) hpos hfin
  have hhalf : ∀ x ∈ ((U σ₀).X k).dom, ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) x ≤
      2 * ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0 := by linarith
  obtain ⟨Xx, hX, hXg, hΛ, -, M, hM, hMk, htr⟩ := GlobalTheory.T.exists_selfDual_data_transvection_principal_level D j H Dw l Xo c U dict h σ₀ hσ₀ k
  have hsp := GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict h σ₀ hσ₀ a n k
  set s : ℝ := ((absA Dw a : ℕ) : ℝ) with hs
  set t : ℝ := ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) with ht
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have hw : (∑ τ, ((U σ₀).X k).spread (laU (U σ₀) a n k) τ) ≤ s + t + 1 := by linarith
  have hw1 : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((U σ₀).X k) hX _ _ z0 M (s + t + 1) (hSS k) hM
    hw hw1 hr (transv_of_eq Xx _ hX _ M (h.chiTriv σ₀ hσ₀ a n ha k) htr) hz0 hhalf hposz
  have hp0 : Xx.p0 = Dw.q := (congrArg Data.p0 hX).trans (hU.2.1 k).1
  have heps : epStar M (fdeg D.host.E) (s + t + 1) Xx.k0 = epsLev D.host.E D.host.d l.M (s + t + 1) := by
    unfold epsLev epStar
    congr 2
    rw [← hMk]
    ring
  have hLa : frameBasisRadius D.R.r Xx.p0 (fdeg D.host.E) (dE D.host.E) (Real.sqrt (epStar M (fdeg D.host.E) (s + t + 1) Xx.k0))
      (3 * frameRadius (s + t + 1) D.R.r / 5) = cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1) := by
    unfold cmLen
    rw [hp0, heps]
  rw [hLa] at hLB
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hd1 := GlobalTheory.WtSizes.one_le_dE D
  have hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * Xx.k0)| + 3 + Real.log (dE D.host.E) := by
    have := Real.log_nonneg hd1
    have := le_abs_self (Real.log (M * Xx.k0))
    have := abs_nonneg (Real.log (M * Xx.k0))
    linarith
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.T.exists_constant_cmEvaluation_fits_room
  have hLa1 : 1 ≤ cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1) := by
    rw [← hLa]
    exact (hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) |Real.log (M * Xx.k0)| 0 M Xx.k0 (s + t + 1) hf1 hr
      Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos hw1 hlog).1
  have hSpos : ∀ σ, 0 < supC Xo c U (xiR D) (goodOf c σ) a n F := fun σ => by
    unfold supC
    refine mul_pos (lieFac_pos _ _ _) (lt_of_le_of_ne (supN_nonneg _ _ _) fun h0 => hF0 ?_)
    exact hSD a n ha _ (Formalism.L2.Pj.goodEmb_goodOf (c := c) σ) F hF h0.symm
  have h5 := GlobalTheory.T.meanLogSupNorm_lowerBound_cmFrame_nonvanishing D.host.E H Dw l Xo c D.R.r U (xiR D) h.unf h.xiAbs (by omega) χ hχ a n ha F hF hval hSpos
    k ⟨x, hx⟩ Xx hX D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  refine le_trans ?_ h5
  have et : ((Module.finrank ℚ D.host.E / 2 * D.R.r : ℕ) : ℝ) * n = t := by
    rw [ht]
    simp only [fdeg, Nat.cast_mul]
  rw [et]
  unfold lamSup
  apply le_of_eq
  simp only [absA] at hs
  rw [← hs]
  ring

end GlobalTheory
end

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogSupNorm_lowerBound_principalLevel : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → F ≠ 0 → -lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U (xiR D) (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  atlas_forward_decl GlobalTheory.lamSup_of_laws
end

section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamPet

open scoped ENNReal

theorem log_le_of_sq_le {A B : ℝ≥0∞} {K L : ℝ} (hL : 0 < L) (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hA0 : A ≠ 0)
    (h : A ^ 2 ≤ ENNReal.ofReal K * B ^ 2) :
    0 < L * B.toReal ∧ Real.log (L * A.toReal) ≤ 1 / 2 * Real.log K + Real.log (L * B.toReal) := by
  have hApos : 0 < A.toReal := ENNReal.toReal_pos hA0 hA
  have hK0 : 0 ≤ K := by
    by_contra hK
    rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hK)), zero_mul] at h
    exact hA0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h zero_le))
  have h2 : A.toReal ^ 2 ≤ K * B.toReal ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB)) h
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, ENNReal.toReal_pow] at this
  have hB0 : 0 < B.toReal := by
    rcases (ENNReal.toReal_nonneg (a := B)).lt_or_eq with hb | hb
    · exact hb
    · rw [← hb] at h2; nlinarith
  have hKpos : 0 < K := by
    by_contra hK
    have : K * B.toReal ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hK) (sq_nonneg _)
    nlinarith
  refine ⟨mul_pos hL hB0, ?_⟩
  rw [Real.log_mul hL.ne' hApos.ne', Real.log_mul hL.ne' hB0.ne']
  have h3 : Real.log (A.toReal ^ 2) ≤ Real.log (K * B.toReal ^ 2) := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_mul hKpos.ne' (by positivity), Real.log_pow] at h3
  push_cast at h3
  linarith

theorem mean_log_petersson_ge : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 → (∀ σ, 0 < normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F) ∧ -lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) / (Module.finrank ℚ c.F : ℝ) := by
  intro hM hT D j H Dw l Xo c U dict hL _ χ hχ a n hD F hF hF0
  have hFc : (F : Rul Xo c) ∈ cusp Xo c U a n := cuspW_wtZ (Xo := Xo) (c := c) (U := U) a n ▸ F.2
  have hF0' : (F : Rul Xo c) ≠ 0 := fun h => hF0 (Subtype.ext h)
  have hsup := GlobalTheory.T.meanLogSupNorm_lowerBound_principalLevel D j H Dw l Xo c U dict hL χ hχ a n hD _ hFc hF hF0'
  have hsl := GlobalTheory.T.weighted_frame_sum_positive hM hT D j H Dw l Xo c U dict hL
  have hsp := GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict hL
  have hdef : Formalism.L2.Pj.SupDef Xo c U :=
    (Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp _ H Dw l Xo c _ _ hL.unf)
  set x := xiR D
  set K := supConst D.host.E D.R.r D.host.d l.M
    (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) with hK
  have hper : ∀ σ : c.F →+* ℂ, 0 < normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F ∧
      Real.log (supC Xo c U x (goodOf c σ) a n F) ≤
        1 / 2 * Real.log K + Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F) := by
    intro σ
    have hσ : GoodEmb c (goodOf c σ) := Formalism.L2.PjFree.goodEmb_goodOf c σ
    have hhol := ((mem_cusp Xo c U a n _).1 hFc).2 _ hσ
    have hw : (0 : ℝ) < ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 := by positivity
    have hb := hsl _ hσ (laU (U (goodOf c σ)) a n) _ hw
      (fun k => (hsp _ hσ a n k).trans (by linarith)) (hL.chiTriv _ hσ a n hD) _ hhol
    have hne0 : supE (U (goodOf c σ)).X (laU (U (goodOf c σ)) a n) (rdU (U (goodOf c σ)) F) ≠ 0 := by
      intro h0
      refine hF0' (hdef a n hD _ hσ _ hFc ?_)
      unfold supN; rw [h0, ENNReal.toReal_zero]
    have hfin := supE_cusp_ne_top hσ hFc
    obtain ⟨_, _, _, _, _, hdu, _⟩ := hL.dictU _ hσ
    have hpfin : petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n)
        (rdU (U (goodOf c σ)) F) ≠ ⊤ :=
      petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hhol
    have key := log_le_of_sq_le (lieFac_pos Dw x a) hfin hpfin hne0 hb
    have e : normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F = lieFac Dw x a *
        (petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n)
          (rdU (U (goodOf c σ)) F)).toReal := by
      show lieFacZ Dw x (wtZ a n) * _ = _
      rw [lieFacZ_wtZ, modelWt_wtZ]
    rw [e]
    exact key
  refine ⟨fun σ => (hper σ).1, ?_⟩
  have hN : (0 : ℝ) < (Module.finrank ℚ c.F : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcard : (Finset.univ : Finset (c.F →+* ℂ)).card = Module.finrank ℚ c.F := by
    rw [Finset.card_univ]; exact NumberField.Embeddings.card c.F ℂ
  have hsum : (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U x (goodOf c σ) a n F)) -
      (Module.finrank ℚ c.F : ℝ) * (1 / 2 * Real.log K) ≤
      ∑ σ : c.F →+* ℂ, Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun σ _ => (hper σ).2
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at this
    linarith
  have e : lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ)
      ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) = lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re
      ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 / 2 * Real.log K := rfl
  rw [e, le_div_iff₀ hN]
  rw [le_div_iff₀ hN] at hsup
  nlinarith

end GlobalTheory.LamPet
end

section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_character_frame_first : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 → (∀ σ, 0 < normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F) ∧ -lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.LamPet.mean_log_petersson_ge | exact GlobalTheory.LamPet.mean_log_petersson_ge | (intros; apply GlobalTheory.LamPet.mean_log_petersson_ge <;> assumption)
end

section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_forms_finite_dimensional : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cuspW Xo c U (wtZ a n)) ∧ (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) ≤ supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) := by
  first | exact @GlobalTheory.LevGeo.RankBd.finrank_cuspW_le | exact GlobalTheory.LevGeo.RankBd.finrank_cuspW_le | (intros; apply GlobalTheory.LevGeo.RankBd.finrank_cuspW_le <;> assumption)
end

section
open NumberField GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_sq_le_of_no_short_vector : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ → (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) → slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) + Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short | exact GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short | (intros; apply GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short <;> assumption)
end

section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LamMuMax

theorem slopeMax_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := by
  intro hMass hTor D j H Dw l Xo c U dict hL _ χ hχ a n hD hG h0
  have hTC : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hj : ∀ (σ : c.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)),
      normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) ((starRingEnd ℂ).comp σ) f =
        normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ f := fun σ f => by
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hP := GlobalTheory.T.kronecker_character_frame_first hMass hTor D j H Dw l Xo c U dict hL χ hχ a n hD
  have hR := GlobalTheory.T.cusp_forms_finite_dimensional hMass hTor D j H Dw l Xo c U dict hL a n hD
  have hS := GlobalTheory.T.maxSlope_sq_le_of_no_short_vector c.F (cuspW Xo c U (wtZ a n)) (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n))
    (latW U (wtZ a n)) _ hG.1 hj hG.2.1 h0 (fun F hF hF0 => (hP F hF hF0).2)
  haveI := hR.1
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  haveI : Nontrivial (cuspW Xo c U (wtZ a n)) := ⟨⟨F, 0, hF0⟩⟩
  have hpos : (0 : ℝ) < (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hlog := Real.log_le_log hpos hR.2
  refine hS.trans ?_
  rw [lamPet]
  linarith

end GlobalTheory.LamMuMax
end
