import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

def RRBelowCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F →
    ∀ (i : ℕ), i ≤ P.r → ∀ (w : List C.Letter), KB.CutWord P p.l0 w → ∀ (h h' : C.LPt) (m : ℕ), 1 ≤ m →
      D.ptSize h + m = i → D.ptSize h' + m = i →
      ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
        (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nPt_app_cont (TT : ℝ) (h : C.LPt) (s : ℕ) :
    ContinuousOn (fun z : ℂ => TBB.nPt P.k P.r TT (h ++ [(s, z)])) {0}ᶜ := by
  have h1 := Formalism.FourierDecayAlt.P.LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) s h 1
  have hmap : Set.MapsTo (fun z : ℂ => ((Complex.normSq z - TT : ℝ), z)) {0}ᶜ (Set.univ ×ˢ {0}ᶜ) :=
    fun z hz => ⟨Set.mem_univ _, hz⟩
  have h2 := h1.comp (Continuous.continuousOn (by fun_prop)) hmap
  refine h2.congr fun z _ => ?_
  simp only [Function.comp, TBB.nPt]
  congr 1
  simp [D.ptGG, D.ptLast]

theorem diag_cont {f : ℂ × ℂ → ℂ} (hf : ContinuousOn f (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))) :
    ContinuousOn (fun z : ℂ => f (z, z)) {0}ᶜ :=
  hf.comp (Continuous.continuousOn (by fun_prop)) fun _ hz => ⟨hz, hz⟩

theorem ew_cont_of_rr (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (w : List C.Letter) (h : C.LPt) (s : ℕ)
    (hRR : ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (h ++ [(s, cc.1)]) (h ++ [(s, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))) :
    ContinuousOn (fun z : ℂ => TBB.Ew p nn F i w (h ++ [(s, z)])) {0}ᶜ := by
  have hn := nPt_app_cont (P := P) (TBB.TTp p) h s
  have hw : ContinuousOn (fun z : ℂ => ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, z)])) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, z)])) / TBB.normC nn w : ℝ) : ℂ)) {0}ᶜ :=
    Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_sqrt.comp_continuousOn hn).mul (Real.continuous_sqrt.comp_continuousOn hn)).div_const _)
  have hr := diag_cont hRR
  exact Complex.continuous_re.comp_continuousOn (hw.mul hr)

end place

theorem germContAll_of (hR : RRBelowCpt) : GermContAll := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF _ b s hb hs hbs h hh w hw _
  have hsz : D.ptSize h + s = b + s - 1 := by rw [hh.2]; omega
  refine ew_cont_of_rr p nn F (b + s - 1) w h s ?_
  rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
  · exact hR Wp Wq P p F hF (b + s - 1) (by omega) w hw.1 h h s (by omega) hsz hsz
  · have he : b + s - 1 = P.r + 1 := by omega
    rw [he] at hsz ⊢
    exact Formalism.FourierDecayAlt.P.LastBlockContinuity.rrTop_cont P p F hF Cb hCb w hw.1 h h s (by omega) hsz hsz

end

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

theorem rr_congr_below {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F)
    (hE : ∀ g ∈ B.GV P.k P.r, F g = F₂ g) (i : ℕ) (hi : i ≤ P.r) (hi1 : 1 ≤ i) (w : List C.Letter)
    (a b : C.LPt) : p.RR F i w a b = p.RR F₂ i w a b := by
  by_cases hl : D.IsLocPt a i ∧ D.IsLocPt b i
  · unfold KB.Pl.RR D.RRplace
    rw [dif_pos hl, dif_pos hl, dif_pos hi, dif_pos hi]
    have hU : ∀ (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV P.k P.r,
        D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e g = D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e g :=
      fun e g hg => (Formalism.FourierDecayAlt.P.CutEXUw.uwG_congrG p.T.base.z p.T.base.z' i hi isOpen_univ
        (fun x _ hx => (hE x hx).symm) w e g (Set.mem_univ _) hg)
    have hS : ∀ (q : C.LPt), D.IsLocPt q i → ∀ (e : Wd.Ix (Fin w.length)),
        ∀ γ ∈ B.GV P.k (P.r - D.ptSize q),
        D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e) q γ =
          D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e) q γ := by
      intro q hq e γ hγ
      have h1 := Formalism.FourierDecayAlt.P.PBG.sliceAt_lincomb P.k P.r Wp Wq p.T F hF i hi hi1 q hq ({()} : Finset Unit)
        (fun _ => 1) (fun _ => w) (fun _ => e) (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e)
        (fun g hg _ => by simp [hU e g hg]) γ hγ
      simp only [Finset.sum_singleton, one_smul] at h1
      exact h1.symm
    refine Formalism.FourierDecayAlt.P.PBG.formLev_congrGV p.T _ _ w _ _ _ _ (fun e g hg => ?_) (fun e g hg => ?_)
    · simp only [D.castF]
      exact hS a hl.1 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
    · simp only [D.castF]
      exact hS b hl.2 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
  · rw [PBL.rr_zero_of_not p F i w a b hl, PBL.rr_zero_of_not p F₂ i w a b hl]

theorem rank_below_compact : RRBelowCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F hF i hi w hw h h' m hm hsz hsz'
  have hi1 : 1 ≤ i := by omega
  have hF0 := hF
  obtain ⟨hs, -, ⟨δ, hδ, hG⟩⟩ := hF
  have heq : ∀ g ∈ B.GV P.k P.r, D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ g = F g :=
    cutF_eq_on_gv p.T.base Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hG hδ le_rfl
  obtain ⟨Cs, -, hSQ⟩ := Formalism.FourierDecayAlt.P.LastBlockContinuity.sliceContQ
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set N : ℕ := w.length with hN
  set A₀ : ℝ := Cs * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)
    with hA₀
  set M : ℕ := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨εn, hn⟩ := Formalism.FourierDecayAlt.P.PBG.nice_of_cpt p.T.base hF0
  obtain ⟨cF, hcF⟩ := hn.2.1 A₀ M
  have hcut : ContinuousOn (fun cc : ℂ × ℂ => p.RR (D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ) i w
      (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)])) (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
    refine Formalism.FourierDecayAlt.P.LastBlockContinuity.rrBelow_cont P p Formalism.FourierDecayAlt.P.Topx2.chi0 δ F i hi w N le_rfl h h' m hm hsz hsz' ?_ ?_
    · intro hh t0 ht0
      obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl P.k P.r Wp Wq p.T Formalism.FourierDecayAlt.P.Topx2.chi0 A₀ N P rfl rfl hk2
        Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation le_rfl δ hδ i hi w le_rfl h m (Formalism.FourierDecayAlt.P.LastBlockContinuity.hc_app h m hsz) hh hm hsz t0 ht0
      exact ⟨ε', hε', fun e => H e F cF hs hcF⟩
    · intro hh t0 ht0
      obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl P.k P.r Wp Wq p.T Formalism.FourierDecayAlt.P.Topx2.chi0 A₀ N P rfl rfl hk2
        Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation le_rfl δ hδ i hi w le_rfl h' m (Formalism.FourierDecayAlt.P.LastBlockContinuity.hc_app h' m hsz') hh hm hsz' t0 ht0
      exact ⟨ε', hε', fun e => H e F cF hs hcF⟩
  refine hcut.congr fun cc _ => ?_
  exact rr_congr_below p hF0 (fun g hg => (heq g hg).symm) i hi hi1 w _ _

theorem germ_continuity_all_levels : GermContAll := germContAll_of rank_below_compact

end

end Formalism.FourierDecayAlt.P.CutBP
end
