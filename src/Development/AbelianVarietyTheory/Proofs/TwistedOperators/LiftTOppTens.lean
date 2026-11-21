import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalFlipOnVolumesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorsRowAndColumnPaths
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainDownEqLiftAlongPath
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneLessEqTopBesselLevelPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombination
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvariant

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorankOneLess_eq_topBesselLevel_period : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : GlobalTheory.FunObj.Vol G)
    (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)),
    Bplus Wl M φ F = (GlobalTheory.RowChain.topLev G hM).per Wl.ψ φ F := by
  first | exact @GlobalTheory.RowChain.TopPer.bplus_eq_topLev_per | exact GlobalTheory.RowChain.TopPer.bplus_eq_topLev_per | (intros; apply GlobalTheory.RowChain.TopPer.bplus_eq_topLev_per <;> assumption)
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem bplus_eq_per {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    (M : GlobalTheory.FunObj.Vol G) (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus Wl M φ F = (topLev G hM).per Wl.ψ φ F :=
  GlobalTheory.T.besselPeriodCorankOneLess_eq_topBesselLevel_period G Wl t M hM φ F

end GlobalTheory.RowChain

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem bplus_eq_coef {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus W M φ F = ∫ h in M.fd (.top 0), φ h *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F (embTop G h) ∂M.ν (.top 0) := by
  simp only [Bplus, besInt, GlobalTheory.Mem.TrueRecord.coef, ← integral_const_mul, mul_assoc]

theorem nu_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {M M' : Vol G}
    (hM : M.IsRow) (hM' : M'.IsRow) : M.ν (.top 0) = M'.ν (.top 0) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have h1 := hM.top
  have h2 := hM'.top
  unfold Vol.IsAt at h1 h2
  have hz : Node.neg D.R.m (Node.top 0) = 0 := rfl
  rw [if_pos hz] at h1 h2
  haveI := h1.1.1
  haveI := h2.1.1
  have e := Measure.isMulLeftInvariant_eq_smul (M.ν (.top 0)) (M'.ν (.top 0))
  have a1 := GlobalTheory.Mass.Levels.measure_comap_finE h1.1
  have a2 := GlobalTheory.Mass.Levels.measure_comap_finE h2.1
  have hc : Measure.haarScalarFactor (M.ν (.top 0)) (M'.ν (.top 0)) = 1 := by
    rw [e, Measure.smul_apply, a2] at a1
    simpa using a1
  rw [e, hc, one_smul]

theorem bplus_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (M M' : Vol G),
    M.IsRow → M'.IsRow → ∀ φ F, GlobalTheory.Unf.IsContAut _ φ → GlobalTheory.Unf.IsContAut _ F → Bplus W M φ F = Bplus W M' φ F := by
  intro D T L sc G W M M' hM hM' φ F hφ hF
  have hψ := W.ψ_std
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hF' : ∀ γ ∈ GQ (G.V (.grid D.R.m 0)), ∀ g, F (γ * g) = F g := hF.1
  have hN := hM.unip
  have hN' := hM'.unip
  rw [bplus_eq_coef, bplus_eq_coef]
  have ec : ∀ g, GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F g =
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F g := fun g =>
    GlobalTheory.Mem.TrueRecord.coef_eq hψ hι G.besTop hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 hF' g
  simp only [ec]
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hf1 := (hM.top.haar_fund).2
  have hf2 := hM'.top.haar_fund
  rw [nu_top_eq hM hM'] at hf1 ⊢
  haveI := hf2.1
  set d := G.rowDec 0 (by have := D.R.two_le_m; omega)
  have e0 : ∀ h, embTop G h = stabilizerEmbedding d h := fun h => rfl
  have e1 : stabilizerEmbedding d 1 = 1 := by
    have := GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d 1 1
    rw [one_mul] at this
    exact left_eq_mul.mp this
  refine hf1.setIntegral_eq hf2.2 fun γ h => ?_
  have hγ : (γ : GA D (G.V (.top 0))) ∈ GQ (G.V (.top 0)) := γ.2
  have hinv : stabilizerEmbedding d (γ : GA D (G.V (.top 0)))⁻¹ = (stabilizerEmbedding d γ)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel, e1]
  have r1 : EmbRel _ _ d.ι (stabilizerEmbedding d γ) γ := (embRel_iff d _ _).2 rfl
  have r2 : EmbRel _ _ d.ι (stabilizerEmbedding d γ)⁻¹ (γ : GA D (G.V (.top 0)))⁻¹ := hinv ▸ (embRel_iff d _ _).2 rfl
  change φ ((γ : GA D (G.V (.top 0))) * h) *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F (embTop G ((γ : GA D (G.V (.top 0))) * h)) = _
  rw [hφ.1 _ hγ, e0, e0, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul,
    GlobalTheory.Mem.TrueRecord.coef_left hψ hι G.besTop hN'.1 hN'.2.1 hN'.2.2 hF' (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational d _ hγ) r1 r2]

end GlobalTheory.RowVal
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

section Lin

variable {T : Type} {D : D7} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {M : Vol G}
  {ρ : RealMatch W} {t : T}

theorem rowFam_cusp (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t))
    {F : Fn G (.grid 0 D.R.m)} (hF : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid 0 D.R.m) F) :
    ∀ n, n ≤ D.R.m → ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, ∃ φ g Q, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) φ g ∧ f i = W.fock (.chi i D.R.m) g Q) →
      GlobalTheory.FlipRun.IsCuspListed W.θ (.grid n D.R.m) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F)
  | 0, _, _, _ => hF
  | n + 1, hn, f, hf => by
    obtain ⟨φ, g, Q, hl, e1⟩ := hf (Fin.last n)
    have ih := rowFam_cusp hS he hF n (by omega) (fun i => f i.castSucc) (fun i => hf i.castSucc)
    have h1 := (hS (.right n D.R.m) (Or.inl ⟨n, D.R.m, by omega, le_rfl, rfl⟩) e he φ g hl Q _ ih).2
    show GlobalTheory.FlipRun.IsCuspListed W.θ (.grid (n + 1) D.R.m)
      (liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F))
    rw [e1]
    exact h1

theorem downFam_cusp (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    ∀ n, n ≤ D.R.m → ∀ (f : ∀ j : Fin n, Sch G (.down t D.R.m j)),
      (∀ j : Fin n, ∃ φ g Q, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) φ g ∧ f j = W.fock (.mu t D.R.m j) g Q) →
      ∀ F : Fn G (.grid D.R.m n), GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m n) F →
      GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m 0) (liftP W M (downPath t D.R.m n) (downFam t D.R.m n f) F)
  | 0, _, _, _, _, hF => hF
  | n + 1, hn, f, hf, F, hF => by
    obtain ⟨φ, g, Q, hl, e1⟩ := hf (Fin.last n)
    have h1 := (hS (.down t D.R.m n) (Or.inr ⟨D.R.m, n, le_rfl, by omega, rfl⟩) e he φ g hl Q F hF).2
    have h1' : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m n) (liftA W M (.down t D.R.m n) (f (Fin.last n)) F) := by
      rw [e1]; exact h1
    have key : liftP W M (downPath t D.R.m (n + 1)) (downFam t D.R.m (n + 1) f) F =
        liftP W M (downPath t D.R.m n) (downFam t D.R.m n fun j => f j.castSucc)
          (liftA W M (.down t D.R.m n) (f (Fin.last n)) F) :=
      pathLift_comp W M (Path.one (.down t D.R.m n)) ((), f (Fin.last n)) F (downPath t D.R.m n)
        (downFam t D.R.m n fun j => f j.castSucc)
    rw [key]
    exact downFam_cusp hS he n (by omega) (fun j => f j.castSucc) (fun j => hf j.castSucc) _ h1'

theorem opp_contAut (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam W.θ) (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D}
    (he : IsIdemSum e (locPl G t)) {F : Fn G (.grid 0 D.R.m)} (hF : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid 0 D.R.m) F)
    (P : PolRow G × PolDown G) (d φ : SchRow G × SchDown G t)
    (hd : (∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (φ.1 i) (d.1 i)) ∧
      ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ.2 j) (d.2 j)) :
    GlobalTheory.Unf.IsContAut (G.V (.grid D.R.m 0)) (liftP W M (oppPath t D.R.m) (oppPure W t P d) F) := by
  have hr := rowFam_cusp (M := M) hS he hF D.R.m le_rfl _ fun i => ⟨φ.1 i, d.1 i, P.1 i, hd.1 i, rfl⟩
  have hdn := downFam_cusp hS he D.R.m le_rfl _ (fun j => ⟨φ.2 j, d.2 j, P.2 j, hd.2 j, rfl⟩) _ hr
  have key : liftP W M (oppPath t D.R.m) (oppPure W t P d) F =
      liftP W M (downPath t D.R.m D.R.m) (downFam t D.R.m D.R.m fun j => W.fock (.mu t D.R.m j) (d.2 j) (P.2 j))
        (liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (d.1 i) (P.1 i)) F) :=
    pathLift_comp W M _ _ F _ _
  rw [key]
  have hrd := rapidDec_of_cuspForm hP hθ hdn.1 hdn.2.1
  exact ⟨hrd.1, hrd.2.1⟩

theorem bplus_fsum {M₀ : Vol G} (h₀ : M₀.IsRow) (hM : M.Is t) {φ : Fn G (.top 0)} (hφ : GlobalTheory.Unf.IsContAut _ φ) {I : Type}
    (s : Finset I) (a : I → ℂ) (f : I → Fn G (.grid D.R.m 0)) (hf : ∀ i ∈ s, GlobalTheory.Unf.IsContAut _ (f i)) :
    Bplus W M₀ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * Bplus W M₀ φ (f i) := by
  rw [bplus_indep G W M₀ M h₀ hM.isRow φ _ hφ (GlobalTheory.SeeSaw.TrcProof.contAut_sum s a f hf), bplus_eq_per G W t M hM]
  refine ((per_linear_trc D W.ψ W.ψ_std _ (topLev G hM) φ hφ).1 I s a f hf).trans ?_
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [bplus_indep G W M₀ M h₀ hM.isRow φ _ hφ (hf i hi), bplus_eq_per G W t M hM]

theorem liftT_oppTens (τi : PolRow G × PolDown G →₀ ℂ) (τ : SchRow G × SchDown G t →₀ ℂ) (F : Fn G (.grid 0 D.R.m)) :
    liftT W M (oppPath t D.R.m) (oppTens W t τi τ) F =
      ∑ P ∈ τi.support, τi P • ∑ d ∈ τ.support, τ d • liftP W M (oppPath t D.R.m) (oppPure W t P d) F := by
  have e : liftT W M (oppPath t D.R.m) (oppTens W t τi τ) F =
      AddMonoidHom.mk' (fun x => liftT W M (oppPath t D.R.m) x F) (fun x y => liftT_add W M _ x y F) (oppTens W t τi τ) := rfl
  rw [e]
  simp only [oppTens, Finsupp.sum, map_sum, AddMonoidHom.mk'_apply, liftT_single, Finset.smul_sum, smul_smul]

end Lin

theorem linAt_big : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => LinAt ch := by
  intro hP hL
  obtain ⟨a0, ha⟩ := Big.and (Big.and (GlobalTheory.T.cuspidal_flip_on_volumes hL hP) (GlobalTheory.EndCusp.formTop_isCuspListed hP)) colFn_cont_left
  refine ⟨a0, fun ε CF hC => ?_⟩
  obtain ⟨x, hx⟩ := ha ε CF hC
  refine ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  obtain ⟨⟨hstep, htop⟩, hcol⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc
  have hθ : IsInfFam ch.W.θ := by
    rw [hch.toIsBase.weil.θ]
    exact hS.core.models.inf
  intro t a τ hτ M hM τi y
  obtain ⟨e, he', φ, hφ, -⟩ := hτ
  have hca : GlobalTheory.Unf.IsContAut _ (colFn ch a) := ⟨(hcol a).2, (hcol a).1⟩
  have hFP : ∀ P : PolRow ch.G × PolDown ch.G, GlobalTheory.Unf.IsContAut _
      (∑ d ∈ τ.support, τ d • liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) := fun P =>
    GlobalTheory.SeeSaw.TrcProof.contAut_sum _ _ _ fun d hd =>
      opp_contAut hP.cuspRapidDecay hθ (hstep t M hM) he' (htop t y) P d (φ d) (hφ d hd)
  simp only [lhs, liftT_oppTens]
  rw [bplus_fsum hch.toIsBase.vol hM hca _ _ _ fun P _ => hFP P, Finsupp.sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

end GlobalTheory.RowVal
end
end
