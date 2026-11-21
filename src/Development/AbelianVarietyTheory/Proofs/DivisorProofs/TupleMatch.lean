import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumLocalFunctionsEqPureTensorScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarFiniteTensorEqDatumSmallModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemOfStanding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmodule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOriented
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSumSelfDualExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe

section
noncomputable section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

namespace GlobalTheory.TopFlip
open GlobalTheory.BigDat GlobalTheory.WeilM

set_option maxHeartbeats 1600000 in

theorem mixglobA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ f₀, IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) (ι w)) →
    (∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0) ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeBig t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.chi i (j + 1)) ε (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) ε (ρ.vT (i + 1) j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0) • f₀) φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M _ e Bs Γ X om om' h hT hti f₀ hdat ι hι
  classical
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hadd, -, -⟩ := GlobalTheory.BigDat.ThBox.thetaPt_box W M t i j e Bs Γ X om om' h hT
  have hf : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) = box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    funext u
    have := hdat.2 u
    exact this.trans ((Finsupp.sum_single_index (zero_mul _)).trans (one_mul _))
  obtain ⟨hid, hsumid⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := fun w hw => GlobalTheory.BigDat.halves_split hL W i j e Γ h.JW h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := GlobalTheory.BigDat.mixCo_spec B t i j e
  have hv := fun w hw => lagr_vac (hι w hw) (hG.vac _).1 (hG.vac _).2.1 (latPt e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hv w hw).1
  refine ⟨hc0, ?_⟩
  intro ε hε n Ψ τ _ hloc φ hφ hΨ
  obtain ⟨φ₁, φ₂, hmem, hsum⟩ := hloc
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  obtain ⟨T₁, hT₁⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg sW)
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd _ ε hε _ h₁.2.theta h₁.2.lat).1
  obtain ⟨T₂, hT₂⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd sW _ ε hε _ h₂.2.theta h₂.2.lat).1
  obtain ⟨g0, g1, g2⟩ := GlobalTheory.BigDat.boxGraph_graph_heis hL W i j e Γ h.JW h.JWW ε _ hε _ _ T₁ T₂ hT₁ hT₂
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  have hb : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f₀) Γ.M.vac) = c • box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    rw [← hf]
    exact funext fun u => (congrArg (thetaPt Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans (thetaPt_smul _ _ _ _ u)
  let R : Submodule ℂ ((Pt G i j → ℂ) × ((Ix G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ (p.1, thetaPt Γ W.ψ p.2) ∈ boxGraph e ε T₁ T₂}
      zero_mem' := ⟨zero_mem _, by
        have : thetaPt Γ W.ψ 0 = 0 := funext fun u => by simpa using thetaPt_smul Γ W.ψ 0 0 u
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun a p hp => ⟨Submodule.smul_mem _ a hp.1, by
        rw [Prod.smul_snd, show thetaPt Γ W.ψ (a • p.2) = a • thetaPt Γ W.ψ p.2 from funext (thetaPt_smul _ _ _ _)]
        exact Submodule.smul_mem _ a hp.2⟩ }
  have hA : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (atPl w 1), x ∈ mixHalf e ε := fun w hw x hx =>
    ⟨isHalf_mono (hεw w hw) hx.1, isHalf_mono (hεw w hw) hx.2⟩
  have hA' : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (cA D (atPl w 1)), x ∈ mixHalf e (cA D ε) := fun w hw x hx =>
    have : cA D ε * cA D (atPl w 1) = cA D (atPl w 1) := by rw [← RingHom.map_mul, hεw w hw]
    ⟨isHalf_mono this hx.1, isHalf_mono this hx.2⟩
  have hbase : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, ι w (Γ.M.vac _) (mixCo B t e w u)) =
      c • box e (halfInd ε (latV G i j)) (halfInd ε (latW G i j)) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, box, halfInd, halfInd]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ ((hco w).2.2.1 u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : mapV e u ∈ latV G i j ∧ mapW e u ∈ latW G i j
      · rw [if_pos ⟨hl.1, hu.1⟩, if_pos ⟨hl.2, hu.2⟩, mul_one, mul_one]
        exact Finset.prod_congr rfl fun w hw => Set.indicator_of_mem (((hh w hw).2.2.2.2 u).2.2 hl.1 hl.2) _
      · have : ∃ w ∈ locPl G t, ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u) ∉ latPt e (w.under (𝓞 D.host.F)) := by
          by_contra! hall
          exact hl ⟨mem_of_sum_smul (hεs ▸ hu.1) fun w hw => (mapV_ofMaps e _ ▸ (hall w hw).2.1 :),
            mem_of_sum_smul (hεs ▸ hu.2) fun w hw => (mapW_ofMaps e _ ▸ (hall w hw).2.2 :)⟩
        obtain ⟨w, hw, hn⟩ := this
        rw [Finset.prod_eq_zero hw (Set.indicator_of_notMem hn _)]
        rcases not_and_or.1 hl with hl | hl
        · rw [if_neg fun h => hl h.1, zero_mul, mul_zero]
        · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.1, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      rcases not_and_or.1 hu with hl | hl
      · rw [if_neg fun h => hl h.2, zero_mul, mul_zero]
      · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.2, mul_zero, mul_zero]
  have hR := GlobalTheory.InductLagr.rel_of_vac Γ.M W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => mixHalf e (atPl w 1)) (fun w => mixHalf e (cA D (atPl w 1))) (mixCo B t e) ι (halfPt e ε) R (c • f₀)
    (fun w hw => hι w hw) (fun w hw u hu => ⟨(hh w hw).1 u hu, mem_halfPt.2 (hA w hw u hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (hco w).1 u x)
    (fun w _ w' _ hne x hx u => by rw [(hco w').1, (hco w').2.2.2 w hne.symm x hx, add_zero])
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, (hco w).2.2.1 u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g1 x (hA w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g2 x (hA' w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, by
      have := (boxGraph e ε T₁ T₂).smul_mem c (Submodule.subset_span
        ⟨_, _, GlobalTheory.isSBHalf_halfInd ε _, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac, (congrArg T₂ (one_smul ℂ _).symm).trans hT₂.vac] at this
      show (_, thetaPt Γ W.ψ _) ∈ _
      rw [hbase, hb]
      exact this⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.2.2.1 v).1 hm; hv w hw e
  have hτ : (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)) ∈ boxGraph e ε T₁ T₂ :=
    sum_mem fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, (hmem d hd).1.1, (hmem d hd).2.1, by
      rw [← (hmem d hd).1.2.2 T₁ hT₁, ← (hmem d hd).2.2.2 T₂ hT₂]⟩)
  have hfst : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, ι w (φ _) (mixCo B t e w u)) =
      (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)).1 := by
    funext u
    rw [Prod.fst_sum, Finset.sum_apply]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw => congrFun (hΨ w hw) _]
      exact (hsum _ _ hu.1 hu.2).symm
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      refine (Finset.sum_eq_zero fun d hd => mul_eq_zero_of_right _ ?_).symm
      by_contra hne
      exact hu ⟨(hmem d hd).1.1.1 _ (left_ne_zero_of_mul hne), (hmem d hd).2.1.1 _ (right_ne_zero_of_mul hne)⟩
  refine ⟨hR.1, fun u => ?_⟩
  have := g0 _ (by
    have := sub_mem hR.2 hτ
    rwa [← Prod.mk.eta (p := Finset.sum _ _), Prod.mk_sub_mk, ← hfst, sub_self] at this)
  have := congrFun (sub_eq_zero.1 this) u
  rw [Prod.snd_sum, Finset.sum_apply] at this
  exact this

end GlobalTheory.TopFlip
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch
open GlobalTheory.SmallDat
open GlobalTheory.BigDat (atW atW_atPl_self atW_atPl_ne atPl_one_mul map_atW_smul symplO_cA_smul symplO_zero_right' isHalf_smul_self
  smul_of_isHalf smul_eq_zero_of_isHalf map_infPart_of_isHalf)
open GlobalTheory.BigDat.GraphHeis

namespace GlobalTheory.TopFlip
open GlobalTheory.SmallPlaces
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000 in

theorem mixglobB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ f₀, IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w) (ι w)) →
    (∏ w ∈ locPl G t, ι w (Γ.M'.vac _) 0) ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeSmall t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.mu t i j) ε (ρ.vT i j)) (IsLocVec W (.chi i j) ε (ρ.vX i j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M' X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumB W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ w ∈ locPl G t, ι w (Γ.M'.vac _) 0) • f₀) φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M _ e Bs Γ X om om' h hT hti f hf₀ I hI
  classical
  have h₁ := ρ.vT_is t i j i.2.le j.2
  have h₂ := ρ.vX_is i j i.2 j.2.le
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  have hadd : ∀ Φ ∈ schA D.host.F (IxS G i j), ∀ Φ' ∈ schA D.host.F (IxS G i j),
      thetaS Γ W.ψ (Φ + Φ') = thetaS Γ W.ψ Φ + thetaS Γ W.ψ Φ' := fun Φ hΦ Φ' hΦ' => funext fun u =>
    (tsum_congr fun _ => mul_add _ _ _).trans
      ((summable_of_mem_schA _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u _ hΦ)).tsum_add
        (summable_of_mem_schA _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u _ hΦ')))
  have hf : thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) = boxS t e (ρ.vT i j) (ρ.vX i j) :=
    funext fun u => (hf₀.2 u).trans ((Finsupp.sum_single_index (zero_mul _)).trans (one_mul _))
  obtain ⟨hid, hsumid⟩ := GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum hL (G := G) t
  have hh := fun w hw => halves_split hL W t i j e Γ h.JW₁ h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := mixCoS_spec B t i j e
  have hv := fun w hw => lagr_vac (hI w hw) (hG.vac _).1 (hG.vac _).2.1 (latPtS t e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (latPtS_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, I w (Γ.M'.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hv w hw).1
  refine ⟨hc0, fun ε hε n Ψ τ _ ⟨φ₁, φ₂, hmem, hsum⟩ φ hφ hΨ => ?_⟩
  have hb : thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) Γ.M'.vac) = c • boxS t e (ρ.vT i j) (ρ.vX i j) := by
    rw [← hf]
    exact funext fun u => (congrArg (thetaS Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans (thetaS_smul _ _ _ _ u)
  have sW := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  obtain ⟨T₁, hT₁⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ sW
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd _ ε hε _ h₁.2.theta h₁.2.lat).1
  obtain ⟨T₂, hT₂⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _
    (isSelfDualC_neg (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd) sW _ ε hε _ h₂.2.theta h₂.2.lat).1
  obtain ⟨g0, g1, g2⟩ := boxGraph_graph_heis hL W t i j e Γ h.JW₁ h.JWW ε _ hε _ _ T₁ T₂ hT₁ hT₂
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  let R : Submodule ℂ ((PtS G i j → ℂ) × ((IxS G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ (p.1, thetaS Γ W.ψ p.2) ∈ boxGraph t e ε T₁ T₂}
      zero_mem' := ⟨zero_mem _, by
        have : thetaS Γ W.ψ 0 = 0 := funext fun u => by simpa using thetaS_smul Γ W.ψ 0 0 u
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun a p hp => ⟨Submodule.smul_mem _ a hp.1, by
        rw [Prod.smul_snd, show thetaS Γ W.ψ (a • p.2) = a • thetaS Γ W.ψ p.2 from funext (thetaS_smul _ _ _ _)]
        exact Submodule.smul_mem _ a hp.2⟩ }
  have hA : ∀ w ∈ locPl G t, ∀ x ∈ mixHalfS e (atPl w 1), x ∈ mixHalfS e ε := fun w hw x hx =>
    ⟨isHalf_mono (hεw w hw) hx.1, isHalf_mono (hεw w hw) hx.2⟩
  have hA' : ∀ w ∈ locPl G t, ∀ x ∈ mixHalfS e (cA D (atPl w 1)), x ∈ mixHalfS e (cA D ε) := fun w hw x hx =>
    have : cA D ε * cA D (atPl w 1) = cA D (atPl w 1) := by rw [← RingHom.map_mul, hεw w hw]
    ⟨isHalf_mono this hx.1, isHalf_mono this hx.2⟩
  have hbase : (Set.indicator (halfPt t e ε : Set _) fun u => ∏ w ∈ locPl G t, I w (Γ.M'.vac _) (mixCoS B t e w u)) =
      c • boxS t e (halfInd ε (latA G t i j)) (halfInd ε (latB G i j)) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, boxS, halfInd, halfInd]
    by_cases hu : u ∈ mixHalfS e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ ((hco w).2.2.1 u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : mapA t e u ∈ latA G t i j ∧ mapB e u ∈ latB G i j
      · rw [if_pos ⟨hl.1, hu.1⟩, if_pos ⟨hl.2, hu.2⟩, mul_one, mul_one]
        exact Finset.prod_congr rfl fun w hw => Set.indicator_of_mem (((hh w hw).2.2.2.2 u).2.2 hl.1 hl.2) _
      · have : ∃ w ∈ locPl G t, ofMaps t e (atPl w 1 • mapA t e u, atPl w 1 • mapB e u) ∉ latPtS t e (w.under (𝓞 D.host.F)) := by
          by_contra! hall
          exact hl ⟨mem_of_sum_smul (hεs ▸ hu.1) fun w hw => (mapA_ofMaps t e _ ▸ (hall w hw).2.1 :),
            mem_of_sum_smul (hεs ▸ hu.2) fun w hw => (mapB_ofMaps t e _ ▸ (hall w hw).2.2 :)⟩
        obtain ⟨w, hw, hn⟩ := this
        rw [Finset.prod_eq_zero hw (Set.indicator_of_notMem hn _)]
        rcases not_and_or.1 hl with hl | hl
        · rw [if_neg fun h => hl h.1, zero_mul, mul_zero]
        · rw [if_neg fun h : _ ∧ IsHalf ε (mapB e u) => hl h.1, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      rcases not_and_or.1 hu with hl | hl
      · rw [if_neg fun h => hl h.2, zero_mul, mul_zero]
      · rw [if_neg fun h : _ ∧ IsHalf ε (mapB e u) => hl h.2, mul_zero, mul_zero]
  have hR := GlobalTheory.T.heisenbergStableRelation_of_vacua Γ.M' W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => mixHalfS e (atPl w 1)) (fun w => mixHalfS e (cA D (atPl w 1))) (mixCoS B t e) I (halfPt t e ε) R (c • f)
    hI (fun w hw u hu => ⟨(hh w hw).1 u hu, mem_halfPt.2 (hA w hw u hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (hco w).1 u x)
    (fun w _ w' _ hne x hx u => by rw [(hco w').1, (hco w').2.2.2 w hne.symm x hx, add_zero])
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, (hco w).2.2.1 u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd x _ hp.1, by
      have := g1 x (hA w hw x hx) _ hp.2
      rwa [← thetaS_rho] at this⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd x _ hp.1, by
      have := g2 x (hA' w hw x hx) _ hp.2
      rwa [← thetaS_rho] at this⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, by
      have := (boxGraph t e ε T₁ T₂).smul_mem c (Submodule.subset_span
        ⟨_, _, GlobalTheory.isSBHalf_halfInd ε _, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac, (congrArg T₂ (one_smul ℂ _).symm).trans hT₂.vac] at this
      show (_, thetaS Γ W.ψ _) ∈ _
      rw [hbase, hb]
      exact this⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.1.2.2.1 v).1 hm; hv w hw e
  have hτ : (∑ d ∈ τ.support, τ d • (boxS t e (φ₁ d) (φ₂ d), boxS t e d.1.2 d.2)) ∈ boxGraph t e ε T₁ T₂ :=
    sum_mem fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, (hmem d hd).1.1, (hmem d hd).2.1, by
      rw [← (hmem d hd).1.2.2 T₁ hT₁, ← (hmem d hd).2.2.2 T₂ hT₂]⟩)
  have hfst : (Set.indicator (halfPt t e ε : Set _) fun u => ∏ w ∈ locPl G t, I w (φ _) (mixCoS B t e w u)) =
      (∑ d ∈ τ.support, τ d • (boxS t e (φ₁ d) (φ₂ d), boxS t e d.1.2 d.2)).1 := by
    funext u
    rw [Prod.fst_sum, Finset.sum_apply]
    by_cases hu : u ∈ mixHalfS e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw => congrFun (hΨ w hw) _]
      exact (hsum _ _ hu.1 hu.2).symm
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      refine (Finset.sum_eq_zero fun d hd => mul_eq_zero_of_right _ ?_).symm
      by_contra hne
      exact hu ⟨(hmem d hd).1.1.1 _ (left_ne_zero_of_mul hne), (hmem d hd).2.1.1 _ (right_ne_zero_of_mul hne)⟩
  refine ⟨hR.1, fun u => ?_⟩
  have := g0 _ (by
    have := sub_mem hR.2 hτ
    rwa [← Prod.mk.eta (p := Finset.sum _ _), Prod.mk_sub_mk, ← hfst, sub_self] at this)
  have := congrFun (sub_eq_zero.1 this) u
  rw [Prod.snd_sum, Finset.sum_apply] at this
  exact this

end GlobalTheory.TopFlip
end

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.LinGlob

open GlobalTheory.BigDat GlobalTheory.WeilM GlobalTheory.BigDat.GraphHeis

section Generic

variable {D : D7} {n d : ℕ} {Y : Spc D.host.F D.host.E n} {Z : Spc D.host.F D.host.E d}

theorem hTens_self {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A) (ε : A) (hε : ε * c ε = 0)
    (x : Matrix (Fin n) (Fin d) A) (hx : ε • x = x) : hTens c JA JB x x = 0 := by
  have hl : ∀ a b, ε * x a b = x a b := fun a b => congrFun (congrFun hx a) b
  unfold hTens
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  have u := congrArg c (hl k l)
  rw [map_mul] at u
  rw [← u, ← hl a b]
  linear_combination (x a b * JA a k * JB b l * c (x k l)) * hε

theorem vac_fixed_half {M : Model D.sp.cm.sig Y Z} {ψ : AddChar (AF D.host.F) ℂ} (hG : M.IsGood ψ) (v : Pl D.host.F) {a : AE D}
    (ha : a * cA D a = 0) {γ : Matrix (Fin n) (Fin d) (AE D)} (hγ : γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y Z v) (hh : a • γ = γ) :
    Acts (evFin D.host.F v) (M.co.rho ψ γ) (M.vac v) (M.vac v) := by
  obtain ⟨-, -, θ, -, hθ⟩ := hG.vac v
  have h1 := hθ γ hγ
  have h2 : hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Y.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Z.J) γ γ = 0 := hTens_self _ _ _ a ha γ hh
  unfold symp at h1
  rwa [h2, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_smul] at h1

variable {S X : HSp D} (p : Matrix (Fin n) (Fin d) (AE D) ≃ₗ[AE D] WO S X)

theorem isHalf_iff {a : AE D} {u : Matrix (Fin n) (Fin d) (AE D)} : IsHalf a (p u) ↔ a • u = u :=
  ⟨fun h => p.injective ((map_smul p a u).trans (smul_of_isHalf h)),
    fun h i j => congrFun (congrFun ((map_smul p a u).symm.trans (congrArg p h)) i) j⟩

theorem at_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {u : Matrix (Fin n) (Fin d) (AE D)}
    (hu : IsHalf b (p u)) : At (evFin D.host.F v) u := fun c hc =>
  smul_eq_zero_of_isHalf v hb (fun i j => congrFun (congrFun ((isHalf_iff p).1 hu) i) j) c hc

theorem smul_add_smul (v : Pl D.host.F) {a : AE D}
    (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) {u : Matrix (Fin n) (Fin d) (AE D)}
    (hu : At (evFin D.host.F v) u) : u = a • u + cA D a • u := by
  have h1 : (1 - GlobalTheory.LatVac.liftV v 1) • u = 0 :=
    hu _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  rw [← add_smul, hsum, algebraMap_smul, ← h1]

set_option maxHeartbeats 1600000 in
open Classical in

theorem datum_of_placeModel (M : Model D.sp.cm.sig Y Z) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hG : M.IsGood ψ)
    (hs : ∀ u w, symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Y.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Z.J) u w = symplO S X (p u) (p w))
    {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {LX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)}
    (hS : IsSelfDualC S LS) (hX : IsSelfDualC X LX) {κ : Type} (P : Finset κ) (pl : κ → Pl D.host.F) (hpl : Set.InjOn pl P)
    (a : κ → AE D) (ha : ∀ w ∈ P, IsSplitIdem D (a w) ∧
      a w + cA D (a w) = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (pl w) 1))
    {ε : AE D} (hεs : ε = ∑ w ∈ P, a w) (hεw : ∀ w ∈ P, ε * a w = a w) (hinf : infPart D ε = 0)
    (hlat : ∀ w ∈ P, ∀ u, At (evFin D.host.F (pl w)) u → p u ∈ latO S X (LS : Set _) (LX : Set _) (fun _ => True) →
      u ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y Z (pl w))
    (C : κ → Type) [∀ w, TopologicalSpace (C w)] [∀ w, AddGroup (C w)] (lin : ∀ w, WO S X → C w)
    (ladd : ∀ w x y, lin w (x + y) = lin w x + lin w y) (lon : ∀ w ∈ P, ∀ z, ∃ x, IsHalf (a w) x ∧ lin w x = z)
    (lsm : ∀ w ∈ P, ∀ x, lin w (a w • x) = lin w x)
    (lne : ∀ w ∈ P, ∀ w' ∈ P, w' ≠ w → ∀ x, IsHalf (a w) x → lin w' x = 0)
    (I : ∀ w, ((Fin n × Fin d → Fv D.host.F (pl w)) → ℂ) →ₗ[ℂ] (C w → ℂ))
    (hI : ∀ w ∈ P, IsLagrModel M ψ (pl w) {u | IsHalf (a w) (p u)} {u | IsHalf (cA D (a w)) (p u)} (fun u => lin w (p u)) (I w))
    {f₀ : WO S X → ℂ} {T : (WO S X → ℂ) →ₗ[ℂ] (WO S X → ℂ)}
    (hT : IsPlaceModel ψ (symplO S X) (heisO ψ S X) ε (latO S X (LS : Set _) (LX : Set _) fun _ => True) 1 f₀ T)
    {f : SInf D.host.F (Fin n × Fin d)} (hf : GlobalTheory.SquareAgree.IsDatum M ψ p (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) f₀)
    (φ : ∀ v : Pl D.host.F, (Fin n × Fin d → Fv D.host.F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hφ' : ∀ v, (∀ w ∈ P, pl w ≠ v) → φ v = M.vac v) :
    GlobalTheory.SquareAgree.IsDatum M ψ p (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ w ∈ P, I w (M.vac _) 0) • f) φ)
      (T fun x => if IsHalf ε x then ∏ w ∈ P, I w (φ (pl w)) (lin w x) else 0) := by
  set Λ := latO S X (LS : Set _) (LX : Set _) (fun _ => True) with hΛ
  have haa : ∀ w ∈ P, a w * a w = a w := fun w hw => (ha w hw).1.1
  have hac : ∀ w ∈ P, a w * cA D (a w) = 0 := fun w hw => (ha w hw).1.2.1
  have hcc : ∀ w ∈ P, cA D (a w) * cA D (a w) = cA D (a w) := fun w hw => by rw [← map_mul, haa w hw]
  have ha1 : ∀ w ∈ P, a w * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (pl w) 1) = a w := fun w hw => by
    rw [← (ha w hw).2, mul_add, haa w hw, hac w hw, add_zero]
  have hc1 : ∀ w ∈ P, cA D (a w) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (pl w) 1) = cA D (a w) := fun w hw => by
    rw [← (ha w hw).2, mul_add, mul_comm, hac w hw, hcc w hw, zero_add]
  have hfa : ∀ w ∈ P, finPart D (a w) ∈ intAE D := fun w hw =>
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa w hw])
  have hfc : ∀ w ∈ P, finPart D (cA D (a w)) ∈ intAE D := fun w hw =>
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc w hw])
  have hsm : ∀ w ∈ P, ∀ u, IsHalf (a w) (p (a w • u)) := fun w hw u => by
    rw [map_smul]; exact isHalf_smul_self (haa w hw) _
  have hv := fun w hw => lagr_vac (hI w hw) (hG.vac _).1 (hG.vac _).2.1 {u | p u ∈ Λ}
    (fun γ hγ hγ' => hγ'.elim
      (fun h => vac_fixed_half hG _ (hac w hw) (hlat w hw γ (at_of_isHalf p _ (ha1 w hw) h) hγ) ((isHalf_iff p).1 h))
      fun h => vac_fixed_half hG _ (splitIdem_conj (ha w hw).1).2.1 (hlat w hw γ (at_of_isHalf p _ (hc1 w hw) h) hγ)
        ((isHalf_iff p).1 h))
    (fun z => by
      obtain ⟨x, hx, rfl⟩ := lon w hw z
      obtain ⟨u, rfl⟩ := p.surjective x
      exact ⟨u, hx, rfl⟩)
    (fun x hx h => GlobalTheory.LatVac.mem_of_char hψ hS hX (map_infPart_of_isHalf _ (ha1 w hw) hx) fun l hl => by
      have := h (p.symm (cA D (a w) • l))
        (by
          show p (p.symm _) ∈ Λ
          rw [p.apply_symm_apply]
          exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ (hfc w hw) l hl)
        (by
          show IsHalf _ (p (p.symm _))
          rw [p.apply_symm_apply]
          exact isHalf_smul_self (hcc w hw) _)
      rwa [hs, p.apply_symm_apply, symplO_cA_smul, smul_of_isHalf hx] at this)
  set c := ∏ w ∈ P, I w (M.vac _) 0 with hc
  have hrho : ∀ {Φ g}, GlobalTheory.SquareAgree.IsDatum M ψ p Φ g → ∀ x,
      GlobalTheory.SquareAgree.IsDatum M ψ p (M.co.rho ψ x Φ) (heisO ψ S X (p x) g) := fun {Φ g} hD x =>
    ⟨GlobalTheory.HeisSchA.rho_mem_schA M ψ hstd x Φ hD.1, fun u => by
      rw [rho_rho M.co ψ u x Φ, thetaSum_smul, hD.2 (u + x)]
      unfold heisO symplOH
      rw [hs, map_add, invOf_two]⟩
  have hsmul : ∀ (b : ℂ) {Φ g}, GlobalTheory.SquareAgree.IsDatum M ψ p Φ g → GlobalTheory.SquareAgree.IsDatum M ψ p (b • Φ) (b • g) :=
    fun b {Φ g} hD => ⟨Submodule.smul_mem _ b hD.1, fun u => ((congrArg (thetaSum D.host.F) (show M.co.rho ψ u (b • Φ) = b • M.co.rho ψ u Φ from
      funext fun _ => mul_left_comm _ _ _)).trans (thetaSum_smul _ _ _)).trans
      (congrArg (b * ·) (hD.2 u))⟩
  let R : Submodule ℂ ((Matrix (Fin n) (Fin d) (AE D) → ℂ) × ((Fin n × Fin d → AF D.host.F) → ℂ)) :=
    { carrier := {q | ∃ g, IsSBHalf ε Λ g ∧ q.1 = g ∘ p ∧ GlobalTheory.SquareAgree.IsDatum M ψ p q.2 (T g)}
      zero_mem' := ⟨0, GlobalTheory.PlaceModelOnto.isSBHalf_zero _ _, rfl, by
        have := hsmul 0 hf
        rwa [zero_smul, zero_smul, ← map_zero T] at this⟩
      add_mem' := by
        rintro q q' ⟨g, h1, h2, h3⟩ ⟨g', h1', h2', h3'⟩
        refine ⟨g + g', GlobalTheory.PlaceModelOnto.isSBHalf_add h1 h1', by rw [Prod.fst_add, h2, h2']; rfl, add_mem h3.1 h3'.1, fun u => ?_⟩
        refine ((congrArg (thetaSum D.host.F) (show M.co.rho ψ u (q.2 + q'.2) = M.co.rho ψ u q.2 + M.co.rho ψ u q'.2 from
            funext fun _ => mul_add _ _ _)).trans
          (thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hstd u _ h3.1) (GlobalTheory.HeisSchA.rho_mem_schA M ψ hstd u _ h3'.1))).trans ?_
        rw [h3.2, h3'.2, map_add]
        rfl
      smul_mem' := by
        rintro b q ⟨g, h1, h2, h3⟩
        refine ⟨b • g, GlobalTheory.PlaceModelOnto.isSBHalf_smul b h1, by rw [Prod.smul_fst, h2]; rfl, ?_⟩
        rw [map_smul]
        exact hsmul b h3 }
  let H : AddSubgroup (Matrix (Fin n) (Fin d) (AE D)) := (GlobalTheory.PlaceModel.half S X ε).comap p.toLinearMap.toAddMonoidHom
  have hH : ∀ u, u ∈ (H : Set _) ↔ IsHalf ε (p u) := fun u => (GlobalTheory.PlaceModel.isHalf_iff _ _).symm
  have hA : ∀ w ∈ P, ∀ x : WO S X, IsHalf (a w) x → IsHalf ε x := fun w hw x hx => isHalf_mono (hεw w hw) hx
  have hA' : ∀ w ∈ P, ∀ x : WO S X, IsHalf (cA D (a w)) x → IsHalf (cA D ε) x := fun w hw x hx =>
    isHalf_mono (by rw [← RingHom.map_mul, hεw w hw]) hx
  have hbase : (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (M.vac _) (lin w (p u))) = (c • halfInd ε Λ) ∘ p := by
    funext u
    rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul, halfInd]
    by_cases hu : IsHalf ε (p u)
    · rw [Set.indicator_of_mem ((hH u).2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ ((lsm w hw _).symm.trans (congrArg (lin w) (map_smul p (a w) u).symm))).trans ((hv w hw).2 _ (hsm w hw u))]
      by_cases hl : p u ∈ Λ
      · rw [if_pos ⟨hl, hu⟩, mul_one]
        exact Finset.prod_congr rfl fun w hw => Set.indicator_of_mem (by
          show p (a w • u) ∈ Λ
          rw [map_smul]
          exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ (hfa w hw) _ hl) _
      · have : ∃ w ∈ P, p (a w • u) ∉ Λ := by
          by_contra! hall
          exact hl (mem_of_sum_smul (hεs ▸ hu) fun w hw => map_smul p (a w) u ▸ hall w hw)
        obtain ⟨w, hw, hn⟩ := this
        rw [Finset.prod_eq_zero hw (Set.indicator_of_notMem (s := {u | p u ∈ Λ}) hn _), if_neg fun h => hl h.1, mul_zero]
    · rw [Set.indicator_of_notMem (mt (hH u).1 hu), if_neg fun h => hu h.2, mul_zero]
  have hR := GlobalTheory.InductLagr.rel_of_vac M ψ hstd hG P pl hpl C
    (fun w => {u | IsHalf (a w) (p u)}) (fun w => {u | IsHalf (cA D (a w)) (p u)}) (fun w u => lin w (p u)) I H R (c • f)
    hI (fun w hw u hu => ⟨at_of_isHalf p _ (ha1 w hw) hu, (hH u).2 (hA w hw _ hu)⟩)
    (fun w hw u hu => at_of_isHalf p _ (hc1 w hw) hu)
    (fun w hw u hu => ⟨a w • u, hsm w hw u, cA D (a w) • u, by
      show IsHalf _ (p _)
      rw [map_smul]; exact isHalf_smul_self (hcc w hw) _, smul_add_smul _ (ha w hw).2 hu⟩)
    (fun w _ x _ u => by rw [map_add, ladd])
    (fun w hw w' hw' hne x hx u => by rw [map_add, ladd, lne w hw w' hw' hne _ hx, add_zero])
    (fun w hw u => ⟨a w • u, hsm w hw u, by rw [map_smul, lsm w hw], fun y hy => by
      rw [hs, hs, map_smul, ← symplO_cA_smul, smul_of_isHalf hy]⟩)
    (by
      rintro w hw x hx q ⟨g, h1, h2, h3⟩
      refine ⟨fun t => g (t + p x), sb_trans_latO hS.1 hX.1 hinf h1 (hA w hw _ hx), funext fun u => ?_, ?_⟩
      · rw [h2]; exact congrArg g (map_add p u x)
      · rw [hT.trans g h1 _ (hA w hw _ hx)]; exact hrho h3 x)
    (by
      rintro w hw x hx q ⟨g, h1, h2, h3⟩
      refine ⟨fun t => ψ (symplO S X t (p x)) * g t,
        sb_modul_latO hψ hS hX (GlobalTheory.PlaceVec.infPart_cA hinf) h1 (hA' w hw _ hx), funext fun u => ?_, ?_⟩
      · rw [h2]; exact congrArg (fun z => ψ z * g (p u)) (hs u x)
      · rw [hT.modul g h1 _ (hA' w hw _ hx)]; exact hrho h3 x)
    ⟨c • halfInd ε Λ, GlobalTheory.PlaceModelOnto.isSBHalf_smul c (GlobalTheory.isSBHalf_halfInd ε _), hbase, by
      rw [map_smul, (congrArg T (one_smul ℂ _).symm).trans hT.vac]
      exact (show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) M.vac = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac from
        funext fun _ => mul_assoc _ _ _) ▸ hsmul c hf⟩
    φ hφ hφ'
  obtain ⟨g, -, h2, h3⟩ := hR
  have : g = fun x => if IsHalf ε x then ∏ w ∈ P, I w (φ (pl w)) (lin w x) else 0 := funext fun x => by
    obtain ⟨u, rfl⟩ := p.surjective x
    refine (congrFun h2 u).symm.trans ?_
    dsimp only
    by_cases hu : IsHalf ε (p u)
    · rw [if_pos hu]; exact Set.indicator_of_mem ((hH u).2 hu) _
    · rw [if_neg hu]; exact Set.indicator_of_notMem (mt (hH u).1 hu) _
  exact this ▸ h3

end Generic

section Arith

variable {D : D7}

theorem exists_den (w : Pl D.host.E)
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    ∃ r : 𝓞 D.host.F, r ∉ (w.under (𝓞 D.host.F)).asIdeal ∧
      ∀ a ∈ D.host.AA, star (algebraMap D.host.F D.host.E r * a) ∈ D.host.AA := by
  have hN : ∀ k : ℕ, k ∣ D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK →
      (k : 𝓞 D.host.F) ∉ (w.under (𝓞 D.host.F)).asIdeal := by
    rintro k ⟨m, hm⟩ hk
    have : (k : 𝓞 D.host.E) ∈ w.asIdeal := by
      have := Ideal.mem_comap.1 hk
      rwa [map_natCast] at this
    exact hw (by rw [hm, Nat.cast_mul]; exact w.asIdeal.mul_mem_right _ this)
  haveI := (w.under (𝓞 D.host.F)).isPrime
  have hnot : ¬ D.host.𝔟.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ (w.under (𝓞 D.host.F)).asIdeal := by
    intro hle
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ _ hle
    have hd : Q ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := by
      rw [D.host.𝔟_spec.1]
      exact (Ideal.dvd_iff_le.2 hQ).mul_right _
    have key : ∀ k : ℕ, (k : 𝓞 D.host.E) ∈ Q → (k : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := fun k hk => by
      rw [← hQc, Ideal.mem_comap, map_natCast]; exact hk
    exact hN (D.host.QS * D.host.q) ⟨D.host.d * Ideal.absNorm D.host.ccK, by ring⟩
      (key _ (by exact_mod_cast D.host.der.diffSupport _ hQp hd))
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
  have hNA : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
    have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
      have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
      rwa [map_natCast] at this
    have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 D.host.E))).2 ⟨_, h1, rfl⟩)
      (Formalism.L2.Pj.one_mem_inverse_halfDifferent D)
    rwa [mul_one, map_natCast] at this
  refine ⟨(Ideal.absNorm D.host.ccK : ℕ) * z, fun h => ?_, fun a ha => ?_⟩
  · rcases (w.under (𝓞 D.host.F)).isPrime.mem_or_mem h with h | h
    exacts [hN _ (Dvd.intro_left _ rfl) h, hzP h]
  · have ha0 : a ∈ D.host.AA0 := by
      have : D.host.AA ≤ D.host.AA0 := (mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans (one_mul _).le
      exact this ha
    unfold Host.AA0 at ha0
    rw [FractionalIdeal.mem_inv_iff hB] at ha0
    obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).1 (ha0 _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hz, rfl⟩))
    have hint : IsIntegral ℤ (star (y : D.host.E)) := y.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom
    have := (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem ⟨_, hint⟩ hNA
    convert this using 1
    have e : algebraMap D.host.F D.host.E (((Ideal.absNorm D.host.ccK : ℕ) * z : 𝓞 D.host.F) : D.host.F) * a =
        (y : D.host.E) * (Ideal.absNorm D.host.ccK : ℕ) := by
      have : (y : D.host.E) = a * algebraMap D.host.F D.host.E (z : D.host.F) := hy
      rw [this]
      push_cast
      exact (mul_rotate _ _ _).trans (congrArg (· * _) (mul_comm _ _))
    rw [e, star_mul', star_natCast]
    rfl

theorem smul_gen_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (v : Pl F) {α : Af F}
    (hα : α ∈ intAf F) {x : Fin n → E} (hx : x ∈ X.L) {y : Fin d → E} {r : 𝓞 F} (hr : r ∉ v.asIdeal)
    (hy : algebraMap F E r • y ∈ Y.L) :
    GlobalTheory.LatVac.liftV v 1 • pairA F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (vecMulVec x y) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := by
  have hr0 : (r : F) ≠ 0 := fun h => hr (by rw [RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  rw [smul_smul]
  refine AddSubgroup.subset_closure ⟨(r : F)⁻¹ • (GlobalTheory.LatVac.liftV v 1 * pairA F 0 α), ?_, ?_, x, hx, _, hy, ?_⟩
  · intro u hu
    rw [smul_comm, smul_eq_mul u, ← mul_assoc, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v 1 u hu, zero_mul, smul_zero]
  · rw [map_smul, map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul, Algebra.smul_def]
    refine mul_mem ?_ (hα v)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
    have : Valued.v (algebraMap F (Fv F v) r) = 1 := by
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_
      exact (v.valuation_of_algebraMap r).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hr)
    rw [this, inv_one]
  · ext p q
    have e : ∀ (β : AF F) (M : Matrix (Fin n) (Fin d) E), (β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F M) p q = β ⊗ₜ[F] M p q := fun β M => by
      change β • ((1 : AF F) ⊗ₜ[F] M p q) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, e, vecMulVec_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm,
      ← Algebra.smul_def, ← TensorProduct.smul_tmul, smul_smul, mul_inv_cancel₀ hr0, one_smul]

theorem frMapO_cpt (S X : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βX : GL (Fin X.rank) (EAf D)) (w : Pl D.host.E) (x : WO S X) :
    (frMapO S X βS βX x).map (cpt w) = (βX⁻¹).val.map (cpt w) * x.map (atW w) * βS.val.map (cpt w) := by
  unfold frMapO
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem frMapO_cpt_surj (S X : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βX : GL (Fin X.rank) (EAf D)) (w : Pl D.host.E)
    (z : Matrix (Fin X.rank) (Fin S.rank) (Kw w)) : ∃ x : WO S X, IsHalf (atPl w 1) x ∧ (frMapO S X βS βX x).map (cpt w) = z := by
  refine ⟨(βX.val.map (cpt w) * z * (βS⁻¹).val.map (cpt w)).map (atPl w), fun a b => atPl_one_mul w _, ?_⟩
  have m : ((βX.val.map (cpt w) * z * (βS⁻¹).val.map (cpt w)).map (atPl w)).map (atW w) =
      βX.val.map (cpt w) * z * (βS⁻¹).val.map (cpt w) := Matrix.ext fun a b => atW_atPl_self w _
  rw [frMapO_cpt, m, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

end Arith

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

def ptEquiv {i j : ℕ} (e : Num G i j) : Pt G i j ≃ₗ[AE D] WO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) :=
  { GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coordsEquiv (m := (spX G i j).rank) (e.symm.trans finSumFinEquiv).symm
      (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram)
      (one_smul D.host.E (GlobalTheory.Grid.sgn true (spW G i j)).gram ▸
        GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.isUnit_det_incM (GlobalTheory.Grid.sgn true (spW G i j)) 1 one_ne_zero) with
    map_smul' := fun c u => Matrix.smul_mul c (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) _ }

theorem ptEquiv_apply {i j : ℕ} (e : Num G i j) (u : Pt G i j) : ptEquiv e u = ptA e u := rfl

theorem symp_ptA {i j : ℕ} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (u w : Pt G i j) :
    sympPt Γ u w = symplO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (ptEquiv e u) (ptEquiv e w) := by
  refine GlobalTheory.SquareAgree.HeisCov.symp_eq true (spW G i j) (spX G i j) (e.symm.trans finSumFinEquiv).symm _ _ hW ?_ (ptA e)
    (fun u => ?_) u w
  · rw [hWW, GlobalTheory.Doubling.gram_hsum]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk GlobalTheory.Doubling.blkMat
    congr 1
    ext a b
    obtain ⟨a | a, rfl⟩ := e.surjective a <;> obtain ⟨b | b, rfl⟩ := e.surjective b <;> simp
  · rw [← GlobalTheory.SquareAgree.HeisCov.sgn_gram]
    rfl

theorem ptEquiv_gen {i j : ℕ} (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW G i j).rank → D.host.E)
    (t : Fin (spX G i j).rank → D.host.E) :
    ptEquiv e (β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (a • t ∘ e.symm.trans finSumFinEquiv))) =
      Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (GlobalTheory.Grid.neg (spW G i j)).gram k j') := by
  ext p q
  rw [ptEquiv_apply, ptA, Matrix.mul_apply]
  simp only [of_apply, Finset.mul_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [submatrix_apply, transpose_apply, smul_incM_apply, vecMulVec_apply, Pi.smul_apply, Function.comp_apply,
    Equiv.apply_symm_apply]
  change (β ⊗ₜ[D.host.F] (star (s k) * (a * t p))) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (GlobalTheory.Grid.neg (spW G i j)).gram k q) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem mem_latAtV {t : T} {i j : ℕ} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (w : Pl D.host.E)
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (u : Pt G i j)
    (hat : At (evFin D.host.F (w.under (𝓞 D.host.F))) u) (hu : ptEquiv e u ∈ homLatA G i j) :
    u ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W (w.under (𝓞 D.host.F)) := by
  obtain ⟨r, hr, hra⟩ := exists_den w hw
  have e1 : GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV _ 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  rw [← e1, ← (ptEquiv e).symm_apply_apply u]
  refine map_mem_of_closure ((DistribMulAction.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1)).comp
    (ptEquiv e).symm.toLinearMap.toAddMonoidHom) ?_ hu
  rintro _ ⟨α, hα, -, a, ha, s, hs, y, hy, rfl⟩
  refine (congrArg (fun z => GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1 • z ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W _)
    ((ptEquiv e).symm_apply_eq.2 (ptEquiv_gen e (pairA _ 0 α) a s y).symm)).mpr
    (smul_gen_mem _ _ _ hα (h.1.ge (star_mem_conjSub hs)) hr (h.2.1.ge ?_))
  rw [smul_smul, GlobalTheory.SkewLat.mem_pairLat]
  simp only [Pi.smul_apply, Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  refine ⟨smul_mem_scLat_of_mem
    ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) ha) hy.1, ?_⟩
  have := star_mem_conjSub (smul_mem_scLat_of_mem (hra a ha) (star_mem_conjSub hy.2))
  rwa [star_smul, star_star, star_star] at this

end Grid

set_option maxHeartbeats 1600000 in

theorem isDatum_linA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ (ρ : RealMatch W) f₀,
      GlobalTheory.SquareAgree.IsDatum Γ.M W.ψ (ptA e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) (vacA ρ i j) →
      ∀ ι : ∀ w, ToA G t i j w, (∀ w ∈ locPl G t, IsLinModelA W B t e Γ w (ι w)) →
      ∀ ε, IsIdemSum ε (locPl G t) → ∀ Ξ F, IsLinA B t i j ρ ε Ξ F →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ξ w) →
        GlobalTheory.SquareAgree.IsDatum Γ.M W.ψ (ptA e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0) • f₀) φ) F := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti ρ f₀ hdat ι hι ε hε Ξ F hF φ hφ hΞ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hid, hsumid⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hF
  have sW : IsSelfDualC (GlobalTheory.Grid.neg (spW G i j)) (G.Λ (.grid (i + 1) (j + 1))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  have sX : IsSelfDualC (spX G i j) (latX G i j) := GlobalTheory.Twist.OrthSum.selfDual_hsum
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd
  have key := datum_of_placeModel (ptEquiv e) Γ.M W.ψ_std hstd hG (symp_ptA e Γ h.JW h.JWW) sW sX (locPl G t)
    (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) (fun w => atPl w 1) hid hεs hεw (GlobalTheory.PlaceVec.idemSum_infPart hε)
    (fun w hw => mem_latAtV hti w (hst.2 w hw)) (MatA G t i j) (linA B t i j)
    (fun w x y => by
      unfold linA
      rw [frMapO_cpt, frMapO_cpt, frMapO_cpt, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
      rfl)
    (fun w _ z => by
      obtain ⟨x, hx, hz⟩ := frMapO_cpt_surj (spW G i j) (spX G i j) (B.β (i + 1) (j + 1)) (frX B i j) w
        ((reindex (finCongr (rankW G t i j w)) (colX G t i j w)).symm z)ᵀ
      refine ⟨x, hx, ?_⟩
      unfold linA
      rw [hz, transpose_transpose, Equiv.apply_symm_apply])
    (fun w _ x => by
      unfold linA
      rw [frMapO_cpt, frMapO_cpt, map_atW_smul])
    (fun w _ w' _ hne x hx => by
      have h₁ : x.map (atW w') = 0 := Matrix.ext fun a b =>
        (congrArg (atW w') (hx a b).symm).trans (by rw [map_mul, atW_atPl_ne hne, zero_mul]; rfl)
      unfold linA
      rw [frMapO_cpt, h₁, Matrix.mul_zero, Matrix.zero_mul]
      rfl)
    ι hι hT₀ hdat φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.2.2.1 v).1 hm; hv w hw e
  rw [hall T₀ hT₀]
  refine (congrArg (fun g => GlobalTheory.SquareAgree.IsDatum Γ.M W.ψ (ptA e) _ (T₀ g)) (funext fun x => ?_)).mpr key
  unfold prodA
  split_ifs
  · exact Finset.prod_congr rfl fun w hw => congrFun (hΞ w hw).symm _
  · rfl

end GlobalTheory.TopFlip.LinGlob

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negW_local_functions_theta_pure_tensor : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ (ρ : RealMatch W) f₀,
      GlobalTheory.SquareAgree.IsDatum Γ.M W.ψ (ptA e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) (vacA ρ i j) →
      ∀ ι : ∀ w, ToA G t i j w, (∀ w ∈ locPl G t, IsLinModelA W B t e Γ w (ι w)) →
      ∀ ε, IsIdemSum ε (locPl G t) → ∀ Ξ F, IsLinA B t i j ρ ε Ξ F →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ξ w) →
        GlobalTheory.SquareAgree.IsDatum Γ.M W.ψ (ptA e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0) • f₀) φ) F := by
  atlas_forward_decl GlobalTheory.TopFlip.LinGlob.isDatum_linA
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.LinSmall

open GlobalTheory.SmallDat (PtS IxS sympS thetaS heisS thetaS_rho thetaS_smul)
open GlobalTheory.BigDat (atW atW_atPl_self atW_atPl_ne atPl_one_mul symplO_cA_smul isHalf_smul_self
  smul_of_isHalf smul_eq_zero_of_isHalf map_infPart_of_isHalf)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (latAtV)

section Sb

variable {D : D7}

theorem sb_zero {m n : ℕ} (a : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf a Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem sb_smul {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf a Λ Φ) : IsSBHalf a Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (hne t ht), k, hk,
    fun u hu hu' t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hu' t], fun t ht => h3 t (hne t ht)⟩

theorem sb_add {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf a Λ Φ) (h' : IsSBHalf a Λ Ψ) : IsSBHalf a Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have hne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf a u → IsHalf a (j • u) := fun j u hu p q => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu p q]
  refine ⟨fun t ht => (hne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (hh _ _ hu') t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (hh _ _ hu') t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem exists_nat_conj {w : Pl D.host.E}
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    ∃ m : ℕ, (m : 𝓞 D.host.E) ∉ w.asIdeal ∧ ∀ a ∈ D.host.AA, star ((m : D.host.E) * a) ∈ D.host.AA := by
  obtain ⟨p, hp, hP⟩ := GlobalTheory.HalfCompare.exists_prime_under w
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hb
  refine ⟨Ideal.absNorm D.host.ccK * Ideal.absNorm D.host.𝔟, fun h => hw ((hP _).2 ?_), fun a ha => ?_⟩
  · rcases hp.dvd_mul.1 ((hP _).1 h) with h | h
    · exact h.mul_left _
    · exact (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 h).mul_right _).mul_right _
  · have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
      have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
      rwa [map_natCast] at this
    have h2 : (1 : D.host.E) ∈ D.host.AA0 := by
      rw [Host.AA0, FractionalIdeal.mem_inv_iff h0]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    have h3 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 D.host.E)) h1) h2
    rw [mul_one, map_natCast] at h3
    have h4 : a ∈ D.host.AA0 := by
      have : D.host.AA ≤ D.host.AA0 := by
        rw [Host.AA]
        calc _ ≤ 1 * D.host.AA0 := by gcongr; exact FractionalIdeal.coeIdeal_le_one
          _ = _ := one_mul _
      exact this ha
    rw [Host.AA0, FractionalIdeal.mem_inv_iff h0] at h4
    have h5 := h4 _ (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.𝔟))
    rw [map_natCast] at h5
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h5
    have h6 : IsIntegral ℤ (star (r : D.host.E)) :=
      (map_isIntegral_int (starRingEnd D.host.E) (RingOfIntegers.isIntegral_coe r) :)
    have h7 := D.host.AA.1.smul_mem (⟨_, h6⟩ : 𝓞 D.host.E) h3
    have e : star (((Ideal.absNorm D.host.ccK * Ideal.absNorm D.host.𝔟 : ℕ) : D.host.E) * a) =
        star (r : D.host.E) * (Ideal.absNorm D.host.ccK : ℕ) := by
      rw [show (r : D.host.E) = _ from hr, Nat.cast_mul, mul_assoc, star_mul', star_natCast, mul_comm a, mul_comm]
    rw [e]
    exact h7

theorem inv_nat_mem {w : Pl D.host.E} {m : ℕ} (hm : (m : 𝓞 D.host.E) ∉ w.asIdeal) :
    (m : Fv D.host.F (w.under (𝓞 D.host.F))) ≠ 0 ∧
      (m : Fv D.host.F (w.under (𝓞 D.host.F)))⁻¹ ∈ (w.under (𝓞 D.host.F)).adicCompletionIntegers D.host.F := by
  set v := w.under (𝓞 D.host.F)
  have h1 : (m : 𝓞 D.host.F) ∉ v.asIdeal := fun h => hm (by
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m ∈ w.asIdeal := h
    rwa [map_natCast] at this)
  have h2 : Valued.v (m : v.adicCompletion D.host.F) = 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 D.host.F) D.host.F m)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h1, map_natCast] at this
    rw [← this]
    congr 1
    exact (map_natCast (algebraMap D.host.F (v.adicCompletion D.host.F)) m).symm
  refine ⟨fun h => ?_, ?_⟩
  · rw [show (m : v.adicCompletion D.host.F) = 0 from h, map_zero] at h2
    exact zero_ne_one h2
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h2, inv_one]

end Sb

section Pt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {i j : ℕ}

def ptE (e : Num G i j) : PtS G i j ≃ₗ[AE D] WO (spW₁ G i j) (spX G i j) :=
  { GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coordsEquiv (e.symm.trans finSumFinEquiv).symm (incM (spW₁ G i j).gram)
      (by simpa only [one_smul] using GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.isUnit_det_incM (spW₁ G i j) 1 one_ne_zero) with
    map_smul' := fun a u => Matrix.smul_mul a (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (spW₁ G i j).gram) }

theorem ptE_apply (e : Num G i j) (u : PtS G i j) : ptE e u = ptB e u := rfl

theorem ptB_add (e : Num G i j) (u x : PtS G i j) : ptB e (u + x) = ptB e u + ptB e x := map_add (ptE e) u x

theorem ptB_smul (e : Num G i j) (a : AE D) (u : PtS G i j) : ptB e (a • u) = a • ptB e u := map_smul (ptE e) a u

theorem ptB_symm (e : Num G i j) (y : WO (spW₁ G i j) (spX G i j)) : ptB e ((ptE e).symm y) = y := (ptE e).apply_symm_apply y

theorem smul_of_half (e : Num G i j) {a : AE D} {u : PtS G i j} (h : IsHalf a (ptB e u)) : a • u = u :=
  (ptE e).injective ((ptB_smul e a u).trans (smul_of_isHalf h))

theorem sympS_ptB (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (u x : PtS G i j) :
    sympS Γ u x = symplO (spW₁ G i j) (spX G i j) (ptB e u) (ptB e x) := by
  refine GlobalTheory.SquareAgree.HeisCov.symp_eq false (spW₁ G i j) (spX G i j) (finSumFinEquiv.symm.trans e) Γ.V'.J Γ.W.J hW ?_ (ptB e)
    (fun u => ?_) u x
  · rw [hWW, GlobalTheory.Doubling.gram_hsum, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram]
    congr 1
    ext a b
    obtain ⟨a | a, rfl⟩ := e.surjective a <;> obtain ⟨b | b, rfl⟩ := e.surjective b <;>
      simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, GlobalTheory.Doubling.blkMat]
  · rw [if_neg Bool.false_ne_true, one_smul]
    rfl

theorem heisS_ptB (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (ψ : AddChar (AF D.host.F) ℂ) (x : PtS G i j)
    (f : WO (spW₁ G i j) (spX G i j) → ℂ) :
    heisS Γ ψ x (fun u => f (ptB e u)) = fun u => heisO ψ (spW₁ G i j) (spX G i j) (ptB e x) f (ptB e u) := by
  funext u
  unfold heisS heisO symplOH
  rw [sympS_ptB e Γ hW hWW, ← ptB_add, GlobalTheory.BigDat.invOf_two]

theorem at_of_half (e : Num G i j) (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {u : PtS G i j} (hu : IsHalf b (ptB e u)) :
    At (evFin D.host.F v) u := fun c hc =>
  smul_eq_zero_of_isHalf v hb (x := u) (fun p q => congrFun (congrFun (smul_of_half e hu) p) q) c hc

theorem liftV_smul {v : Pl D.host.F} {u : PtS G i j} (hu : At (evFin D.host.F v) u) : GlobalTheory.LatVac.liftV v 1 • u = u := by
  have := hu (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem symm_gen (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW₁ G i j).rank → D.host.E)
    (r : Fin (spX G i j).rank → D.host.E) :
    (ptE e).symm (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spW₁ G i j).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) fun q => a * r (finSumFinEquiv (e.symm q))) := by
  rw [LinearEquiv.symm_apply_eq, ← GlobalTheory.BigDat.mulG_divG (spW₁ G i j) (Matrix.of _)]
  refine congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (spW₁ G i j)) (Matrix.ext fun p q => ?_)
  refine (GlobalTheory.BigDat.divG_gen (spW₁ G i j) β a s r p q).trans ?_
  rw [submatrix_apply, transpose_apply, GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, mul_comm]
  simp

theorem mem_latAtV {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) {w : Pl D.host.E}
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {u : PtS G i j}
    (hu : At (evFin D.host.F (w.under (𝓞 D.host.F))) u) (hl : ptB e u ∈ homLatB G i j) :
    u ∈ latAtV Γ.V' Γ.W (w.under (𝓞 D.host.F)) := by
  obtain ⟨m, hm, hA⟩ := exists_nat_conj hw
  obtain ⟨hm0, hmi⟩ := inv_nat_mem hm
  set v := w.under (𝓞 D.host.F)
  have key : ∀ y ∈ homLatB G i j, GlobalTheory.LatVac.liftV v 1 • m • (ptE e).symm y ∈ latAtV Γ.V' Γ.W v := fun y hy => by
    refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
      ((DistribMulAction.toAddMonoidHom (PtS G i j) m).comp (ptE e).symm.toLinearMap.toAddMonoidHom)) ?_ hy
    rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
    have e1 : m • (pairA D.host.F 0 α) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F
        (vecMulVec (star s) fun q => a * r (finSumFinEquiv (e.symm q))) = (pairA D.host.F 0 α) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F
        (vecMulVec (star s) fun q => (m * a) * r (finSumFinEquiv (e.symm q))) := by
      ext p q
      rw [Matrix.smul_apply, GlobalTheory.BigDat.smul_incM_apply, GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, vecMulVec_apply,
        ← TensorProduct.tmul_smul, nsmul_eq_mul]
      congr 1
      ring
    refine (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v)
      ((congrArg (m • ·) (symm_gen e (pairA _ 0 α) a s r)).trans e1)).mpr
      (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hs)) (h.1.2.1.ge ?_))
    rw [GlobalTheory.SkewLat.mem_pairLat]
    simp only [Equiv.symm_apply_apply]
    have hma : (m : D.host.E) * a ∈ D.host.AA := by
      have := D.host.AA.1.smul_mem (m : 𝓞 D.host.E) ha
      rwa [Algebra.smul_def, map_natCast] at this
    refine ⟨GlobalTheory.BigDat.smul_mem_scLat_of_mem hma hr.1, ?_⟩
    have := GlobalTheory.BigDat.star_mem_conjSub (GlobalTheory.BigDat.smul_mem_scLat_of_mem (hA a ha) (GlobalTheory.BigDat.star_mem_conjSub hr.2))
    rwa [star_smul, star_star, star_star] at this
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable Γ.V' Γ.W v).2 _ hmi _ (key _ hl)
  rw [← ptE_apply, LinearEquiv.symm_apply_apply, smul_comm _ m, liftV_smul hu, smul_comm, ← smul_assoc, ← map_nsmul,
    nsmul_eq_mul, mul_inv_cancel₀ hm0, liftV_smul hu] at h1
  exact h1

end Pt

section Co

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

def atC (w : Pl D.host.E) : AE D →+* Kw w := (atW w).comp (cA D)

theorem atC_cA (w : Pl D.host.E) (a : AE D) : atC w (cA D a) = atW w a := congrArg (atW w) (GlobalTheory.DualPairCheck.cA_cA a)

theorem adj_eq (S X : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βX : GL (Fin X.rank) (EAf D)) (w : Pl D.host.E) (y : WO S X) :
    (frMapAdj S X βS βX y).map (cpt w) = ((βS⁻¹).val.map (cpt w) * ((S.gram⁻¹).map (incA D)).map (atW w)) *
      ((y : Matrix (Fin X.rank) (Fin S.rank) (AE D)).map (atC w))ᵀ * ((X.gram.map (incA D)).map (atW w) * βX.val.map (cpt w)) := by
  unfold frMapAdj
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := toEAf D), Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rfl

theorem adj_surj (S X : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βX : GL (Fin X.rank) (EAf D)) (w : Pl D.host.E)
    (z : Matrix (Fin S.rank) (Fin X.rank) (Kw w)) :
    ∃ y : WO S X, IsHalf (cA D (atPl w 1)) y ∧ (frMapAdj S X βS βX y).map (cpt w) = z := by
  have h1 : ((βS⁻¹).val.map (cpt w) * ((S.gram⁻¹).map (incA D)).map (atW w)) *
      ((S.gram.map (incA D)).map (atW w) * βS.val.map (cpt w)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.map _ (atW w)), ← Matrix.map_mul, GlobalTheory.SquareAgree.HeisCov.gram_inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.map_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((βX⁻¹).val.map (cpt w) * ((X.gram⁻¹).map (incA D)).map (atW w)) *
      ((X.gram.map (incA D)).map (atW w) * βX.val.map (cpt w)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.map _ (atW w)), ← Matrix.map_mul, GlobalTheory.SquareAgree.HeisCov.gram_inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.map_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Matrix (Fin S.rank) (Fin X.rank) (Kw w), y₀ = ((S.gram.map (incA D)).map (atW w) * βS.val.map (cpt w)) * z *
    ((βX⁻¹).val.map (cpt w) * ((X.gram⁻¹).map (incA D)).map (atW w)) := ⟨_, rfl⟩
  refine ⟨y₀ᵀ.map fun a => cA D (atPl w a), fun p q => ?_, ?_⟩
  · rw [map_apply, ← RingHom.map_mul, atPl_one_mul]
  · have e : ((y₀ᵀ.map fun a => cA D (atPl w a)).map (atC w))ᵀ = y₀ :=
      Matrix.ext fun p q => (atC_cA w _).trans (atW_atPl_self w _)
    rw [adj_eq, e, hy₀, ← Matrix.mul_assoc _ (_ * z), ← Matrix.mul_assoc _ _ z, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
      Matrix.mul_one]

variable (B : Frames G) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E)

theorem linB_add (x y : WO (spW₁ G i j) (spX G i j)) : linB B t i j w (x + y) = linB B t i j w x + linB B t i j w y := by
  unfold linB
  rw [adj_eq, adj_eq, adj_eq, Matrix.map_add _ (map_add _), transpose_add, Matrix.mul_add, Matrix.add_mul]
  rfl

theorem linB_surj (z : MatB G t i j w) : ∃ y, IsHalf (cA D (atPl w 1)) y ∧ linB B t i j w y = z := by
  obtain ⟨y, h1, h2⟩ := adj_surj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) w
    ((reindex (finCongr (rankW₁ G t i j w)) (colX G t i j w)).symm z)
  exact ⟨y, h1, (congrArg _ h2).trans (Equiv.apply_symm_apply _ z)⟩

theorem linB_smul (y : WO (spW₁ G i j) (spX G i j)) : linB B t i j w (cA D (atPl w 1) • y) = linB B t i j w y := by
  have e : (cA D (atPl w 1) • y).map (atC w) = y.map (atC w) := Matrix.ext fun p q => by
    rw [map_apply, map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, atC_cA, atW_atPl_self, one_mul]
  unfold linB
  rw [adj_eq, adj_eq, e]

theorem linB_ne {w' : Pl D.host.E} (h : w ≠ w') {y : WO (spW₁ G i j) (spX G i j)} (hy : IsHalf (cA D (atPl w' 1)) y) :
    linB B t i j w y = 0 := by
  have e : y.map (atC w) = 0 := Matrix.ext fun p q => by
    rw [map_apply, ← hy p q, RingHom.map_mul, atC_cA, atW_atPl_ne h, zero_mul, Matrix.zero_apply]
  unfold linB
  rw [adj_eq, e, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
  rfl

end Co

section Vac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {i j : ℕ}

theorem vac_fixed_half {W : G.Weil} {M : Vol G} {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : Chars D.host.F D.host.E} {om : Rep D.sp.cm.sig Γ.V Γ.W} {om' : Rep D.sp.cm.sig Γ.V' Γ.W}
    (h : IsTripleOf W M t i j e Bs Γ X) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') {v : Pl D.host.F} {γ : PtS G i j}
    (hγ : γ ∈ latAtV Γ.V' Γ.W v) {b : AE D} (hb : b * cA D b = 0) (hh : IsHalf b (ptB e γ)) :
    Acts (evFin D.host.F v) (Γ.M'.co.rho W.ψ γ) (Γ.M'.vac v) (Γ.M'.vac v) := by
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac v
  have h1 := hθ γ hγ
  have h0 : GlobalTheory.WeilM.hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
    have hl : ∀ p q, b * γ p q = γ p q := fun p q => congrFun (congrFun (smul_of_half e hh) p) q
    unfold GlobalTheory.WeilM.hTens
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun k _ =>
      Finset.sum_eq_zero fun l _ => ?_
    have u : cA D b * cA D (γ k l) = cA D (γ k l) := by rw [← RingHom.map_mul, hl]
    change γ p q * _ * _ * cA D (γ k l) = 0
    rw [← u, ← hl p q]
    linear_combination (γ p q * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J p k * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J q l *
      cA D (γ k l)) * hb
  unfold GlobalTheory.WeilM.symp at h1
  rw [h0, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_smul, h.ψ] at h1
  exact h1

theorem halves (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (spW₁ G i j) (G.Λ (.grid i j))) (hX : IsSelfDualC (spX G i j) (latX G i j)) (v : Pl D.host.F) {c : AE D}
    (hc : IsSplitIdem D c) (hsum : c + cA D c = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) :
    (∀ u : PtS G i j, IsHalf (cA D c) (ptB e u) → At (evFin D.host.F v) u) ∧
    (∀ u : PtS G i j, IsHalf c (ptB e u) → At (evFin D.host.F v) u) ∧
    (∀ u : PtS G i j, At (evFin D.host.F v) u → ∃ x, IsHalf (cA D c) (ptB e x) ∧ ∃ y, IsHalf c (ptB e y) ∧ u = x + y) ∧
    (∀ x : PtS G i j, IsHalf (cA D c) (ptB e x) → (∀ y, At (evFin D.host.F v) y ∧ ptB e y ∈ homLatB G i j → IsHalf c (ptB e y) →
      ψ (sympS Γ x y) = 1) → At (evFin D.host.F v) x ∧ ptB e x ∈ homLatB G i j) ∧
    ∀ u : PtS G i j, IsHalf (cA D c) (ptB e (cA D c • u)) ∧
      (∀ y, IsHalf c (ptB e y) → sympS Γ u y = sympS Γ (cA D c • u) y) ∧
      (ptB e u ∈ homLatB G i j → ptB e (cA D c • u) ∈ homLatB G i j) := by
  obtain ⟨haa, hac, -⟩ := hc
  have hcc : cA D c * cA D c = cA D c := by rw [← RingHom.map_mul, haa]
  have hca : cA D c * c = 0 := by rw [mul_comm, hac]
  have ha1 : c * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = c := by
    rw [← hsum, mul_add, haa, hac, add_zero]
  have hc1 : cA D c * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D c := by
    rw [← hsum, mul_add, hca, hcc, zero_add]
  have hfa : finPart D c ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa])
  have hfc : finPart D (cA D c) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
  have hp : ∀ {b : AE D}, b * b = b → ∀ u : PtS G i j, IsHalf b (ptB e (b • u)) := fun hb u => by
    rw [ptB_smul]; exact isHalf_smul_self hb _
  have hs : ∀ x y : WO (spW₁ G i j) (spX G i j), symplO _ _ x (c • y) = symplO _ _ (cA D c • x) y := fun x y => by
    rw [← symplO_cA_smul, GlobalTheory.DualPairCheck.cA_cA]
  refine ⟨fun u hu => at_of_half e v hc1 hu, fun u hu => at_of_half e v ha1 hu, fun u hu =>
    ⟨_, hp hcc u, _, hp haa u, ?_⟩, fun x hx hψ => ⟨at_of_half e v hc1 hx, ?_⟩, fun u => ⟨hp hcc u, fun y hy => ?_, fun hu => ?_⟩⟩
  · rw [← add_smul, add_comm (cA D c), hsum, algebraMap_smul, liftV_smul hu]
  · refine GlobalTheory.LatVac.mem_of_char hstd hS hX (map_infPart_of_isHalf v hc1 hx) fun l hl => ?_
    have := hψ (c • (ptE e).symm l) ⟨at_of_half e v ha1 (hp haa _), by
      rw [ptB_smul, ptB_symm]; exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa l hl⟩ (hp haa _)
    rwa [sympS_ptB e Γ hW hWW, ptB_smul, ptB_symm, hs, smul_of_isHalf hx] at this
  · rw [sympS_ptB e Γ hW hWW, sympS_ptB e Γ hW hWW, ptB_smul, ← hs, smul_of_isHalf hy]
  · rw [ptB_smul]
    exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc _ hu

end Vac

set_option maxHeartbeats 1600000 in

theorem isDatum_linB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X → ∀ (ρ : RealMatch W) f₀,
      GlobalTheory.SquareAgree.IsDatum Γ.M' W.ψ (ptB e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) (vacB ρ i j) →
      ∀ ι : ∀ w, ToB G t i j w, (∀ w ∈ locPl G t, IsLinModelB W B t e Γ w (ι w)) →
      ∀ ε, IsIdemSum ε (locPl G t) → ∀ Ψ F, IsLinB B t i j ρ ε Ψ F →
      ∀ φ, IsFinPart Γ.M' X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        GlobalTheory.SquareAgree.IsDatum Γ.M' W.ψ (ptB e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ w ∈ locPl G t, ι w (Γ.M'.vac _) 0) • f₀) φ) F := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti ρ f hf₀ I hI ε hε Ψ F hF φ hφ hΨ
  classical
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  have hadd : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (IxS G i j), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (IxS G i j),
      thetaS Γ W.ψ (Φ + Φ') = thetaS Γ W.ψ Φ + thetaS Γ W.ψ Φ' := fun Φ hΦ Φ' hΦ' => funext fun u =>
    (tsum_congr fun _ => mul_add _ _ _).trans
      ((GlobalTheory.WeilM.summable_of_mem_schA _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u _ hΦ)).tsum_add
        (GlobalTheory.WeilM.summable_of_mem_schA _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd u _ hΦ')))
  obtain ⟨hid, hsumid⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have sW : IsSelfDualC (spW₁ G i j) (G.Λ (.grid i j)) := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  have sX : IsSelfDualC (spX G i j) (latX G i j) := GlobalTheory.Twist.OrthSum.selfDual_hsum
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd
  have hh := fun w hw => halves e Γ h.JW₁ h.JWW W.ψ_std sW sX _ (hid w hw).1 (hid w hw).2
  have hv := fun w hw => GlobalTheory.SmallPlaces.lagr_vac (hI w hw) (hG.vac _).1 (hG.vac _).2.1
    {u | At (evFin D.host.F (w.under (𝓞 D.host.F))) u ∧ ptB e u ∈ homLatB G i j}
    (fun γ hγ hγ' => hγ'.elim
      (fun h' => vac_fixed_half h hT (mem_latAtV hti (hst.2 w hw) hγ.1 hγ.2) (GlobalTheory.SmallPlaces.splitIdem_conj (hid w hw).1).2.1 h')
      fun h' => vac_fixed_half h hT (mem_latAtV hti (hst.2 w hw) hγ.1 hγ.2) (hid w hw).1.2.1 h')
    (fun z => let ⟨y, h1, h2⟩ := linB_surj B t i j w z
      ⟨(ptE e).symm y, (congrArg (IsHalf _) (ptB_symm e y)).mpr h1, (congrArg (linB B t i j w) (ptB_symm e y)).trans h2⟩)
    (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, I w (Γ.M'.vac _) 0 with hc
  have hb : thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) Γ.M'.vac) = fun u => (c • vacB ρ i j) (ptB e u) :=
    funext fun u => (congrArg (thetaS Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans
      ((thetaS_smul _ _ _ _ u).trans (congrArg (c * ·) (hf₀.2 u)))
  obtain ⟨⟨T₁, hT₁⟩, hall⟩ := hF
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  have hinf : infPart D ε = 0 := GlobalTheory.PlaceVec.idemSum_infPart hε
  have hcε : cA D (cA D ε) = ε := GlobalTheory.DualPairCheck.cA_cA ε
  let R : Submodule ℂ ((PtS G i j → ℂ) × ((IxS G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ GlobalTheory.WeilM.schA D.host.F _ ∧ ∃ g, IsSBHalf (cA D ε) (homLatB G i j) g ∧ p.1 = (fun u => g (ptB e u)) ∧
        thetaS Γ W.ψ p.2 = fun u => T₁ g (ptB e u)}
      zero_mem' := ⟨zero_mem _, 0, sb_zero _ _, rfl, funext fun u => by
        rw [map_zero]; simpa using thetaS_smul Γ W.ψ 0 0 u⟩
      add_mem' := fun {p q} ⟨hp, g, g1, g2, g3⟩ ⟨hq, k, k1, k2, k3⟩ => ⟨add_mem hp hq, g + k, sb_add g1 k1, by
        rw [Prod.fst_add, g2, k2]; rfl, by
        rw [Prod.snd_add, hadd _ hp _ hq, g3, k3, map_add]; rfl⟩
      smul_mem' := fun a p ⟨hp, g, g1, g2, g3⟩ => ⟨Submodule.smul_mem _ a hp, a • g, sb_smul a g1, by
        rw [Prod.smul_fst, g2]; rfl, funext fun u => by
        rw [Prod.smul_snd, thetaS_smul, g3, map_smul]; rfl⟩ }
  let H : AddSubgroup (PtS G i j) := (GlobalTheory.PlaceModel.half _ _ (cA D ε)).comap (ptE e).toLinearMap.toAddMonoidHom
  have hH : ∀ u, u ∈ H ↔ IsHalf (cA D ε) (ptB e u) := fun u => (GlobalTheory.PlaceModel.isHalf_iff _ _).symm
  have hA : ∀ w ∈ locPl G t, ∀ x : WO (spW₁ G i j) (spX G i j), IsHalf (cA D (atPl w 1)) x → IsHalf (cA D ε) x :=
    fun w hw x hx => GlobalTheory.SmallPlaces.isHalf_mono (by rw [← RingHom.map_mul, hεw w hw]) hx
  have hA' : ∀ w ∈ locPl G t, ∀ x : WO (spW₁ G i j) (spX G i j), IsHalf (atPl w 1) x → IsHalf (cA D (cA D ε)) x :=
    fun w hw x hx => GlobalTheory.SmallPlaces.isHalf_mono (by rw [hcε, hεw w hw]) hx
  have hco : ∀ w u, linB B t i j w (ptB e (cA D (atPl w 1) • u)) = linB B t i j w (ptB e u) := fun w u => by
    rw [ptB_smul, linB_smul]
  have hbase : (Set.indicator (H : Set _) fun u => ∏ w ∈ locPl G t, I w (Γ.M'.vac _) (linB B t i j w (ptB e u))) =
      fun u => (c • halfInd (cA D ε) (homLatB G i j)) (ptB e u) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, halfInd]
    by_cases hu : IsHalf (cA D ε) (ptB e u)
    · rw [Set.indicator_of_mem ((hH u).2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ (hco w u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : ptB e u ∈ homLatB G i j
      · rw [if_pos ⟨hl, hu⟩, mul_one]
        refine Finset.prod_congr rfl fun w hw => Set.indicator_of_mem ?_ _
        exact ⟨(hh w hw).1 _ ((hh w hw).2.2.2.2 u).1, ((hh w hw).2.2.2.2 u).2.2 hl⟩
      · have : ∃ w ∈ locPl G t, ptB e (cA D (atPl w 1) • u) ∉ homLatB G i j := by
          by_contra! hall
          refine hl (GlobalTheory.SmallPlaces.mem_of_sum_smul (P := locPl G t) (a := fun w => cA D (atPl w 1)) ?_
            fun w hw => (congrArg (· ∈ homLatB G i j) (ptB_smul e _ u)).mp (hall w hw))
          rw [← map_sum, ← hεs]
          exact hu
        obtain ⟨w, hw, hn⟩ := this
        rw [if_neg fun h' => hl h'.1, mul_zero]
        refine Finset.prod_eq_zero hw (Set.indicator_of_notMem ?_ _)
        exact fun h' => hn h'.2
    · rw [Set.indicator_of_notMem (mt (hH u).1 hu), if_neg fun h' => hu h'.2, mul_zero]
  have hR := GlobalTheory.InductLagr.rel_of_vac Γ.M' W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => {u | IsHalf (cA D (atPl w 1)) (ptB e u)}) (fun w => {u | IsHalf (atPl w 1) (ptB e u)})
    (fun w u => linB B t i j w (ptB e u)) I H R (c • f)
    hI (fun w hw u hu => ⟨(hh w hw).1 u hu, (hH u).2 (hA w hw _ hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (congrArg _ (ptB_add e u x)).trans (linB_add B t i j w _ _))
    (fun w _ w' _ hne x hx u => (congrArg _ (ptB_add e u x)).trans ((linB_add B t i j w' _ _).trans
      ((congrArg _ (linB_ne B t i j w' hne hx)).trans (add_zero _))))
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, hco w u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p ⟨hp, g, g1, g2, g3⟩ => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd x _ hp, _,
      GlobalTheory.BigDat.GraphHeis.sb_trans_latO sW.1 sX.1 (GlobalTheory.PlaceVec.infPart_cA hinf) g1 (hA w hw _ hx),
      funext fun u => (congrFun g2 _).trans (congrArg g (ptB_add e u x)), by
        rw [hT₁.trans g g1 _ (hA w hw _ hx), ← heisS_ptB e Γ h.JW₁ h.JWW, ← g3]
        exact thetaS_rho Γ W.ψ p.2 x⟩)
    (fun w hw x hx p ⟨hp, g, g1, g2, g3⟩ => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd x _ hp, _,
      GlobalTheory.BigDat.GraphHeis.sb_modul_latO W.ψ_std sW sX (hcε.symm ▸ hinf) g1 (hA' w hw _ hx),
      funext fun u => congrArg₂ (· * ·) (congrArg W.ψ (sympS_ptB e Γ h.JW₁ h.JWW u x)) (congrFun g2 u), by
        rw [hT₁.modul g g1 _ (hA' w hw _ hx), ← heisS_ptB e Γ h.JW₁ h.JWW, ← g3]
        exact thetaS_rho Γ W.ψ p.2 x⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, _, sb_smul c (GlobalTheory.isSBHalf_halfInd _ _), hbase, by
      rw [map_smul, (congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac]
      exact hb⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.1.2.2.1 v).1 hm; hv w hw e
  obtain ⟨r1, g, -, g2, g3⟩ := hR
  have hg : g = prodB B t i j ε Ψ := funext fun y => by
    obtain ⟨u, rfl⟩ := (ptE e).surjective y
    refine (congrFun g2 u).symm.trans ?_
    rw [ptE_apply, prodB]
    dsimp only
    by_cases hu : IsHalf (cA D ε) (ptB e u)
    · rw [if_pos hu]
      rw [Set.indicator_of_mem ((hH u).2 hu)]
      exact Finset.prod_congr rfl fun w hw => congrFun (hΨ w hw) _
    · rw [if_neg hu]
      exact Set.indicator_of_notMem (mt (hH u).1 hu) _
  refine ⟨r1, fun u => ?_⟩
  rw [hall T₁ hT₁, ← hg]
  exact congrFun g3 u

end GlobalTheory.TopFlip.LinSmall

end
end

section
noncomputable section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TopFlip

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.TripleAssembly GlobalTheory.RouteSeesaw GlobalTheory.SquareIdent
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM)

theorem pureT_smul {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] {s ξ ξ' : ∀ i, N i}
    (h : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ) (h' : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ') {c : ι → ℂ} (hc : (Function.mulSupport c).Finite)
    (e : ∀ i, ξ' i = c i • ξ i) : GlobalTheory.SmallThetaModules.pureT s ξ' = (∏ᶠ i, c i) • GlobalTheory.SmallThetaModules.pureT s ξ := by
  apply Subtype.ext
  rw [Submodule.coe_smul, GlobalTheory.SmallThetaModules.coe_pureT h, GlobalTheory.SmallThetaModules.coe_pureT h']
  funext l
  simp only [GlobalTheory.SmallThetaModules.evFam, Pi.smul_apply, smul_eq_mul, e, map_smul]
  exact finprod_mul_distrib hc (GlobalTheory.SmallThetaModules.mulSupport_fin h l)

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem match_tens (hH : GlobalTheory.Published.HoweDualityReal) (hP : GlobalTheory.FunPr.Hypotheses₂) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ωA : WRep W X} {ωB : WRep W₁ X} (hωA : IsWeil ψ true W X β (β / α) ωA)
    (hωB : IsWeil ψ false W₁ X α (α / β) ωB) {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs Γ Xc}
    (hR : IsReading ψ A A₁ B α β e Bs Γ Xc) {om₀ om₀'} (hT₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om₀ om₀') :
    ∃ om om' R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf ∧
      ∃ rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB (ModuleCat.of ℂ (PiT R Γ Rf)) rf rl p p' ∧
      (∀ f₀, Γ.M.IsGauss Bs.ψ Bs.emb f₀ → ∀ P, ∃ a : R.Pi, ∀ φ, GlobalTheory.BigNZ.IsFinPart Γ.M Xc.T φ → ∀ F : WO W X → ℂ,
        IsDatum Γ.M ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
          Matrix (Fin X.rank) (Fin W.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F →
        IsFinF ψ θ true A B F ∧
          p (fockF ψ θ true A B F P) = a ⊗ₜ GlobalTheory.SmallThetaModules.pureT (vacIm Γ Rf) fun v => Rf.p v (φ v)) ∧
      ∀ f₀, Γ.M'.IsGauss Bs.ψ Bs.emb f₀ → ∀ P, ∃ a : R.Pi, ∀ φ, GlobalTheory.BigNZ.IsFinPart Γ.M' Xc.T φ → ∀ F : WO W₁ X → ℂ,
        IsDatum Γ.M' ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM W₁.gram) :
          Matrix (Fin X.rank) (Fin W₁.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F →
        IsFinF ψ θ false A₁ B F ∧
          p' (fockF ψ θ false A₁ B F P) = a ⊗ₜ GlobalTheory.SmallThetaModules.pureT (vacIm Γ Rf) fun v => Rf.p' v (φ v) := by
  obtain rfl := hR.ψ
  have hg := hT₀.geo
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hT₀.base.std
  obtain ⟨om, hom, tA⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base true W X e _ _ hg.hV hg.hW 1 hR.JW
    (by rw [neg_gram, one_smul, neg_neg]) hR.JX Γ.M hg.hM hωA
  obtain ⟨om', hom', tB⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base false W₁ X e _ _ hg.hV' hg.hW (-1) hR.JW₁
    (neg_one_smul _ _) hR.JX Γ.M' hg.hM' hωB
  have hT' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' :=
    ⟨hT₀.base, hg, hT₀.chars, by rw [hR.α, hR.β]; exact hom, by rw [hR.α, hR.β]; exact hom'⟩
  obtain ⟨R, Rf, hm⟩ := hTL _ _ _ Bs _ _ Γ Xc om om' hT'
  have sA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hstd hθ true W X A B β (β / α) ωA hωA
  have sB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hstd hθ false W₁ X A₁ B α (α / β) ωB hωB
  obtain ⟨oA, oB⟩ := GlobalTheory.T.algF_map_mapA_and_mapB_eq_top hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨iA, iB⟩ := GlobalTheory.T.mapA_mapB_invariant_under_finite_group hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨lA, lB⟩ := GlobalTheory.T.seesaw_weil_local_factor_eq hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨fA, fB⟩ := GlobalTheory.T.seesaw_weil_archimedean_factor hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨dA, dB⟩ := GlobalTheory.T.seesaw_weil_unramified_factor hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  have ir := GlobalTheory.T.seesaw_weil_global_factor hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨cA, hcA⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W X e.symm (-1) (neg_ne_zero.2 one_ne_zero)
  obtain ⟨cB, hcB⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W₁ X e.symm 1 one_ne_zero
  have gX := GlobalTheory.RouteCoords.gram_det_ne X
  have dV : Γ.V.J.det ≠ 0 := by rw [hR.JW, one_smul]; exact GlobalTheory.RouteCoords.gram_det_ne _
  have dV' : Γ.V'.J.det ≠ 0 := by
    rw [hR.JW₁, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (GlobalTheory.RouteCoords.gram_det_ne _)
  have dW : Γ.W.J.det ≠ 0 := by
    rw [hR.JX, det_smul, det_submatrix_equiv_self, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero) gX
  refine ⟨om, om', R, Rf, hm, _, _, _, _,
    ⟨hωA, hωB, ir, ⟨sA.1, sA.2, oA, iA, lA, fA, dA⟩, ⟨sB.1, sB.2, oB, iB, lB, fB, dB⟩⟩, fun f₀ g1 P => ?_, fun f₀ g2 P => ?_⟩
  · obtain ⟨a1, a2, -⟩ := fock_datum hθ true A B e.symm Bs hT₀.base hR.JW hR.JX hg.hV hg.hW
      (fun w => by
        obtain ⟨τ, a, b, -, d⟩ := hR.cart w
        exact ⟨τ, a, b.trans (one_smul _ _).symm, d⟩) Γ.M hg.hM cA hcA g1
    obtain ⟨f, hf, hPf⟩ := a2 P
    refine ⟨R.p f, fun φ p1 F kA => ?_⟩
    have p2 : ∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v := Xc.T.eventually_cofinite_notMem.mono p1.2
    have hcA' : ∀ u, cA u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
        Matrix (Fin X.rank) (Fin W.rank) (AE D)) := fun u => by rw [hcA, neg_one_smul]; rfl
    replace kA : IsDatum Γ.M Bs.ψ cA (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F := ⟨kA.1, fun u => by rw [hcA']; exact kA.2 u⟩
    have mA := thetaLift_pure Γ.M hg.hM hT₀.base.std dV dW (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) e Bs.emb R.p Rf.p
      (vacIm Γ Rf) (Filter.Eventually.of_forall fun _ => rfl) hf p1.1 p2
    have eA := eq_thO Γ.M Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) cA hcA' (hPf φ p1.1 p2 _ kA)
    refine ⟨a1 φ p1.1 p2 _ kA, ?_⟩
    rw [eA]
    exact mA
  · obtain ⟨b1, b2, -⟩ := fock_datum hθ false A₁ B e.symm Bs hT₀.base hR.JW₁ hR.JX hg.hV' hg.hW
      (fun w => by
        obtain ⟨τ, a, -, c, d⟩ := hR.cart w
        exact ⟨τ, a, c.trans (neg_one_smul _ _).symm, d⟩) Γ.M' hg.hM' cB hcB g2
    obtain ⟨f', hf', hP'⟩ := b2 P
    refine ⟨R.p' f', fun φ' q1 F kB => ?_⟩
    have q2 : ∀ᶠ v in Filter.cofinite, φ' v = Γ.M'.vac v := Xc.T.eventually_cofinite_notMem.mono q1.2
    have hcB' : ∀ u, cB u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM W₁.gram) :
        Matrix (Fin X.rank) (Fin W₁.rank) (AE D)) := fun u => by rw [hcB, one_smul]
    replace kB : IsDatum Γ.M' Bs.ψ cB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ') F := ⟨kB.1, fun u => by rw [hcB']; exact kB.2 u⟩
    have mB := thetaLift_pure Γ.M' hg.hM' hT₀.base.std dV' dW (GlobalTheory.RouteCoords.gram_det_ne W₁) e Bs.emb R.p' Rf.p'
      (vacIm Γ Rf) (Xc.T.eventually_cofinite_notMem.mono fun v hv => (hm.fin.sph v hv).1.symm) hf' q1.1 q2
    have eB := eq_thO Γ.M' Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne W₁) cB hcB' (hP' φ' q1.1 q2 _ kB)
    refine ⟨b1 φ' q1.1 q2 _ kB, ?_⟩
    rw [eB]
    exact mB

end GlobalTheory.TopFlip

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem pureT_loc (hL : L.Is μ₀) {t : T} {i j : ℕ} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} {om om' R Rf} (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf) (hti : IsTied t i j e Bs Γ X)
    {φ φ'} (h : IsFinPart Γ.M X.T φ) (h' : IsFinPart Γ.M' X.T φ') {c : Pl D.host.E → ℂ}
    (hc : ∀ w ∈ locPl G t, Rf.p _ (φ (w.under (𝓞 D.host.F))) = c w • Rf.p' _ (φ' (w.under (𝓞 D.host.F)))) :
    (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p v (φ v)) =
      (∏ w ∈ locPl G t, c w) • GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (φ' v) := by
  classical
  let c' : Pl D.host.F → ℂ := fun v => ∏ w ∈ locPl G t with w.under (𝓞 D.host.F) = v, c w
  have h1 : ∀ v, v ∉ X.T → c' v = 1 := fun v hv => Finset.prod_eq_one fun w hw => by
    obtain ⟨a, b⟩ := Finset.mem_filter.1 hw
    exact absurd ((hti.2.2.1 v).2 ⟨w, a, b⟩) hv
  have hs : Function.mulSupport c' ⊆ X.T := fun v hv => by_contra fun h => hv (h1 v h)
  rw [pureT_smul (s := GlobalTheory.TripleAssembly.vacIm Γ Rf) (ξ := fun v => Rf.p' v (φ' v)) (ξ' := fun v => Rf.p v (φ v)) (c := c') (X.T.finite_toSet.subset fun v hv => by_contra fun hn => hv (by
      exact (congrArg (Rf.p' v) (h'.2 v hn)).trans (hm.fin.sph v hn).1.symm))
    (X.T.finite_toSet.subset fun v hv => by_contra fun hn => hv (congrArg (Rf.p v) (h.2 v hn))) (X.T.finite_toSet.subset hs) fun v => ?_,
    finprod_eq_prod_of_mulSupport_subset _ hs,
    Finset.prod_fiberwise_of_maps_to fun w hw => (hti.2.2.1 _).2 ⟨w, hw, rfl⟩]
  by_cases hv : v ∈ X.T
  · obtain ⟨w, hw, rfl⟩ := (hti.2.2.1 v).1 hv
    have : c' (w.under (𝓞 D.host.F)) = c w := Finset.prod_eq_single_of_mem w (Finset.mem_filter.2 ⟨hw, rfl⟩)
      fun w' hw' hne => absurd (Good.under_injOn hL G t (Finset.mem_filter.1 hw').1 hw (Finset.mem_filter.1 hw').2) hne
    rw [this, hc w hw]
  · rw [h1 v hv, one_smul, h.2 v hv, h'.2 v hv, (hm.fin.sph v hv).1]

end GlobalTheory.TopFlip

end
end
