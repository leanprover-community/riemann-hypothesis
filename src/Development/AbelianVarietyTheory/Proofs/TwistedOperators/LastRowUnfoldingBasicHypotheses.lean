import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvarianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QEqColPer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepTrilinearFormProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsTer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansion

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaJoint

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

set_option maxHeartbeats 1000000 in

theorem isBiTheta_lastDat (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj))
    (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ)
    (hΦ₁ : IsThetaFunO W.ψ _ _ Φ₁) (hΦ₂ : IsThetaFunO W.ψ _ _ Φ₂) :
    IsBiTheta W.ψ _ _ _ (lastDat W hM j hj vN g Φ₁ Φ₂) := by
  have hΨ : IsThetaFunO W.ψ _ _ ((lastAt G W t hM j hj vN).s.om (g, 1) Φ₁) := (lastAt G W t hM j hj vN).s.weil.om_pres _ _ hΦ₁
  have hΞ : IsThetaFunO W.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1)))
      (GlobalTheory.Unf.flatBF (lastAt G W t hM j hj vN).s ((lastAt G W t hM j hj vN).s.om (g, 1) Φ₁)) :=
    (GlobalTheory.LastRed.val_zero (lastAt G W t hM j hj vN).s hΨ).1
  have hΦ₂' : IsThetaFunO W.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m))
      (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) := GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero _ _ hΦ₂
  exact GlobalTheory.LastBiTheta.isBiTheta_lastBi D W.ψ W.ψ_std (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
    (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o
    (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau LastSeeSawStep.lastTau_gram _ _ hΞ hΦ₂'

set_option maxHeartbeats 1000000 in

theorem isBiTheta_contr (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j (σ + 1) hj))
    (vN' : GlobalTheory.Unf.VolN (besDecAt G (j + 1 + 1) σ (by omega))) (vL : GlobalTheory.Unf.VolM D _ _)
    (Ψ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Ψ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) → ℂ)
    (h₁ : IsThetaFunO W.ψ _ _ Ψ₁) (h₂ : IsThetaFunO W.ψ _ _ Ψ₂) :
    IsBiTheta W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))
      (GlobalTheory.Unf.contr (linkAt hM j σ hj vN (by omega) vN') (G.V (.top (j + 1))) vL
      (GlobalTheory.Unf.flatBF (B := besAt G hM j _ hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
        (stepAt G W t hM j (by omega) (besDecAt G j _ hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))) Ψ₁)
      (GlobalTheory.Unf.flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega)) (B := besAt G hM (j + 1 + 1) σ (by omega) vN')
        (stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
          (besDecAt G (j + 1 + 1) σ (by omega))) Ψ₂)) := by
  let B := besAt G hM j (σ + 1) hj vN
  let J := jacAt G hM (j + 1) (σ + 1) (by omega)
  let B' := besAt G hM (j + 1 + 1) σ (by omega) vN'
  let s₁ : GlobalTheory.Unf.StepBF W.ψ B J :=
    stepAt G W t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
  let s₂ : GlobalTheory.Unf.StepFB W.ψ J B' :=
    stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
  have t₁ : IsThetaFunO W.ψ B.V₀ J.W₀ (GlobalTheory.Unf.flatBF s₁ Ψ₁) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).1 _ B J s₁ _ h₁
  have t₂ : IsThetaFunO W.ψ J.W₀ B'.V₀ (GlobalTheory.Unf.flatFB s₂ Ψ₂) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).2 _ J B' s₂ _ h₂
  exact (GlobalTheory.ContrComb.contr_comb_main D W.ψ W.ψ_std _ _ B B' (linkAt hM j σ hj vN (by omega) vN') _ vL _ _ t₁ t₂).1

theorem castSch_theta' {k n : ℕ} (e : n = D.R.m) (f : WO (G.V (.grid D.R.m k)) (G.V (.grid D.R.m n)) → ℂ)
    (hf : IsThetaFunO W.ψ _ _ f) : IsThetaFunO W.ψ _ _ (castSch G e f) := by
  subst e
  exact hf

theorem dite_pred {α : Type} (P : α → Prop) {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} (ha : ∀ h, P (a h))
    (hb : ∀ h, P (b h)) : P (dite c a b) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h

set_option maxHeartbeats 1000000 in

theorem isBiTheta_conAt (hM : M.Is t) (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (j : ℕ) :
    IsBiTheta W.ψ _ _ _ (conAt W hM Φ h j) := by
  unfold conAt
  refine dite_pred (IsBiTheta W.ψ _ _ _) (fun h0 => ?_) (fun _ => dite_pred (IsBiTheta W.ψ _ _ _) (fun hj => ?_) (fun _ => ?_))
  · exact isBiTheta_lastDat W hM j h0 _ _ _ _ (hΦ ⟨j, by omega⟩) (castSch_theta' W _ _ (hΦ ⟨j + 1, by omega⟩))
  · refine isBiTheta_contr W hM j _ hj _ _ _ _ _ ?_ ?_
    · exact (W.om_is (.mu t D.R.m j) ⟨le_rfl, by omega⟩).om_pres _ _ (hΦ ⟨j, by omega⟩)
    · exact (W.om_is (.mu t D.R.m (j + 1)) ⟨le_rfl, by omega⟩).om_pres _ _ (hΦ ⟨j + 1, by omega⟩)
  · exact GlobalTheory.TriStep.isBiTheta_zero'

theorem main : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (M : Vol ch.G) (hM : M.Is t), ∀ d ∈ τ.support, ∀ P h,
    ∀ j, Even j → j < D.R.m → IsBiTheta ch.W.ψ _ _ _ (conAt ch.W hM (fockD ch.W t d.2 P) h j) := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t Φ τ hτ M hM d hd P h j _ _
  obtain ⟨e, he, φ, hφ, -⟩ := hτ
  exact isBiTheta_conAt ch.W hM _ (fun a => GlobalTheory.DownFock.isThetaFunO_fock_down ch.rm t D.R.m a le_rfl a.2 he ((hφ d hd).2 a) (P a)) h j

end GlobalTheory.ThetaJoint
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingJointData_jointlySmoothTheta_evenIndex : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (M : Vol ch.G) (hM : M.Is t), ∀ d ∈ τ.support, ∀ P h,
    ∀ j, Even j → j < D.R.m → IsBiTheta ch.W.ψ _ _ _ (conAt ch.W hM (fockD ch.W t d.2 P) h j) := by
  atlas_forward_decl GlobalTheory.ThetaJoint.main
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlipRowTheta

theorem row_isThetaFunO : Big fun ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ d ∈ τ.support, ∀ i,
    IsThetaFunO ch.W.ψ _ _ (d.1 i) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t Φ τ hτ d hd i
  obtain ⟨e, _he, φ, hφ, _⟩ := hτ
  have hv := ch.rm.vX_is i D.R.m i.2 le_rfl
  exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt ch.W.ψ_std ch.W.θ_is ((hφ d hd).1 i).2 hv.2.theta

end GlobalTheory.FlipRowTheta

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_flippedFiniteTensor_row_isThetaFunction : Big fun ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ d ∈ τ.support, ∀ i, IsThetaFunO ch.W.ψ _ _ (d.1 i) := by
  atlas_forward_decl GlobalTheory.FlipRowTheta.row_isThetaFunO
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowCombGood

theorem comb_good : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) →
    Good ch.W (combC ch.W c C) (combR ch.rm c) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro C hC c _
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  have hL := s.core.lev
  refine ⟨fun j hje hj => ?_, fun i => ?_⟩
  · obtain ⟨k, hk⟩ := D.R.m_even
    obtain ⟨l, hl⟩ := hje
    obtain ⟨hv, hs⟩ := hC j ⟨l, hl⟩ hj
    have h1 : IsBiTheta ch.W.ψ _ _ _ (C j) :=
      GlobalTheory.FrComb.biTheta_of_vac (node_isV ch.G hL (X := .top j) (show j ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).sd hv hs
    exact GlobalTheory.FrCombAny.biTheta_biComb D _ hψ _ _ _ _ h1 _ _
  · exact GlobalTheory.CombThetaAny.main D _ hψ _ _ _ _ (ch.rm.vX_is i D.R.m i.2 le_rfl).2.theta

end GlobalTheory.RowCombGood
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_heisenberg_combinations_joint_row_good : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) →
    Good ch.W (combC ch.W c C) (combR ch.rm c) := by
  atlas_forward_decl GlobalTheory.RowCombGood.comb_good
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_exists_combinations_of_expansion : Big fun ch => ∀ t Φ β τ, ch.S.IsExpansion t Φ β τ → ∃ c, IsCombs ch.W τ c := by
  first | exact @GlobalTheory.CombsExist.combs_exist | exact GlobalTheory.CombsExist.combs_exist | (intros; apply GlobalTheory.CombsExist.combs_exist <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowBasic

theorem c3 : Big fun ch => ∀ t (M : Vol ch.G), M.Is t → IsHaarDef M := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro t M hM X hX _
  refine (hM.vtx X ?_).haar_fund
  cases X <;> simp only [DefNode, Node.InRange] at hX ⊢ <;> omega

theorem c4 : Big fun ch => ∀ t Φ β M, IsTermVol t ch.S.toGridChoice Φ β M → IsHaarDef M := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro t Φ β M hM X hX hne
  cases X with
  | grid i j =>
    obtain ⟨hi, rfl⟩ := hX
    exact (hM.2 i hi).haar_fund
  | top j =>
    have : j < D.R.m := lt_of_le_of_ne hX (fun e => hne (by rw [e]))
    exact (hM.1 j this).haar_fund
  | core i => exact hX.elim

theorem basicAt : Big fun ch => BasicAt ch := by
  have hall := (((((((GlobalTheory.T.besselColumnScalarFunction_continuous_leftInvariant.and GlobalTheory.T.gridTopVertexFormFunction_continuous_left_invariant).and c3).and c4).and GlobalTheory.T.unfoldingJointData_jointlySmoothTheta_evenIndex).and GlobalTheory.T.rowTest_flippedFiniteTensor_row_isThetaFunction).and GlobalTheory.T.rowTest_heisenberg_combinations_joint_row_good).and GlobalTheory.T.rowTest_exists_combinations_of_expansion)
  refine GlobalTheory.RowReal.big_mono (fun ch h => ?_) hall
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5a⟩, h5b⟩, h6⟩, h7⟩
  refine ⟨fun a => ⟨(h1 a).2, (h1 a).1⟩, fun t y => ⟨(h2 t y).2, (h2 t y).1⟩, h3, h4, ?_, h6, h7⟩
  intro t Φ τ hτ M hM d hd P hh
  exact ⟨fun j hj hjm => h5a t Φ τ hτ M hM d hd P hh j hj hjm, h5b t Φ τ hτ d hd⟩

end GlobalTheory.RowBasic
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_unfolding_basicHypotheses : Big fun ch => BasicAt ch := by
  atlas_forward_decl GlobalTheory.RowBasic.basicAt
end
