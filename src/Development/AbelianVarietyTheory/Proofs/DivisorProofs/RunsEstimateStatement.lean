import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNeOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullOfXiRec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTopOfCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRuns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.RunOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val_eq (D : D7) (y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
    ((cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  have h : D.conjF = D.sp.cm.sig :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin sigR
  rw [h]
  rfl

theorem xi_det_of_isDetRoot {D : D7} {xi de : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} (h : XiTilde xi de)
    (V : Formalism.BasicNotions.TH.HSp D) (g : Formalism.L2.Theta.GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.IsDetRoot V g x) :
    xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom V g)) =
      de (Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x) := by
  rw [← GlobalTheory.AntiCycRead.quo_of_isDetRoot D V g x hx, ← h]
  congr 1
  apply GlobalTheory.AntiCycRead.quo_eq_of
  have e : (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) =
      ((Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) := rfl
  rw [e, ← cjFin_val_eq, ← Units.val_mul, div_mul_cancel]

theorem exists_run_pins : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), Links2 p → CoreTies L ex.errX p.T (R2 p) → ∀ l : ℕ, (l = D.host.pde ∨ l = D.host.pde') → ∃ r : GlobalTheory.RealIndexBound.RunData p.T, LawsFull r.full ∧ (∀ i : Fin D.R.m, GlobalTheory.FormTies.OneCover r.full.toTop ((i : ℕ) + 1)) ∧ (∀ j n : ℕ, InR D j → (r.full.dδ j n).pd = l) ∧ (∀ i : Fin D.R.m, ∀ γ₀ ∈ Formalism.L2.Theta.GQ (r.full.V ((i : ℕ) + 1) r.full.σ₀), r.full.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (r.full.V ((i : ℕ) + 1) r.full.σ₀) γ₀)) = 1) ∧ ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ i : Fin D.R.m, letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg; RunPin (T := r.full) (R2 p) i (p.κ i).n v (ownAt D v) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ hC l hl

  obtain ⟨δ, hδdef⟩ : ∃ δ : Formalism.L2.Host.HChar D.host.E, δ = if l = D.host.pde then (R2 p).C.del else (R2 p).C.del' :=
    ⟨_, rfl⟩
  have hδ : Formalism.L2.Host.IsDelta (H := D.host) l δ := by
    rcases hl with rfl | rfl
    · rw [hδdef, if_pos rfl]; exact (R2 p).C.isDel
    · rw [hδdef, if_neg D.host.pde_ne.symm]; exact (R2 p).C.isDel'
  have hδv : ∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D := by
    intro x
    by_cases h : l = D.host.pde
    · rw [hδdef, if_pos h]; exact hC.delVal x
    · rw [hδdef, if_neg h]; exact hC.delVal' x
  obtain ⟨χ, de, hχ, hd, hfin⟩ := GlobalTheory.TameFinitePart.exists_xiRec D l δ hl hδ hδv
  have hF : GlobalTheory.FinalJoin2.FieldOK0 D l := by
    rcases hl with rfl | rfl
    exacts [hC.field₁, hC.field₂]

  obtain ⟨Pk, hPk⟩ := hC.oneHalf
  obtain ⟨P, hP, hPv⟩ : ∃ P : HeightOneSpectrum (𝓞 D.host.K), ((l : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal ∧
      ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ PP ∈ placesOver (R2 p) ((R2 p).mu v) (ownAt D v),
        P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
    by_cases hex : ∃ v ∈ (R2 p).twPl, ownAt D v = l
    · obtain ⟨v, hv, hvl⟩ := hex
      refine ⟨Pk l, by rw [← hvl]; exact (hPk v hv).1, fun w hw hwl PP hPP => ?_⟩
      have := (hPk w hw).2 PP hPP
      rwa [hwl] at this
    · have hlp : l.Prime := by
        rcases hl with rfl | rfl
        exacts [D.host.pde_prime, D.host.pde'_prime]
      obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hlp
      exact ⟨P, hP, fun w hw hwl => absurd ⟨w, hw, hwl⟩ hex⟩

  have hJ : LawsJ p.T := (fw2 p).laws
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.FinalJoin.exists_top_of_core D p.T.toCore hC.laws hC.rank hF.kpsi
  have hcan : T.Q.Canon := by
    have e : T.toCore.Q = p.T.toCore.Q := congrArg (fun C => C.Q) hTc
    rw [show T.Q = p.T.Q from e]
    exact hC.canon
  obtain ⟨dd, TF, hTF, -, hJ', hxi, hh, hcov⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiRec D p.T T hJ hT hTc hcan l hF P hP de hd
  obtain ⟨r, rfl⟩ : ∃ r : GlobalTheory.RealIndexBound.RunData p.T, r.full = TF := by
    rw [← hJ']
    exact ⟨GlobalTheory.RealIndexBound.RunData.of TF, rfl⟩
  have hInR : ∀ i : Fin D.R.m, InR D ((i : ℕ) + 1) := fun i => ⟨Nat.le_add_left _ _, i.2⟩
  refine ⟨r, hTF, fun i => (hcov _ (hInR i)).1, fun j n hj => (hcov j hj).2 n, ?_, ?_⟩
  · intro i γ₀ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D _).2.2.1 γ₀ hγ
    rw [xi_det_of_isDetRoot hxi _ _ _ hx]
    exact hd.rat _ x rfl
  · intro v hv hvl i
    letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [hvl]
      exact (hcov _ (hInR i)).2 _
    · intro PP hPP
      rw [hh]
      exact hPv v hv hvl PP hPP
    · have hδv' : (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = δ := by
        unfold ownAt at hvl
        unfold Formalism.L2.Host.CharFrame.delAt
        by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
        · rw [if_pos h] at hvl ⊢
          rw [hδdef, ← hvl, if_neg D.host.pde_ne.symm]
        · rw [if_neg h] at hvl ⊢
          rw [hδdef, ← hvl, if_pos rfl]
      refine ⟨χ, hδv' ▸ hχ, fun g x hx => ?_⟩
      rw [xi_det_of_isDetRoot hxi _ _ _ hx]
      exact hfin x _ rfl

end GlobalTheory.RunOnto
end
end

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), Links2 p → CoreTies L ex.errX p.T (R2 p) → ∀ l : ℕ, (l = D.host.pde ∨ l = D.host.pde') → ∃ r : GlobalTheory.RealIndexBound.RunData p.T, LawsFull r.full ∧ (∀ i : Fin D.R.m, GlobalTheory.FormTies.OneCover r.full.toTop ((i : ℕ) + 1)) ∧ (∀ j n : ℕ, InR D j → (r.full.dδ j n).pd = l) ∧ (∀ i : Fin D.R.m, ∀ γ₀ ∈ Formalism.L2.Theta.GQ (r.full.V ((i : ℕ) + 1) r.full.σ₀), r.full.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (r.full.V ((i : ℕ) + 1) r.full.σ₀) γ₀)) = 1) ∧ ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ i : Fin D.R.m, letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg; RunPin (T := r.full) (R2 p) i (p.κ i).n v (ownAt D v) := by
  atlas_forward_decl GlobalTheory.RunOnto.exists_run_pins
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroup_levelStructure_action_fixedRuns : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → (∀ i, OMPins J R κ v₀ O i) → RhoGeo fw O → (∀ i, OneMapRow0 J R κ v₀ O i) → J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∃ ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l), ∀ (r : RunData J) (h : LawsFull r.full) (i : Fin D.R.m), letI : Algebra r.full.J.Q.c.F D.what₂.LL := ‹Algebra J.Q.c.F D.what₂.LL›; LevelPin (T := r.full) R i (ℓ i) ∧ ActionPin (T := r.full) (R := R) h.p fw i (ℓ i) := by
  first | exact @GlobalTheory.LevelActionOnto.levelPin_actionPin | exact GlobalTheory.LevelActionOnto.levelPin_actionPin | (intros; apply GlobalTheory.LevelActionOnto.levelPin_actionPin <;> assumption)
end

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

set_option autoImplicit false

namespace GlobalTheory.BigOn.RunsExist

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_runs_at (p : PtAt ex Csz) (hR : p.Rows) (hM : More p) :
    ∃ r : TwoRuns p.T p.P.Gp, RunsOk (fw2 p) r ∧ OwnPin r := by
  have hL : Links2 p := GlobalTheory.T.second_link_of_weight_rows D L hT Gi Gl Kc Y cX ex Csz p hR hM.1
  have hC : CoreTies L ex.errX p.T (R2 p) := hM.2.1
  obtain ⟨r₁, l₁, c₁, d₁, x₁, p₁⟩ :=
    GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime D L hT Gi Gl Kc Y cX ex Csz p hL hC D.host.pde (Or.inl rfl)
  obtain ⟨r₂, l₂, c₂, d₂, x₂, p₂⟩ :=
    GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime D L hT Gi Gl Kc Y cX ex Csz p hL hC D.host.pde' (Or.inr rfl)
  have hcore : GlobalTheory.Hk3.Core (R2 p) (F2 p) :=
    ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.finiteGroup_levelStructure_action_fixedRuns D _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) hcore hL.2.2.2.2.2.2.1
    p.rhoGeo (fun i => (hR.oneMap i).1) hC.level
  let r : TwoRuns p.T p.P.Gp := ⟨r₁, r₂, ℓ⟩
  have hown : OwnPin r := ownPin_of d₁ d₂
  have hused : ∀ v, (r.used v = r₂ ∧ ownAt D v = D.host.pde') ∨ (r.used v = r₁ ∧ ownAt D v = D.host.pde) := by
    intro v
    by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
    · exact Or.inl ⟨if_pos h, if_pos h⟩
    · exact Or.inr ⟨if_neg h, if_neg h⟩
  have hlaws : ∀ v, LawsFull (r.used v).full := by
    intro v
    rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    exacts [l₂, l₁]
  refine ⟨r, ⟨hlaws, ?_, ?_, ?_, ?_, ?_, hC.level⟩, hown⟩
  · intro v
    rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    exacts [c₂, c₁]
  · intro v
    rcases hused v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    exacts [x₂, x₁]
  · intro v hv i
    rcases hused v with ⟨h, ho⟩ | ⟨h, ho⟩ <;> rw [h]
    exacts [p₂ v hv ho i, p₁ v hv ho i]
  · intro v i
    exact (hℓ (r.used v) (hlaws v) i).1
  · intro v i
    exact (hℓ (r.used v) (hlaws v) i).2

end GlobalTheory.BigOn.RunsExist

theorem GlobalTheory.BigOn.runsSt : RunsSt := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact ⟨0, fun x hx _ i p hR hM => GlobalTheory.BigOn.RunsExist.exists_runs_at p hR hM⟩
end
