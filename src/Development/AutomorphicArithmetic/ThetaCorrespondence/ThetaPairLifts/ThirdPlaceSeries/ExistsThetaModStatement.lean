import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaModuleOfCanonicalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaModuleOfCanonical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLinearForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionContinuousInvariantStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionContinuousInvariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MapMemISupIsLinAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepcongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftEquivariance
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftedCharactersAgreeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftedCharactersAgree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
noncomputable section
namespace GlobalTheory.ThetaFormV
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.ThetaTri
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Frame
variable {D : D7} {V : HSp D} {n : ℕ}
end Frame
section Forms
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
theorem eW_cast_cV_rho_eq_wt_rho (A : GlobalTheory.NJoin.Agree X P.M P.rep) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ)
    (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m)
    (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) {γ : GA D (Vc D j)} (hγ : γ ∈ GQ (Vc D j))
    (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h * A.a j))) (v : (X.R.cV j).W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2) ((X.R.cV j).ρ γ v) =
      (P.M μ k p1 p2).wt.ρ h ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2) v) := by
  subst hk
  exact A.wt μ hμ j h γ hγ he v
theorem eWloc_cV_rho_eq_wt_rho (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) {γ : GA D (Vc D j)}
    (hγ : γ ∈ GQ (Vc D j))
    (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h * A.a j))) (v : (X.R.cV j).W) :
    _root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ ((X.R.cV j).ρ γ v) = (P.M.loc i).wt.ρ h (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ v) :=
  _root_.GlobalTheory.ThetaFormV.eW_cast_cV_rho_eq_wt_rho A hμ j _ hj _ _ h hγ he v
end Forms
section Main
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def agreementLocalMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Bridge.Gf (Vc D j) → (X.R.cV j).W :=
  fun k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))
theorem fFin_apply' (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (k : Bridge.Gf (Vc D j)) : _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F k =
      (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k)) := rfl
theorem formToVectorMap_eq_ext_fFin (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F = (X.R.cV j).ext (_root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F) := rfl
theorem fFin_rangeRestrict_mul (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    {γ : GA D (Vc D j)} (hγ : γ ∈ GQ (Vc D j)) (k : Bridge.Gf (Vc D j)) :
    _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F ((finHom (Vc D j)).rangeRestrict γ * k) = (X.R.cV j).ρ γ (_root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F k) := by
  set x := preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ) with hxdef
  have hx : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ x) :=
    (congrArg Subtype.val (GlobalTheory.ThetaFormV.fin_preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ))).symm
  have e0 : (A.a j)⁻¹ * (A.a j * x * (A.a j)⁻¹) * A.a j = x := by group
  have hrat : A.a j * x * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV :=
    (A.rat j _).2 ⟨γ, hγ, by rw [e0]; exact hx⟩
  have he : finHom (Vc D j) γ =
      finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * ((⟨_, hrat⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : GAf D.host.E D.R.nV) * A.a j)) := by
    rw [e0]; exact hx
  have e1 : A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ * k) =
      (A.a j * x * (A.a j)⁻¹) * (A.a j * preF (A.PV j) k) := by
    rw [GlobalTheory.ThetaFormV.preF_mul, ← hxdef]; group
  have hF := F.2.1 ⟨_, hrat⟩ (A.a j * preF (A.PV j) k)
  unfold _root_.GlobalTheory.ThetaFormV.agreementLocalMap
  rw [e1]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  rw [_root_.GlobalTheory.ThetaFormV.eWloc_cV_rho_eq_wt_rho A i j hj hμ ⟨_, hrat⟩ hγ he, LinearEquiv.apply_symm_apply]
  exact hF
theorem formToVectorMap_left_invariant (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    ∀ γ ∈ GQ (Vc D j), ∀ h, _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * h) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h := by
  intro γ hγ h
  rw [_root_.GlobalTheory.ThetaFormV.formToVectorMap_eq_ext_fFin, GlobalTheory.ThetaFormV.ext_apply, GlobalTheory.ThetaFormV.ext_apply, map_mul, _root_.GlobalTheory.ThetaFormV.fFin_rangeRestrict_mul A i j hj hμ F hγ]
  have e : (X.R.cV j).ρ (γ * h)⁻¹ * (X.R.cV j).ρ γ = (X.R.cV j).ρ h⁻¹ := by
    rw [← map_mul]; congr 1; group
  exact congrArg (fun T : Module.End ℂ (X.R.cV j).W => T _) e
end Main
section Cont
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
theorem continuous_formToVectorMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Continuous (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D (Vc D j)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D j).gram))
  obtain ⟨N, hN, hlev⟩ := F.2.2
  let J : Subgroup (Bridge.Gf (Vc D j)) :=
    { carrier := {q | ∀ k, _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F (k * q) = _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F k}
      mul_mem' := fun {a b} ha hb k => by simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [← mul_assoc, hb, ha]
      one_mem' := fun k => by rw [mul_one]
      inv_mem' := fun {a} ha k => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (k * a⁻¹), inv_mul_cancel_right] }
  have hfJ : _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F ∈ Bridge.AdForms ((finHom (Vc D j)).rangeRestrict.comp (GQ (Vc D j)).subtype)
      ((X.R.cV j).ρ.comp (GQ (Vc D j)).subtype) J 1 := by
    exact GlobalTheory.ThetaFormV.mem_adForms_one _ _ (fun γ hγ k => _root_.GlobalTheory.ThetaFormV.fFin_rangeRestrict_mul A i j hj hμ F hγ k) J (fun q hq => hq)
  have hJ : ∀ᶠ κ in 𝓝 (1 : GA D (Vc D j)), ∃ h : (finHom (Vc D j)).rangeRestrict κ ∈ J,
      (1 : J →* ℂˣ) ⟨_, h⟩ = 1 := by
    filter_upwards [eventually_cong_preF (A.PV j) A.hF (A.stdV j) hN] with κ hκ
    refine ⟨fun k => ?_, rfl⟩
    show _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F (k * (finHom (Vc D j)).rangeRestrict κ) = _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F k
    rw [_root_.GlobalTheory.ThetaFormV.fFin_apply', _root_.GlobalTheory.ThetaFormV.fFin_apply', GlobalTheory.ThetaFormV.preF_mul, ← mul_assoc, hlev _ hκ]
  exact (GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D j)).rangeRestrict (GQ (Vc D j)) (X.R.cV j).ρ
    ((X.given.core.models.cV j).2.2.1) hJ hfJ).congr fun g => (GlobalTheory.ThetaFormV.ext_apply _ _ _).symm
end Cont
theorem formToVectorMap_continuous_and_left_invariant : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)),
    Continuous (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F) ∧
      ∀ γ ∈ GQ (Vc D j), ∀ h, _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * h) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h :=
  fun _ _ _ _ A i j hj hμ F => ⟨_root_.GlobalTheory.ThetaFormV.continuous_formToVectorMap A i j hj hμ F, _root_.GlobalTheory.ThetaFormV.formToVectorMap_left_invariant A i j hj hμ F⟩
end GlobalTheory.ThetaFormV
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)),
    Continuous (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F) ∧
      ∀ γ ∈ GQ (Vc D j), ∀ h, _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * h) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h := by
  atlas_forward_decl _root_.GlobalTheory.ThetaFormV.formToVectorMap_continuous_and_left_invariant
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.ThetaTri in
theorem mem_omI_of_theta_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (φ v)) → φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ := by
  intro _ hP hL D P X A i j hj Y hc hμ φ hφ
  have hm := X.given.core.models
  have hθ : IsInfFam X.R.θ := hm.inf
  have hω := X.given.core.thP.ωP j (X.tupT (D.nd.mu i))
  have hp : (Vc D j).IsPosDef := hm.vpos j
  have hpd : ∀ τ, (gramAt D (Vc D j) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((j : ℕ) + 1)) τ
  have hHV := (hm.νV j (X.tupT (D.nd.mu i))).1.1
  have hfdV := (hm.νV j (X.tupT (D.nd.mu i))).2
  have hHW : (X.R.νW j).IsHaarMeasure := (hm.νW j).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D j)) (X.R.fdW j) (X.R.νW j) := (hm.νW j).2
  intro p
  have hφ' : ∀ v, IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ v) :=
    fun v => hω.om_pres _ _ (hφ v)
  refine ⟨hφ', fun F g => ?_, fun F y => ?_⟩
  · obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant hL D P X A i j hj hμ F
    exact GlobalTheory.DefiniteQuotient.integrableOn_theta D X.R.ψ hω.std (Vc D j) (Wc D j) _ _ _ hω hpd _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2 _ _ hHV hfdV g
  · obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant hL D P X A i j hj hμ F
    have hmap := (Classical.choose_spec (Classical.choose_spec hc)).2.2.1
    have hey : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) ∈ Formalism.IndefR.principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) := by
      rw [← hmap]; exact ⟨y, y.2, rfl⟩
    have hyv : _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y = _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) (fun τ => ((Classical.epsilon fun u : ↥(lowT (X.R.MW j (sg0 D X.A)) τ) =>
        ‖((u : (X.R.MW j (sg0 D X.A)).sm τ) : (X.R.MW j (sg0 D X.A)).H τ)‖ = 1 : ↥(lowT (X.R.MW j (sg0 D X.A)) τ)) :
          (X.R.MW j (sg0 D X.A)).sm τ)) := by
      simp [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap, kUnit, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
    obtain ⟨haut, hcu⟩ := GlobalTheory.T.multiplicitySpaceAllLevels_values_smooth_cuspidal X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) _ hey
      (fun τ => ((Classical.epsilon fun u : ↥(lowT (X.R.MW j (sg0 D X.A)) τ) =>
        ‖((u : (X.R.MW j (sg0 D X.A)).sm τ) : (X.R.MW j (sg0 D X.A)).H τ)‖ = 1 : ↥(lowT (X.R.MW j (sg0 D X.A)) τ)) :
          (X.R.MW j (sg0 D X.A)).sm τ))
    rw [← hyv] at haut hcu
    have hR := (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ haut hcu).conj
    have hgr := GlobalTheory.T.moderateGrowth_definiteThetaIntegral_vectorForm X.R.ψ (Vc D j) (Wc D j) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2
    have hct := GlobalTheory.T.continuous_definiteThetaIntegral_vectorForm X.R.ψ (Vc D j) (Wc D j) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2
    have hinv : ∀ γ ∈ GQ (Wc D j), ∀ g, (∫ h in X.R.fdV j (X.tupT (D.nd.mu i)),
        thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h (γ * g)
          (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h)) ∂(X.R.νV j (X.tupT (D.nd.mu i)))) =
        ∫ h in X.R.fdV j (X.tupT (D.nd.mu i)), thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h g
          (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h)) ∂(X.R.νV j (X.tupT (D.nd.mu i))) := by
      intro γ hγ g
      congr 1
      funext h
      have e : ((h, γ * g) : GA D (Vc D j) × GA D (Wc D j)) = (1, γ) * (h, g) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hφ' _))
    have := hR.integrableOn_modGrowth_mul hHW hfdW hgr hinv hct.aestronglyMeasurable
    convert this using 1
    funext g
    simp only [Pi.mul_apply, thIn]
    rw [mul_comm]
    rfl
end GlobalTheory.ThetaTri
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_linear_form_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (φ v)) → φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ := by
  atlas_forward_decl _root_.GlobalTheory.ThetaTri.mem_omI_of_theta_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaTri
open scoped TensorProduct
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc Formalism.L2.Theta
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
theorem eW_cast_symm_wt_rho_eq (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) (w : (P.M (D.nd.mu i) k p1 p2).wt.W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm
        ((P.M (D.nd.mu i) k p1 p2).wt.ρ h' w) =
      (X.R.cV j).ρ γ ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm w) := by
  subst hk
  apply (A.eW _ hμ j).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [A.wt _ hμ j h' γ hγ he]
  simp
theorem eWloc_symm_wt_rho_eq_cV_rho (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (w : (P.M.loc i).wt.W) :
    (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((P.M.loc i).wt.ρ h' w) = (X.R.cV j).ρ γ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm w) :=
  _root_.GlobalTheory.ThetaTri.eW_cast_symm_wt_rho_eq A i j hμ h' γ hγ he (D.nd.j i) hj _ _ w
theorem formToVectorMap_rt_eq_mul_psi (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (hcv : (X.R.cV j).Is) (h : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (hF : (F' : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F)
    (x : GA D (Vc D j)) : _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F' x = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (x * (A.PV j).ψ h) := by
  show (X.R.cV j).ext _ x = (X.R.cV j).ext _ (x * (A.PV j).ψ h)
  rw [GlobalTheory.DefLiftHecke.ext_mul _ hcv _ ((A.PV j).into h) x]
  show (X.R.cV j).ρ x⁻¹ _ = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk, preF_mul, hF, NG.rt, mul_assoc]
theorem formToVectorMap_mul_of_mem_GQ (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (γ : GA D (Vc D j)) (hγ : γ ∈ GQ (Vc D j)) (x : GA D (Vc D j)) :
    _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * x) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F x := by
  obtain ⟨y, hy⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict γ)
  obtain ⟨z, hz⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict x)
  have hh' : A.a j * y * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := by
    refine (A.rat j _).2 ⟨γ, hγ, ?_⟩
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    rw [this]
    exact (congrArg Subtype.val hy).symm
  have he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ *
      ((⟨_, hh'⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j)) := by
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    simp only [this]
    exact (congrArg Subtype.val hy).symm
  show (X.R.cV j).ρ (γ * x)⁻¹ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x))))) =
    (X.R.cV j).ρ x⁻¹ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x))))
  have hprod : (finHom (Vc D j)).rangeRestrict γ * (finHom (Vc D j)).rangeRestrict x =
      (finHom (Vc D j)).rangeRestrict ((A.PV j).ψ (y * z)) :=
    (congrArg₂ (· * ·) hy.symm hz.symm).trans
      ((map_mul (finHom (Vc D j)).rangeRestrict _ _).symm.trans
        (congrArg (finHom (Vc D j)).rangeRestrict (map_mul (A.PV j).ψ y z).symm))
  have key : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x)) = y * z :=
    (congrArg (preF (A.PV j)) ((map_mul (finHom (Vc D j)).rangeRestrict γ x).trans hprod)).trans (preF_frame _ _)
  have hz' : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x) = z :=
    (congrArg (preF (A.PV j)) hz.symm).trans (preF_frame _ _)
  rw [key, hz']
  have e1 : A.a j * (y * z) = (A.a j * y * (A.a j)⁻¹) * (A.a j * z) := by group
  rw [e1, F.2.1 ⟨_, hh'⟩ (A.a j * z), _root_.GlobalTheory.ThetaTri.eWloc_symm_wt_rho_eq_cV_rho A i j hj hμ ⟨_, hh'⟩ γ hγ he, _root_.mul_inv_rev,
    map_mul, Module.End.mul_apply, ← Module.End.mul_apply ((X.R.cV j).ρ γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]
theorem thetaEvaluationMap_apply {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y x = PiTensorProduct.lift (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A)) (PiTensorProduct.map
      (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype) (kUnit (X.R.MW j (sg0 D X.A)))) x := rfl
theorem thetaEvaluationMap_rho_eq_mul_psi {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (g : Formalism.AUTREP.GAf D.host.E D.R.r) (y y' : ↥Y.C) (hy : (y' : Y.A) = Y.ρ g y) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y' x = _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (x * (X.PW j).ψ g) := by
  have he : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y' : Y.A) = Formalism.IndefR.principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A)) g (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A)) := by
    rw [hy]; exact (Classical.choose_spec (Classical.choose_spec hc)).2.2.2.1 g y
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, he, lift_actM]
theorem thetaEvaluationMap_mul_of_mem_GQ {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (γ : GA D (Wc D j)) (hγ : γ ∈ GQ (Wc D j)) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (γ * x) = _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y x := by
  have hm : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) ∈ LeftInvM (X.R.MW j (sg0 D X.A)) := by
    apply minf_le_leftInv X.R.θ (X.PW j)
    rw [← (Classical.choose_spec (Classical.choose_spec hc)).2.2.1]
    exact Submodule.mem_map_of_mem y.2
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply]
  exact lift_left _ _ hm _ γ hγ x
theorem lamI_inv_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ → ∀ (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y y' : ↥Y.C), (F' : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : Y.A) = Y.ρ g y → _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (GlobalTheory.ThetaTri.valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' y' = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ φ F y := by
  intro hL D P X A i j hj Y hc hμ h g φ hφ F F' y y' hF hy
  have hcore := X.given.core
  have hW := hcore.thP.ωP j (X.tupT (D.nd.mu i))
  have hcv : (X.R.cV j).Is := hcore.models.cV j
  have hth : ∀ v, IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (φ v) := by
    intro v
    have := (hφ 1).1 v
    simpa [valAct1_apply] using this
  have hV := hcore.models.νV j (X.tupT (D.nd.mu i))
  have hWm := hcore.models.νW j
  haveI : (X.R.νV j (X.tupT (D.nd.mu i))).IsHaarMeasure := hV.1.1
  haveI : (X.R.νV j (X.tupT (D.nd.mu i))).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hV.1.1
  haveI : (X.R.νW j).IsHaarMeasure := hWm.1.1
  haveI : (X.R.νW j).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hWm.1.1
  haveI : Countable (GQ (Vc D j)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Vc D j).gram
  haveI : Countable (GQ (Wc D j)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Wc D j).gram
  have inner : ∀ g₀, thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (X.R.νV j (X.tupT (D.nd.mu i)))
      (X.R.fdV j (X.tupT (D.nd.mu i))) (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' g₀ =
      thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (X.R.νV j (X.tupT (D.nd.mu i)))
      (X.R.fdV j (X.tupT (D.nd.mu i))) φ F (g₀ * (X.PW j).ψ g) := by
    intro g₀
    unfold thIn
    have e1 : ∀ h₀, thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h₀ g₀
        (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F' h₀)) =
        thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) (h₀ * (A.PV j).ψ h) (g₀ * (X.PW j).ψ g)
          (φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (h₀ * (A.PV j).ψ h))) := by
      intro h₀
      rw [valAct1_apply, _root_.GlobalTheory.ThetaTri.formToVectorMap_rt_eq_mul_psi A i j hj hμ hcv h F F' hF h₀]
      exact thetaKO_act _ _ _ _ _
    simp only [e1]
    refine (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D j)) _ _ hV.2
      (fun h₁ => thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h₁ (g₀ * (X.PW j).ψ g) (φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))) ?_ _).2
    intro γ hγ h₁
    rw [_root_.GlobalTheory.ThetaTri.formToVectorMap_mul_of_mem_GQ A i j hj hμ F γ hγ h₁]
    have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))).1 γ hγ 1
      (one_mem _) h₁ (g₀ * (X.PW j).ψ g)
    rwa [one_mul] at this
  unfold _root_.GlobalTheory.ThetaTri.canonicalPairingValue lamV
  congr 1
  have e2 : ∀ g₀, star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y' g₀) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i)))
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' g₀ =
      star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (g₀ * (X.PW j).ψ g)) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i))) φ F (g₀ * (X.PW j).ψ g) := by
    intro g₀
    rw [inner, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_rho_eq_mul_psi hc g y y' hy]
  simp only [e2]
  refine (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Wc D j)) _ _ hWm.2
    (fun g₁ => star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y g₁) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i))) φ F g₁) ?_ _).2
  intro γ hγ g₁
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_mul_of_mem_GQ hc y γ hγ g₁]
  congr 1
  unfold thIn
  congr 1
  funext h₁
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))).1 1 (one_mem _) γ hγ
    h₁ g₁
  rwa [one_mul] at this
end GlobalTheory.ThetaTri
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_equivariance_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ → ∀ (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y y' : ↥Y.C), (F' : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : Y.A) = Y.ρ g y → _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (GlobalTheory.ThetaTri.valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' y' = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ φ F y := by
  atlas_forward_decl _root_.GlobalTheory.ThetaTri.lamI_inv_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaRead
open MeasureTheory Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
  Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.ThetaTri
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pair
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
end Pair
section Unit
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
end Unit
section Row
variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
end Row
section Forms
variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} {X : GlobalTheory.NJoin.RealAt D cf nch tp}
  {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
end Forms
section Canon
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
set_option maxHeartbeats 1000000 in
theorem integral_theta_evaluation_thetaKO {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (Y : RowMod D P.rep k)
    (hc : GlobalTheory.NJoin.IsCanon X j hk Y) (x : D.what₂.Mt μ k) (y : D.what₂.Mj k) :
    inner ℂ y (D.what₂.thetaP μ k x) = (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) *
      ∫ g in X.R.fdW j, star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc ⟨Y.φ y, Y.φ_mem y⟩ g) *
        (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
          (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT μ) (X.fn hμ j (hk.symm ▸ x) h)) ∂(X.R.νV j (X.tupT μ))) ∂(X.R.νW j) := by
  subst hk
  obtain ⟨-, -, -, -, hB, hφ⟩ := Classical.choose_spec (Classical.choose_spec hc)
  refine (Y.φ_inner _ _).trans ((hB _ (Y.φ_mem _) _ (Y.φ_mem _)).trans (congrArg (fun z => (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) * z) ?_))
  exact ipM_theta X hμ j x y (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (Y.φ y)) (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (Y.φ (D.what₂.thetaP μ (j.1 + 1) x))) (hφ y) (hφ _)
end Canon
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (y : D.what₂.Mj (D.nd.j i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)), (F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = (P.M.loc i).real x → inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i))) F ⟨Y.φ y, Y.φ_mem y⟩ := by
  intro hL D P X A i j hj Y hc hμ x y F hF
  have hf : _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F = X.fn hμ j (hj.symm ▸ x) := by
    refine Eq.trans ?_ (ext_real_cast X.given.core.models.cV A hμ j _ hj (D.nd.j_range i).1 (D.nd.j_range i).2 x)
    show (X.R.cV j).ext (fun k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm
      ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))) = _
    rw [hF]
    rfl
  rw [_root_.GlobalTheory.ThetaRead.integral_theta_evaluation_thetaKO X hμ j _ hj Y hc x y, ← hf]
  rfl
end GlobalTheory.ThetaRead
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_automorphic_form_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (y : D.what₂.Mj (D.nd.j i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)), (F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = (P.M.loc i).real x → inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i))) F ⟨Y.φ y, Y.φ_mem y⟩ := by
  atlas_forward_decl _root_.GlobalTheory.ThetaRead.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.WeilDatumChars
theorem weil_chars_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).1 (P.tp.tup (D.nd.mu i) j) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).2 (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹) := by
  intro hL D P X A i j hj
  have hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hlev := X.recR.base.lev
  have hx : X.R.toLevCh.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq_of_heq X.cfEq X.Tp P.tp X.tpEq]
  have hxi := hlev.xi (X.tupT (D.nd.mu i))
  rw [hx] at hxi
  have hm := hlev.mu0 j
  have he := hlev.eta
  have hC : X.R.toLevCh.C = P.cf := X.cfEq
  rw [hC] at hm he
  exact ⟨GlobalTheory.Mem.TupChar.chrEq_mul hm hxi, GlobalTheory.ClassScalarValue.chrEq_mul_inv hm hxi he⟩
end GlobalTheory.WeilDatumChars
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chrTh_chrEq_tup_and_tup_mul_eta_inv : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).1 (P.tp.tup (D.nd.mu i) j) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).2 (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹) := by
  atlas_forward_decl _root_.GlobalTheory.WeilDatumChars.weil_chars_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)), GlobalTheory.NJoin.IsCanon X j hj Y → Nonempty (ThetaMod D P.M i Y (P.tp.tup (D.nd.mu i) j) P.cf.eta) := by
  intro hHC hCR hL D P X A i j hj Y hc
  have hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hC := X.given.core
  have hth : ∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j)
      (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i)) v) := fun v => hC.thP.pt_theta j _ _
  have h0 : _root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i)) ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ :=
    _root_.GlobalTheory.T.theta_lift_linear_form_alt hHC hCR hL D P X A i j hj Y hc hμ _ hth
  refine ⟨{ Ω := ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ)
            ω := _root_.GlobalTheory.ThetaTri.omegaMapAtLocal A i j hj hc hμ
            Λ := _root_.GlobalTheory.ThetaTri.canonicalPairingMap A i j hj hc hμ
            inv := fun h g φ F F' y y' hF hy => _root_.GlobalTheory.T.theta_lift_equivariance_alt hL D P X A i j hj Y hc hμ h g φ.1 φ.2 F F' y y' hF hy
            φ₀ := ⟨_, h0⟩
            read := fun x y F hF => _root_.GlobalTheory.T.theta_lift_automorphic_form_alt hL D P X A i j hj Y hc hμ x y F hF
            loc := ?_ }⟩
  intro s μw ηw hμw hηw
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.chrTh_chrEq_tup_and_tup_mul_eta_inv hL D P X A i j hj
  have hv : ∀ v, _root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i)) v ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.nV) (Fin D.R.r)
      (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ))
      (_ : IsLinAt (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) s μw ηw ι ∧
        ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (ι Φ)),
      LinearMap.range ι := fun v =>
    GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame D X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) D.R.nV D.R.r (A.PV j) (X.PW j) A.hF
      (A.stdV j) (A.stdW j) _ _ (X.R.ωP j (X.tupT (D.nd.mu i))) (hC.thP.ωP j _) _ _ h1 h2 s μw ηw hμw hηw _ (hth v)
  have hlin := _root_.GlobalTheory.ThetaTri.mem_iSup_range_isLinAt_valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
    (Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j))
    (· ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ)
    (fun β f hf => _root_.GlobalTheory.T.theta_lift_linear_form_alt hHC hCR hL D P X A i j hj Y hc hμ _ fun v => by
      simpa [GlobalTheory.ThetaTri.single1] using Formalism.IndefR.Fock.CCR.theta_smul hf (β v))
    s μw ηw _ hv
  exact GlobalTheory.ThetaTri.mem_iSup_isLinAt_omSub _ _ _ _ _ _ _ _ _ s μw ηw h0 hlin
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_theta_mod_of_is_canon : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)), GlobalTheory.NJoin.IsCanon X j hj Y → Nonempty (ThetaMod D P.M i Y (P.tp.tup (D.nd.mu i) j) P.cf.eta) := by
  atlas_forward_decl _root_.GlobalTheory.ThetaTri.nonempty_thetaMod_of_isCanon
end
end
