import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsRc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponentsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatibleStatement
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SupportCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
import Development.DiscreteGroups.GlobalIrreducibility.IneEqOfHasGreenLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.DiscreteGroups.GlobalIrreducibility.ActKEEqSelfLe
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.TypeRec
theorem exists_comp_irrSm_param_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (hrc : _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc) (Rw : GlobalTheory.HeightCounting.RowSide D)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (h1 : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR) (h2 : GlobalTheory.HeightCounting.RowDepth D rep) :
    ∃ cp : GlobalTheory.GoodTypes.Comp D, IsComp I rep cp ∧
      ∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  obtain ⟨cp, hc⟩ := exists_isComp_of_rowDepth I rep h2
  refine ⟨cp, hc, fun σ k v => ⟨?_, _root_.GlobalTheory.TypeRec.Model.locR_eq_rc_of_isRc_and_true_reading hrc hc h1 σ k v⟩⟩
  obtain ⟨s, hs, τ, -, e⟩ := hc σ k v
  rw [e]
  exact Model.irrSm_pull I k v τ
end GlobalTheory.TypeRec
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → ∃ cp : GlobalTheory.GoodTypes.Comp D, IsComp I rep cp ∧ ∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  atlas_forward_decl _root_.GlobalTheory.TypeRec.exists_comp_irrSm_param_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.SuppIne
open GlobalTheory.LocGL GlobalTheory.SmGL
section Transport
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
end Transport
end GlobalTheory.SuppIne
namespace GlobalTheory.SuppIne
open GlobalTheory.LocGL GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem ine_pol_rc_eq_char_pol_loc_rec {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D}
    {rc : GlobalTheory.SerSys.Corr D} (h : _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc) (k : Fin 2) (v : D.nd.PlG k) (n : ℕ)
    (σ : IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E))) (π : QRep (D.host.g k) n)
    (e : Nonempty (π ≅ pull I k v σ)) :
    D.naut.inePol (rc k v n π) (D.ntypes.tg k v) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls σ)).charPol
        (GlobalTheory.WeilDeligne.ineIncl _ ⟨D.ntypes.tg k v, D.ntypes.tg_mem k v⟩) := by
  rw [T.inePol _ _ _ (D.ntypes.tg_mem k v), h k v n σ π e,
    GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ (D.ntypes.tg_mem k v)]
theorem ine_pol_rc_eq_prod_of_has_support : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ (k : Fin 2) (v : D.nd.PlG k) (π : Supp.GLRep (D.host.g k)) (y : List (GlobalTheory.LocGL.IrrGL ℚ_[D.host.g k])), GlobalTheory.LocGL.HasSupport π.2.ρ (y : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[D.host.g k])) → D.naut.inePol (rc k v π.1 π.2) (D.ntypes.tg k v) = (y.map fun x => D.naut.inePol (rc k v x.1 (Rep.of x.rep)) (D.ntypes.tg k v)).prod := by
  intro hL D T I rc hRc k v π y hy
  obtain ⟨n, ρ⟩ := π
  have hs := hy.isSmooth
  have hi := hy.isIrreducible
  change D.naut.inePol (rc k v n ρ) _ = _
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hsupp : HasSupport (GlobalTheory.LocLanglands.cls (tr I k v ρ hs hi)).rep
      ((y : Multiset _).map (trGL (I.i k v) (continuous_symm I k v))) :=
    (hasSupport_comp (I.i k v) (I.cont k v) (continuous_symm I k v) hy).of_equiv (IrrGL.equivOf _ _ _)
  rw [_root_.GlobalTheory.SuppIne.ine_pol_rc_eq_char_pol_loc_rec hRc k v n _ ρ (iso_pull I k v ρ hs hi), H.supp _ _ hsupp, Multiset.map_coe, Multiset.map_coe,
    Multiset.prod_coe, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [Function.comp_apply, _root_.GlobalTheory.SuppIne.ine_pol_rc_eq_char_pol_loc_rec hRc k v x.1 _ (Rep.of x.rep)
    (iso_pull I k v (Rep.of x.rep) x.2.rep.smooth x.2.rep.irr)]
  rfl
end GlobalTheory.SuppIne
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace UpperTheory.One.M
open GlobalTheory GlobalTheory.SerSys GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil
theorem supportCompat_alt_alt : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  intro hZ hL D T I rc hrc k v π hi hs
  obtain ⟨L, y, hind, -, hsup, hf⟩ := GlobalTheory.SerSys.SuppTame.chain hZ (D.host.g k) π hi hs
  refine ⟨_, inInd_reps hind y hf, fun ρ hρ => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hρ
    have hc := hsup.isCusp (Multiset.mem_coe.2 hx)
    exact ⟨hc.1, Ysupp.IrreducibleSupport.isIrrRep_of_isIrreducible (IrrRep.irr _),
      GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal ℚ_[D.host.g k] x.1 _ x.rep hc.2⟩
  show D.naut.inePol (rc k v π.1 π.2) (D.ntypes.tg k v) = _
  rw [_root_.GlobalTheory.SuppIne.ine_pol_rc_eq_prod_of_has_support hL D T I rc hrc k v π y hsup, List.map_map]
  rfl
end UpperTheory.One.M
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  atlas_forward_decl _root_.UpperTheory.One.M.supportCompat_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TameRecord
theorem tame_param_le_of_tame_coupled : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ (L : ∀ k, LabelDatum (D.host.g k)) (k : Fin 2) (v : D.nd.PlG k) (κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen → DiscreteGroups.sglob.DzType.Rt.TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  intro hDZ hL D T I rc hrc L k v κ hκ ρ hb hρ τ P hP hinf
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, π⟩ := ρ
  have hs : GlobalTheory.PRep.IsSmooth π.ρ := hρ.2.2.1
  set σ := transRep I k v π hρ.2.1 hs
  have hsc : GlobalTheory.PRep.IsSupercuspidal σ.ρ :=
    isSupercuspidal_comp π.ρ _ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)
      (continuous_glMap _ (continuous_symm _ (I.i k v) (I.cont k v))) (continuous_glMap _ (I.cont k v))
      (glMap_apply_symm (I.i k v)) (glMap_symm_apply (I.i k v)) hρ.2.2
  have hcusp : (GlobalTheory.LocLanglands.cls σ).IsCusp := GlobalTheory.LocGL.IrrGL.isCusp_of.2 ⟨hρ.1, GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal _ n _ σ.ρ hsc⟩
  have hinf' : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)) τ := by
    rw [transRep_comp]; exact hinf
  show D.naut.inePol (rc k v n π) (D.ntypes.tg k v) = _
  rw [T.inePol _ _ _ (D.ntypes.tg_mem k v), hrc k v n σ π (iso_pull I k v π hρ.2.1 hs)]
  exact hDZ D.host.E D.nd.Om (D.host.g k) _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) (I.i k v) (I.cont k v) κ (L k) _ (D.ntypes.tg_mem k v) hκ n (Or.inr (DiscreteGroups.sglob.DzType.big_of_le_nV D k hb)) σ hcusp
    τ P hP hinf'
end DiscreteGroups.sglob.DzType.Rt
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.WeilDeligne GlobalTheory.SerSys.LabDepth in
theorem labLP_isLabel_and_actK_fix : Green → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (L : ∀ k, LabelDatum (D.host.g k)), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.SerSys.LabTie D L → DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc → ∀ k v (π : QRep (D.host.g k) D.R.r), IrrSm π → fixK1 π.ρ ≠ ⊥ → IsLabel D k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π)) ∧ ∀ y ∈ fixK1 π.ρ, actK π.ρ (D.ntypes.eSer k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π))) y = y := by
  intro hG hL D T I rc L hRc hLT hLab hP k v π hπ hfix
  let S : Sys (D.host.g k) := OfLabel.ofLabel (L k) (Bridge.five_le D k) hG
  have hSe : ∀ n f, S.e n f = eSerC (L k) n f := fun _ _ => rfl
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
  obtain ⟨f, hf⟩ : ∃ f, actK π.ρ (S.e D.R.r f) y ≠ 0 := by
    obtain ⟨T', hT'⟩ := S.sum D.R.r
    by_contra hcon
    push Not at hcon
    apply hy0
    rw [← LabLoc.actK_one_of_mem π.ρ hy, ← hT', LabLoc.actK_finset_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun f _ => hcon f
  have hne : S.e D.R.r f ≠ 0 := fun e => hf (by rw [e]; simp [actK])
  obtain ⟨hm, hd, h0⟩ := S.label _ f hne
  have hine : D.naut.inePol (rc k v D.R.r π) (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    rw [← (hLab k).1]
    exact hP k v D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) π hπ f ⟨y, hy, hf⟩
  have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have htame : (T.e _ (rc k v D.R.r π)).tame := by
    obtain ⟨σ, hiso, hσ⟩ := exists_pull D I k v π hπ hfix
    rw [hRc k v D.R.r σ π hiso]
    first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    refine tame_of_isTameWD ((fun hx => haveI := UpperTheory.One.M.charZero_compl (D.naut.plGw k v); _root_.UpperTheory.One.M.LawsM.depth hl _ (UpperTheory.One.M.good_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ _ hx) hx : _ → _) ?_)
    exact GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm hσ
  have hlab : D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π) = f := by
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hLT k v, WD.lab_eq_iff_of_tame hSet htame, ← T.inePol _ _ _ (D.ntypes.tg_gen k v).1, hine, e1,
      roots_multiset_prod_X_sub_C]
    exact ⟨hm, rfl⟩
  refine ⟨hlab ▸ ⟨hm, hd, h0⟩, fun z hz => ?_⟩
  rw [hlab, (hLab k).2 f, ← hSe]
  refine DiscreteGroups.sglob.DzType.Rt.actK_e_eq_self_le _ S (L k).teich (fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) D.R.nV ?_
    (hP k v) D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) π hπ f hm h0 ?_ z hz
  · rw [(hLab k).1]
    exact fun x hx y hy e => D.ntypes.teichC_inj k x y hx hy e
  · rw [(hLab k).1]; exact hine
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]
end GlobalTheory.SerSys
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
theorem exists_isRc_isClassMapD_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (I : Ident D), ∃ rc : GlobalTheory.SerSys.Corr D, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc ∧ ∀ k v, GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v) := by
  intro hL D T I
  obtain ⟨rc, hrc⟩ := _root_.GlobalTheory.TypeRec.Model.exists_isRc_alt hL T I
  refine ⟨rc, hrc, fun k v n π hπ => ?_⟩
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  obtain ⟨σ, e⟩ := GlobalTheory.TypeRec.Model.exists_pull I k v π hπ
  refine ⟨?_, fun π' hπ' hg => ?_⟩
  · rw [← T.dim, hrc k v n σ π e]
    exact H.dim _
  · obtain ⟨σ', e', hσ'⟩ := GlobalTheory.SerSys.LabDepth.exists_pull D I k v π' hπ' hg
    have hg' : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ') :=
      haveI := charZero_compl (D.naut.plGw k v)
      good_cls_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ σ' hσ'
    constructor
    · intro hr
      have h2 := congrArg (T.e _) hr
      rw [hrc k v n σ π e, hrc k v n σ' π' e'] at h2
      obtain ⟨f⟩ := pull_iso_of_cls_eq I k v σ σ' (_root_.UpperTheory.One.M.LawsM.inj H _ _ hg' h2)
      exact ⟨e.some ≪≫ f ≪≫ e'.some.symm⟩
    · rintro ⟨f⟩
      apply (T.e _).injective
      rw [hrc k v n σ π e, hrc k v n σ π' ⟨f.symm ≪≫ e.some⟩]
end UpperTheory.One.M
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem typeLab_of_local_m_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep := by
  intro hG hZ hDZ hL D T Rw rep L hLab hRow hDep hLT hTame
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := _root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc hL D T I rc hrc Rw rep hRow hDep
  have hP : DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc := DiscreteGroups.sglob.DzType.Rt.labParamLe_of D L rc hG (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D T I rc hrc)
    (fun k => GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule (D.host.g k))
    (fun k v => by
      obtain ⟨κ, hκ⟩ := hTame k v
      exact _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D T I rc hrc L k v κ hκ)
  have hfix : ∀ σ k v, fixK1 (cp σ k v).ρ ≠ ⊥ := by
    intro σ k v
    obtain ⟨s, τ, hsw, hloc, hfx⟩ := hDep σ k v
    have hT := hRow.1 σ s τ hloc
    have key : ∀ (w : PlE D.host) (hw : w = D.naut.plGw k v)
        (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
        T.e w (Rw.locR σ w) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) →
        GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥ →
        fixK1 (cp σ k v).ρ ≠ ⊥ := by
      intro w hw τ hT hfx
      subst hw
      have h1 := hrc k v D.R.r τ (pull I k v τ) ⟨CategoryTheory.Iso.refl _⟩
      have h2 : rc k v D.R.r (pull I k v τ) = rc k v D.R.r (cp σ k v) := by
        rw [← (hcp σ k v).2]
        exact (T.e _).injective (h1.trans hT.symm)
      obtain ⟨e⟩ := (((hcls k v) D.R.r (cp σ k v) (hcp σ k v).1).2 (pull I k v τ) (GlobalTheory.TypeRec.Model.irrSm_pull I k v τ)
        (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)).1 h2.symm
      exact GlobalTheory.LabPin.principalCongruenceFixedVectors_ne_bot_of_iso e (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)
    exact key s.w hsw τ hT hfx
  intro σ k v
  have hlab : D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r (cp σ k v)) := by
    rw [Rw.lab_eq, (hcp σ k v).2]
  obtain ⟨h1, h2⟩ := _root_.DiscreteGroups.sglob.DzType.Rt.labLP_isLabel_and_actK_fix hG hL D T I rc L hrc hLab hLT hP k v (cp σ k v) (hcp σ k v).1 (hfix σ k v)
  show IsLabel D k (D.nd.lab k σ v) ∧ ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → SerFix (rep σ) s (D.ntypes.eSer k (D.nd.lab k σ v))
  rw [hlab]
  exact ⟨h1, fun s hs => GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent D I rep cp hcomp σ k v _ h2 s hs⟩
end DiscreteGroups.sglob.DzType.Rt
end
section
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
end
end
end
