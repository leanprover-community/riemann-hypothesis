import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.PeriodIntegrals.BesselMapUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLv3MvFixH
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameFOfDiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepPuVolAR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsoPairToTermSymm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Chi2ApplyOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorLevelMultiplicitySpaceMemGoodRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EvalConvGroupAlg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoices
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdelicPointCarriesRowLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultREqReL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvEvHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvRowJ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapHypOfNodes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSPackIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarCoeffOfEqReverse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfMemSuppSpan

section
open Formalism.BasicNotions

namespace GlobalTheory.Mem.SRe

theorem cdScale_eq_cdScaleOf : ∀ D : D7, cdScaleTie D → D.s.cdScale = Formalism.L2.SG.PairVal.cdScaleOf D := by
  intro D h
  exact GlobalTheory.Mem.Vol.Scale.cdScaleIs_unique D.cd ((GlobalTheory.Mem.Vol.cdScaleTie_iff D).1 h)
    (fun n ε => (Formalism.L2.SG.PairVal.cdScaleOf_tie D (Formalism.L2.SG.PairVal.cdScaleExists_of_tie D h) n ε).2)

end GlobalTheory.Mem.SRe
end

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem real_reS : ∀ (D : D7) (Z : SNew D), (Formalism.L2.Theta.RealTied D → Formalism.L2.Theta.RealTied (reS D Z)) ∧ StandardLattice.DstarD (reS D Z) = StandardLattice.DstarD D ∧ (StandardLattice.VolumeEqMass₂ D → StandardLattice.VolumeEqMass₂ (reS D Z)) :=
  fun _ _ => ⟨fun h => ⟨h.cdScale, h.dsig, h.dsig_all, h.vol⟩, rfl, fun h => h⟩

end GlobalTheory.Mem.SRe
end

section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

section Core

variable {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
  (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)
  (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y))

set_option maxHeartbeats 4000000 in

def sIsoRe (hR : Formalism.L2.Theta.RealTied D) (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) :
    SIso (reD D ⟨P.toNew hD j, N, hh⟩).s (sOf hF) where
  cd := by
    have h := (real_reS D (P.toNew hD j)).1 hR
    exact cdScale_eq_cdScaleOf (reD D ⟨P.toNew hD j, N, hh⟩) ((by with_unfolding_all exact (h.cdScale :)))
  del := rfl
  letter := rfl
  eHH := (by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))
  eCu := fun u => (by with_unfolding_all exact (eCure ⟨P.toNew hD j, N, hh⟩ P.fin hF u :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).1 :))
  volN := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).1 :))
  volH := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).2 :))
  eT := fun u u' => (by with_unfolding_all exact (eRT ⟨P.toNew hD j, N, hh⟩ P.Y u u' :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => by
    apply Subtype.ext
    exact (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.1 :))
  atP := fun p => (by with_unfolding_all exact ((hL p).some :))
  ePl := (by with_unfolding_all exact (Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.1 q :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.1 :))
  eP := fun u u' => (by with_unfolding_all exact ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose :))
  pfst := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1 :))
  psnd := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.1 :))
  s0 := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.1 :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.1 :))
  pval := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.2 :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} (p : RP P.Y u u') => by
    have h1 := ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 p.1.1).2.2.2.2.2.2.2.2.1
    have h2 := ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1
    exact (by with_unfolding_all exact (h1.trans (congrArg (fun t => Formalism.L2.SG.PairVal.massTerm t) h2) :))
  meanCount := by
    funext u u' w
    exact (by with_unfolding_all exact ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').2 w :))

end Core

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

set_option maxHeartbeats 4000000 in

theorem exists_sRest_re : ∀ (D : D7) (F : ∀ u, Forms0 D u) (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F F') (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)), Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.Theta.RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → ∃ S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro D F P hD j N hh F' hs hF hph hL hR hDs
  have hR' := (real_reS D (P.toNew hD j)).1 hR
  have hDs' : (reD D ⟨P.toNew hD j, N, hh⟩).what₂.Dstar = StandardLattice.DstarD (reD D ⟨P.toNew hD j, N, hh⟩) := (by with_unfolding_all exact (hDs.trans (real_reS D (P.toNew hD j)).2.1.symm :))
  have hAut : Formalism.MainNotions.S.AutTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.B
      (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.pl :=
    GlobalTheory.BundleTie.autTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X
      ⟨(by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))⟩ ((by with_unfolding_all exact (hph :))) hDs' (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).inst
      ((by with_unfolding_all exact (Formalism.L2.Theta.VolTieG.volTie hR'.vol :))) ((by with_unfolding_all exact (hR'.cdScale :))) ((by with_unfolding_all exact (hR'.dsig_all :)))
  refine ⟨⟨sIsoRe P hD j N hh hF hR hL, hAut, ?_, j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G), ?_, (by with_unfolding_all exact (hL :))⟩, rfl⟩
  · intro u x
    apply Subtype.ext
    exact (by with_unfolding_all exact (colDictL_reTr ⟨P.toNew hD j, N, hh⟩ (P.tr u) (hs u).2.1 (hs u).2.2 P.Y.hK x :))
  · intro x
    exact (by with_unfolding_all exact ((conjHH_eEECre ⟨P.toNew hD j, N, hh⟩ P.G (j x)).symm :))

end GlobalTheory.Mem.SRe
end
end

section
open Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting MeasureTheory
open scoped Classical

noncomputable section

namespace GlobalTheory.Mem.GoodExpand

theorem eg_eq_step {D : D7} (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) :
    eg X = fun x => if x ∈ X.B.I.Kset then D.ntypes.e0.coeff (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  funext x
  unfold eg
  by_cases hx : x ∈ X.B.I.Kset
  · have hex : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ := ⟨hx, red x, hr.1 x hx⟩
    rw [dif_pos hex, if_pos hx,
      Formalism.L2.SG.Pf.rowDictEgWellDef_holds X x _ _ (Classical.choose_spec hex.2) (hr.1 x hx)]
  · rw [dif_neg (fun h => hx h.1), if_neg hx]

theorem rg_expand : ∀ (D : D7) (X : HidaSetting D) (G : GoodOp X) [Fintype (G0g D.nd)] (red : X.B.I.Gf → G0g D.nd) (s : G0g D.nd → X.B.I.Gf), IsRedHom X red → (∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ) → ∀ φ : L2X X, (∀ k ∈ X.B.I.Kg X.B.g, X.B.R (1, k) φ = φ) → G.Rg φ = ∑ γ, D.ntypes.e0.coeff γ • X.B.R (1, s γ) φ := by
  intro D X G _ red s hr hs φ hφ
  have hT := G.Rg_spec
  rw [eg_eq_step X hr] at hT
  refine GlobalTheory.Mem.SRe.ConvStep.top_expand X hr s hs (fun γ => D.ntypes.e0.coeff γ) G.Rg hT φ ?_
  intro k hk
  have hsk := (hs (red k)).1
  have hk' : (s (red k))⁻¹ * k ∈ X.B.I.Kg X.B.g :=
    (GlobalTheory.Mem.SRe.ConvStep.fibre_iff X hr hsk k).1 ⟨hk, ((hs (red k)).2).symm⟩
  have hmul := (GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B).2.1
  have e : ((1, k) : X.B.I.GA) = (1, s (red k)) * (1, (s (red k))⁻¹ * k) := by
    ext
    · simp
    · simp
  rw [e, hmul]
  show X.B.R (1, s (red k)) (X.B.R (1, (s (red k))⁻¹ * k) φ) = _
  rw [hφ _ hk']

end GlobalTheory.Mem.GoodExpand
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eC_conj_of_match {R : RealDat D A Ks} {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) (g k : G') :
    RealDat.eC (A := A) D.what₂.embLL (g * k * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL k := by
  have e : ∀ x : G', RealDat.eC (A := A) D.what₂.embLL x = star (D.ntypes.e0.coeff (σ.symm x)) := fun x => by
    rw [hC, MulEquiv.apply_symm_apply]
  rw [e, e, show σ.symm (g * k * g⁻¹) = σ.symm g * σ.symm k * (σ.symm g)⁻¹ by simp, GlobalTheory.ProjComm.goodProjector_coeff_classFunction]

theorem eC_conv_of_match {R : RealDat D A Ks} {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) (g : G') :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) =
      RealDat.eC (A := A) D.what₂.embLL g := by
  have e : ∀ x : G', RealDat.eC (A := A) D.what₂.embLL x = star (D.ntypes.e0.coeff (σ.symm x)) := fun x => by
    rw [hC, MulEquiv.apply_symm_apply]
  simp only [e]
  rw [← GlobalTheory.ProjectedLift.conv_of_idem _ (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (σ.symm g), star_sum]
  refine Fintype.sum_equiv σ.symm.toEquiv _ _ fun a => ?_
  show _ = star (D.ntypes.e0.coeff (σ.symm a) * D.ntypes.e0.coeff ((σ.symm a)⁻¹ * σ.symm g))
  rw [star_mul', map_mul, map_inv]

theorem goodProjector_maps_rows_into_goodRows {R : RealDat D A Ks} {F : Face D A} (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf)
    {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) {S : MMap (MP R)} (hS : S ∈ MultR R F) :
    postOn (MP R) R.e0 S ∈ EP R F := by
  have hX : S ∈ GlobalTheory.Mem.Th.multAt R (R.levR F true) A.μ0 0 := by
    rw [GlobalTheory.Mem.Th.multAt_zero]; exact hS
  have h0 := GlobalTheory.Mem.Th.multAt_le R _ A.μ0 0 hX
  rw [GlobalTheory.Mem.Th.multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 S ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (eC_conv_of_match hC) h0
  refine ⟨GlobalTheory.KeepLevel.mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (S v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 h0).lev v
  refine GlobalTheory.KeepLevel.hasType_of_comm (L := R.dat0 R.triv) (P := R.levR F true) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 hX).lev v)
    fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact GlobalTheory.ProjComm.gaL_comm (L := R.dat0 R.triv) R.eG _ (eC_conj_of_match hC) g a0

set_option maxHeartbeats 1000000 in

theorem evalOn_good : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ), R.toLevCh.Is A.μ0 → R.models_inf → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → SeeAt R F X h t → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c hl hi hv hsee hJe
  obtain ⟨σ, red, hA, hB, hC⟩ := hsee.mat
  obtain ⟨J, hJ⟩ := hJe
  have hle : EP R F ≤ MultR R F := inf_le_left
  have hmult : ∀ S ∈ MultR R F, IsMultMap R.θ (MP R) (JR R F) (chiR R F) S := fun S hS =>
    (GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 hS
  have hGQ : ∀ S ∈ MultR R F, ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g := fun S hS =>
    ((hmult S hS).aut v₀).left
  choose s0 hs0 using hB.1.2.2.1
  have hs0' : ∀ γ, s0 γ ∈ X.B.I.Kset ∧ red (s0 γ) = γ := hs0

  have hinv : ∀ S : MultR R F, ∀ k ∈ X.B.I.Kg X.B.g,
      X.B.R (1, k) (star ((J S : conjRows X) : L2X X)) = star ((J S : conjRows X) : L2X X) := by
    intro S k hk
    classical
    have hkK : k ∈ X.B.I.Kset := hk.1
    have hrk : red k = 1 := (hB.1.2.2.2 k hkK).2 hk
    let a : G0g D.nd → ℂ := fun γ => if γ = 1 then 1 else 0
    let s : G0g D.nd → X.B.I.Gf := fun γ => if γ = 1 then k else s0 γ
    have hs : ∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ := by
      intro γ
      by_cases hγ : γ = 1
      · subst hγ
        simp only [s, if_pos rfl]
        exact ⟨hkK, hrk⟩
      · simp only [s, if_neg hγ]
        exact hs0' γ
    have hI := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB (S : MMap (MP R)) S.2
      ((J S : conjRows X) : L2X X) (hJ S).1 (hGQ _ S.2) a s hs
    have e1 : (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star ((J S : conjRows X) : L2X X))) : L2X X) =
        star (X.B.R (1, k) (star ((J S : conjRows X) : L2X X))) := by
      rw [Finset.sum_eq_single (1 : G0g D.nd)]
      · simp [a, s]
      · intro b _ hb
        simp [a, hb]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have hsum : (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (a (σ.symm g))) =
        actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG 1) := by
      unfold gaL
      rw [Finset.sum_eq_single (1 : G')]
      · have ha1 : a (σ.symm 1) = 1 := by simp [a]
        simp only [ha1, star_one, one_smul]
        rfl
      · intro b _ hb
        have hb' : σ.symm b ≠ 1 := by
          intro h1
          apply hb
          simpa using congrArg σ h1
        have ha0 : a (σ.symm b) = 0 := by simp [a, hb']
        simp only [ha0, star_zero, zero_smul]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have e2 : ∀ y : GA D (D.sp.Y 0),
        (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (a (σ.symm g))) ((S : MMap (MP R)) v₀) y =
          (S : MMap (MP R)) v₀ y := by
      intro y
      rw [hsum]
      have hB2 := hB.2 k hkK (S : MMap (MP R)) S.2 v₀ y
      rw [hrk, map_one σ] at hB2
      refine hB2.symm.trans ?_
      have hK2 := (Formalism.L2.SG.Closed.level_subgroup_properties X).1 k hk
      obtain ⟨hkJ, hkχ⟩ := hA k hK2.1
      have hχ1 : chiR R F (kap X h t k) = 1 := hkχ.trans (by rw [hK2.2, star_one])
      refine ((hmult _ S.2).lev v₀ _ hkJ y).trans ?_
      rw [hχ1, one_mul]
    have e3 : ((star (X.B.R (1, k) (star ((J S : conjRows X) : L2X X))) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
        (((J S : conjRows X) : L2X X) : X.B.I.GA → ℂ) := by
      rw [← e1]
      exact hI.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => e2 _) (hJ S).1.symm)
    have e4 := congrArg star (Lp.ext e3)
    rwa [star_star] at e4

  have key : ∀ S : MultR R F,
      ((J ⟨postOn (MP R) R.e0 S, hle (goodProjector_maps_rows_into_goodRows hl hi hC S.2)⟩ : conjRows X) : L2X X) =
        star (G.Rg (star ((J S : conjRows X) : L2X X))) := by
    intro S
    have hexp := GlobalTheory.Mem.GoodExpand.rg_expand D X G red s0 hB.1 hs0' _ (hinv S)
    have hI := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB (S : MMap (MP R)) S.2
      ((J S : conjRows X) : L2X X) (hJ S).1 (hGQ _ S.2) (fun γ => D.ntypes.e0.coeff γ) s0 hs0'
    have e1 : star (G.Rg (star ((J S : conjRows X) : L2X X))) = ∑ γ, star (D.ntypes.e0.coeff γ) •
        star (X.B.R (1, s0 γ) (star ((J S : conjRows X) : L2X X))) := by
      rw [hexp]
      change conjL (muX X) _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply, starRingEnd_apply]
    have e2 : (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (D.ntypes.e0.coeff (σ.symm g))) = R.e0 := by
      unfold RealDat.e0
      congr 1
      funext g
      rw [hC, MulEquiv.apply_symm_apply]
    rw [e1]
    apply Lp.ext
    refine (hJ _).1.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => ?_) hI.symm)
    rw [e2]
    rfl
  have hEPS : ∀ S : MultR R F, (S : MMap (MP R)) ∈ EP R F ↔ postOn (MP R) R.e0 S = S := by
    intro S
    constructor
    · intro hS
      exact sub_eq_zero.1 (LinearMap.mem_ker.1 hS.2)
    · intro e
      exact ⟨S.2, LinearMap.mem_ker.2 (sub_eq_zero.2 e)⟩
  have hconj : ∀ Fx : L2X X, Fx ∈ EEC X G → Fx ∈ conjRows X := fun Fx hF => (Submodule.mem_inf.1 hF).1
  let L0 : EP R F →ₗ[ℂ] L2X X :=
    (conjRows X).subtype ∘ₗ (J : MultR R F →ₗ[ℂ] conjRows X) ∘ₗ Submodule.inclusion hle
  have hL0 : ∀ S : EP R F, L0 S ∈ EEC X G := by
    intro S
    have hS1 : postOn (MP R) R.e0 (Submodule.inclusion hle S : MultR R F) = (Submodule.inclusion hle S : MultR R F) :=
      (hEPS _).1 S.2
    have k1 := key (Submodule.inclusion hle S)
    have e : (⟨postOn (MP R) R.e0 (Submodule.inclusion hle S : MultR R F),
        hle (goodProjector_maps_rows_into_goodRows hl hi hC (Submodule.inclusion hle S).2)⟩ : MultR R F) = Submodule.inclusion hle S :=
      Subtype.ext hS1
    rw [e] at k1
    have k2 : G.Rg (star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X)) =
        star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) := by
      have k3 := congrArg star k1
      rw [star_star] at k3
      exact k3.symm
    refine Submodule.mem_inf.2 ⟨(J (Submodule.inclusion hle S)).2, LinearMap.mem_ker.2 ?_⟩
    change G.Rg (star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X)) -
      star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) = 0
    rw [k2, sub_self]
  let L : EP R F →ₗ[ℂ] EEC X G := L0.codRestrict (EEC X G) hL0
  have hLv : ∀ S : EP R F, ((L S : EEC X G) : L2X X) = ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) :=
    fun S => rfl
  have hinj : Function.Injective L := by
    intro x y hxy
    have e1 : ((L x : EEC X G) : L2X X) = ((L y : EEC X G) : L2X X) := by rw [hxy]
    rw [hLv, hLv] at e1
    exact Submodule.inclusion_injective hle (J.injective (Subtype.ext e1))
  have hsurj : Function.Surjective L := by
    intro Fx
    let F' : conjRows X := ⟨(Fx : L2X X), hconj _ Fx.2⟩
    let S : MultR R F := J.symm F'
    have hJS : ((J S : conjRows X) : L2X X) = (Fx : L2X X) := by
      show ((J (J.symm F') : conjRows X) : L2X X) = _
      rw [LinearEquiv.apply_symm_apply]
    have hRg : G.Rg (star (Fx : L2X X)) = star (Fx : L2X X) := by
      have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 Fx.2).2
      exact sub_eq_zero.1 this
    have k1 := key S
    rw [hJS, hRg, star_star, ← hJS] at k1
    have hfix : postOn (MP R) R.e0 S = S := congrArg Subtype.val (J.injective (Subtype.ext k1))
    refine ⟨⟨(S : MMap (MP R)), (hEPS S).2 hfix⟩, Subtype.ext ?_⟩
    rw [hLv]
    exact hJS
  let j : EP R F ≃ₗ[ℂ] EEC X G := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hj : ∀ S : EP R F, ((j S : EEC X G) : L2X X) = ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) :=
    fun S => rfl
  refine ⟨⟨j, fun S => ?_⟩, ⟨v₀, hv, j, fun S => ?_⟩⟩
  · rw [hj]
    exact hJ _
  · rw [hj]
    exact hJ _

end GlobalTheory.Mem.SRe
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_goodRows_to_conjugate_goodRows : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ), R.toLevCh.Is A.μ0 → R.models_inf → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → SeeAt R F X h t → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c := by
  atlas_forward_decl GlobalTheory.Mem.SRe.evalOn_good
end

section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finX_spectralRedivisionFullChoices : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  first | exact @GlobalTheory.Mem.SRe.finX_reY | exact GlobalTheory.Mem.SRe.finX_reY | (intros; apply GlobalTheory.Mem.SRe.finX_reY <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_conjRows_eq {D : D7} (X : HidaSetting D) :
    Module.finrank ℂ (conjRows X) = Module.finrank ℂ (HHX X) := by
  let e := conjL (muX X)
  let j : conjRows X ≃+ HHX X :=
    { toFun := fun f => ⟨e f, f.2⟩
      invFun := fun g => ⟨e.symm g, by
        show e.toLinearEquiv.toLinearMap (e.symm g) ∈ HHX X
        simpa using g.2⟩
      left_inv := fun f => by ext1; simp
      right_inv := fun g => by ext1; simp
      map_add' := fun f g => by ext1; simp }
  have hbij : Function.Bijective (starRingEnd ℂ : ℂ → ℂ) :=
    Function.Involutive.bijective (fun z => by simp)
  have hr := rank_eq_of_equiv_equiv (starRingEnd ℂ : ℂ → ℂ) j hbij (fun r m => by
    ext1
    show e (r • (m : L2X X)) = (starRingEnd ℂ r) • e m
    exact e.map_smulₛₗ r m)
  unfold Module.finrank
  rw [hr]

theorem exists_rowJ_and_finrank_HHX : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c eE hc hv₀ hE hrange hnorm hle hJ1 hJ2
  refine ⟨fun hD => ?_, exists_rowJ_of_evalOn hc hv₀ hE hrange hnorm hle hJ2⟩
  obtain ⟨J1, -⟩ := hJ1
  have hD' : D.what₂.Dall = Module.finrank ℂ (MultR R F) := hD
  rw [hD', J1.finrank_eq, finrank_conjRows_eq]

end GlobalTheory.Mem.SRe

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowIsometry_conjugatedGoodRows_finrank : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  atlas_forward_decl GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem levCols_le_triv_and_finite : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  intro hF _ D G' _ _ Pl0 T A Ks _ _ _ R F _ hi _
  refine ⟨GlobalTheory.Mem.Th.EEat_le_triv R _, ?_⟩
  obtain ⟨U, hU, hJ⟩ := GlobalTheory.DefiniteEnd.exists_open_level (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
  exact GlobalTheory.MultFinite.hcFinite hF hi ⟨U, hU, fun k hk hk' => by
    obtain ⟨h1, h2⟩ := hJ k hk
    have hm : k ∈ levS (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) := ⟨hk', h1⟩
    have hc : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) k = 1 := congrArg Units.val h2
    obtain ⟨h3, h4⟩ := GlobalTheory.Mem.Th.principal_le_level (R.βY 0) (R.dat0 (R.levR F true)) (R.dat0 (R.levR F true)).P k hm
    exact ⟨h3, h4.trans hc⟩⟩

end GlobalTheory.Mem.SRe

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  atlas_forward_decl GlobalTheory.Mem.SRe.levCols_le_triv_and_finite
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2

namespace GlobalTheory.Mem.SRe

set_option maxHeartbeats 4000000 in

theorem exists_sRest_top : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro hDS hHC hCusp hDSU hRF D G' _ _ Pl0 T A Ks _ _ _ R F F0 P eE hGap hph hL hR hDs hLev hGrp hPin hE0 hM hRange hNorm hDall
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_finiteAdelicPoint_carries_rowLevel D G' Pl0 T A Ks R F P.X P.inst P.pin hLev hGrp hPin hE0
  obtain ⟨v₀, hv, c, hc, hev⟩ :=
    GlobalTheory.T.lowestVector_evaluation_identifies_levelRows_conj hDS hCusp hDSU hRF D G' Pl0 T A Ks R F P.X P.inst t P.pin hGap hLev hM.inf hM.ν0 ht
  have hg := GlobalTheory.T.evaluation_goodRows_to_conjugate_goodRows D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c hLev hM.inf hv ht hev
  have hle := (GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional hHC hCusp D G' Pl0 T A Ks R F hLev hM.inf hM.ν0).1
  obtain ⟨hfr, j, hj⟩ :=
    GlobalTheory.T.exists_rowIsometry_conjugatedGoodRows_finrank D G' Pl0 T A Ks R F P.X P.inst P.G t v₀ c eE hc hv hM.HE hRange hNorm hle hev hg.1
  refine ⟨hfr hDall, j, t, c, hc, ht, hg.2, hj, ?_⟩
  intro N hh F' hs
  have hF := GlobalTheory.T.finX_spectralRedivisionFullChoices D ⟨P.toNew (hfr hDall) j, N, hh⟩ P.X P.Y P.fin
  obtain ⟨S, hS⟩ := exists_sRest_re D F0 P (hfr hDall) j N hh F' hs hF hph hL hR hDs
  exact ⟨hF, S, hS⟩

end GlobalTheory.Mem.SRe
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectralLevel_objects_replacedStages : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  atlas_forward_decl GlobalTheory.Mem.SRe.exists_sRest_top
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.SRe

section Parts

variable {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
  {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
  {F0 : ∀ u, Forms0 a.D u} (P : SPack a.D F0) {F₁ : ∀ u, Forms0 (reL a Z).D u} (hs : SameL a Z F0 F₁)
  (hF : FinX (reY Z P.Y))

set_option maxHeartbeats 4000000 in

def packL : SPack (reL a Z).D F₁ := (by with_unfolding_all exact ((P.re Z hs hF) :))

set_option maxHeartbeats 4000000 in

def restL (S : SRest (P.re Z hs hF)) : SRest (packL a Z P hs hF) := (by with_unfolding_all exact (S :))

set_option maxHeartbeats 4000000 in

theorem restL_j (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) :
    (restL a Z P hs hF S).j = (by with_unfolding_all exact (j.trans (eEECre Z P.G) :)) := (by with_unfolding_all exact (hS :))

set_option maxHeartbeats 4000000 in

theorem nonempty_sAtL (R : RealDat a.D A Ks) (F : Face a.D A) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H)
    (t : GA a.D (a.D.sp.Y 0)) (c : ℝ) (hc : 0 < c) (see : SeeAt R F P.X P.inst t)
    (ev : EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c)
    (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (rowJ : RowJ R eE P.X P.inst P.G t j)
    (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) : Nonempty (SAtL a Z R F eE F₁) := by
  have h1 := mvRowJ a Z R P.X P.inst P.G t eE j rowJ
  have h2 := restL_j a Z P hs hF j S hS
  letI := alg (reL a Z) iK
  exact ⟨{ P := packL a Z P hs hF
           S := restL a Z P hs hF S
           t := tL a Z t
           c := c
           c_pos := hc
           see := (by with_unfolding_all exact ((mvSee a Z R F P.X P.inst t see) :))
           ev := (by with_unfolding_all exact ((mvEv_holds a Z R F P.X P.inst P.G t c ev) :))
           rowJ := by rw [h2]; exact (by with_unfolding_all exact (h1 :)) }⟩

end Parts

set_option maxHeartbeats 4000000 in

theorem satOfDiscreteSeries : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  intro h1 h2 h3 h4 h5 B C a G' _ _ Pl0 T A Ks _ _ _ R F F0 eE P hG hI hL hRT hDs hLev hgl hPin hE0 hMod hRg hN hDall
  obtain ⟨hD, j, t, c, hc, see, ev, rowJ, rest⟩ := GlobalTheory.T.exists_spectralLevel_objects_replacedStages h1 h2 h3 h4 h5 a.D G' Pl0 T A Ks R F F0 P eE hG hI hL hRT hDs
    hLev hgl hPin hE0 hMod hRg hN hDall
  refine ⟨P.toNew hD j, fun N hh F₁ hs => ?_⟩
  obtain ⟨hF, S, hS⟩ := rest N hh _ hs
  exact nonempty_sAtL a _ P hs hF R F eE t c hc see ev j rowJ S hS

end GlobalTheory.Mem.SRe

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectralObjects_over_replacedStages : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  atlas_forward_decl GlobalTheory.Mem.SRe.satOfDiscreteSeries
end

section
noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def formsRe {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    FormsTiedSym (reD D Z) u Ch chOf := by kcopy T

end GlobalTheory.Mem.SRe.ColRe

end
end

section
noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def hermRe (H : Formalism.L2.Herm.ColsHermS D) : Formalism.L2.Herm.ColsHermS (reD D Z) := by kcopy H

end GlobalTheory.Mem.SRe.ColRe

end
end

section
noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def colsRe (C : ColsTiedSym D) : ColsTiedSym (reD D Z) := (by with_unfolding_all exact ((@ColsTiedSym.mk (reD D Z) (hermRe Z C.herm) ((by with_unfolding_all exact ((fun u => formsRe Z (C.forms u)) :)))
    ((by with_unfolding_all exact (C.eV :)))
    ((by with_unfolding_all exact (C.piU :)))
    ((by with_unfolding_all exact (C.res :)))
    ((by with_unfolding_all exact (C.car0 :)))
    ((by with_unfolding_all exact (C.carC :)))
    ((by with_unfolding_all exact (C.carM :)))
    ((by with_unfolding_all exact (C.carP :)))
    ((by with_unfolding_all exact (C.lattice₂ :)))
    ((by with_unfolding_all exact (C.pr :)))
    ((by with_unfolding_all exact (C.prk :)))
    ((by with_unfolding_all exact (C.prC :)))
    ((by with_unfolding_all exact (C.z0 :)))
    ((by with_unfolding_all exact (C.ga :)))
    ((by with_unfolding_all exact (C.sp :)))
    ((by with_unfolding_all exact (C.piG :)))
    ((by with_unfolding_all exact (C.fr0 :)))
    ((by with_unfolding_all exact (C.gl_const :)))
    ((by with_unfolding_all exact (C.chi :)))
    ((by with_unfolding_all exact (C.frame_level_zero_const :)))
    ((by with_unfolding_all exact (C.frP_const :)))) :))

set_option maxHeartbeats 4000000 in

theorem sameF_colsRe (C : ColsTiedSym D) :
    SameForms0LevelsAndValues Z (fun u => (C.forms u).to0) (fun u => ((colsRe Z C).forms u).to0) := by
  intro u
  refine ⟨?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.cls0.lev) :))
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.cls0.y) :))
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.val0.eY) :))

set_option maxHeartbeats 4000000 in

theorem exists_colsTiedSym (D : D7) (Z : New D) (C : ColsTiedSym D) :
    ∃ C' : ColsTiedSym (reD D Z), SameForms0LevelsAndValues Z (fun u => (C.forms u).to0) (fun u => (C'.forms u).to0) :=
  ⟨colsRe Z C, sameF_colsRe Z C⟩

end GlobalTheory.Mem.SRe.ColRe

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.RowsLvl

section Scale

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℝ}
    (hc : 0 < c) {k : ℂ} (h : IsMultIP M μ 𝓕 T T' k) :
    IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' ((c : ℂ) * k) := by
  intro v v'
  obtain ⟨hi, he⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul]
    exact hi.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, he, ENNReal.toReal_ofReal hc.le, Complex.real_smul, mul_assoc]

theorem ipM_smul (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℝ}
    (hc : 0 < c) (hv : ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal c • μ) 𝓕 T T' = (c : ℂ) * ipM M μ 𝓕 T T' := by
  obtain ⟨v, hv⟩ := hv
  by_cases h : ∃ k, IsMultIP M μ 𝓕 T T' k
  · have hs := isMultiplicityInner_smul_measure M μ 𝓕 T T' hc (ipM_spec M μ 𝓕 T T' h)
    exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, hs⟩) hs
  · have h' : ¬ ∃ k, IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' k := by
      rintro ⟨k, hk⟩
      have e : ENNReal.ofReal c⁻¹ • ENNReal.ofReal c • μ = μ := by
        rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]
      have := isMultiplicityInner_smul_measure M _ 𝓕 T T' (inv_pos.2 hc) hk
      rw [e] at this
      exact h ⟨_, this⟩
    unfold ipM
    rw [dif_neg h, dif_neg h', mul_zero]

theorem mmap_eq_zero (M : DSModel V S) (hv : ¬ ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (T : MMap M) :
    T = 0 := by
  classical
  have : ∃ τ, ∀ w : M.sm τ, w = 0 := by
    by_contra hne
    push_neg at hne
    choose w hw using hne
    refine hv ⟨w, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
    rw [inner_self_ne_zero]
    exact fun h0 => hw τ (Subtype.ext h0)
  obtain ⟨τ, hτ⟩ := this
  ext v g
  rw [T.map_coord_zero τ (hτ (v τ))]
  rfl

end Scale

end GlobalTheory.Mem.R3.RowsLvl

namespace GlobalTheory.Mem.R3.RowsLvl

set_option maxHeartbeats 2000000 in

theorem range_eE_and_norm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → LinearMap.range Y.eE = (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e ∧ ∀ x, ‖Y.eE x‖ ^ 2 = RealDat.nP F.lv2 true * ‖x‖ ^ 2 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _
  have hE : R.models_HE := hP.char.base.models.HE
  have hEEc : (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc true =
      (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).map
        (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := rfl
  have hlift : Function.Injective (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) :=
    LinearEquiv.injective _
  refine ⟨?_, fun x => ?_⟩
  · ext h
    constructor
    · rintro ⟨x, rfl⟩
      have hm := (Y.Ish.jE x).2
      rw [Y.eE_read, hEEc] at hm
      obtain ⟨u, hu, he⟩ := hm
      have : u = R.HE.e (Y.eE x) := hlift he
      rw [Submodule.mem_comap, ← this]
      exact hu
    · intro hh
      rw [Submodule.mem_comap] at hh
      have hm : (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) (R.HE.e h) ∈
          (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc true := by
        rw [hEEc]; exact ⟨_, hh, rfl⟩
      refine ⟨Y.Ish.jE.symm ⟨_, hm⟩, ?_⟩
      have e1 := Y.eE_read (Y.Ish.jE.symm ⟨_, hm⟩)
      rw [LinearEquiv.apply_symm_apply] at e1
      exact (hE.1 (hlift e1)).symm
  · have hx := Y.tied.sharp.ee x x
    have hy := hE.2.2 (Y.eE x) (Y.eE x)
    have hnP : 0 < RealDat.nP F.lv2 true := by
      unfold RealDat.nP; exact_mod_cast Nat.card_pos
    by_cases hv : ∃ v : (R.MY 0).Vec, ∏ τ, ⟪(v τ : (R.MY 0).H τ), (v τ : (R.MY 0).H τ)⟫_ℂ ≠ 0
    · have e : ⟪x, x⟫_ℂ = (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * ⟪Y.eE x, Y.eE x⟫_ℂ := by
        rw [hx, hy]
        show ipMT _ _ _ _ _ = _
        unfold ipMT
        rw [Y.eE_read]
        erw [LinearEquiv.symm_apply_apply]
        exact ipM_smul _ _ _ _ _ (inv_pos.2 hnP) hv
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
      have e' : ‖x‖ ^ 2 = (RealDat.nP F.lv2 true)⁻¹ * ‖Y.eE x‖ ^ 2 := by
        apply Complex.ofReal_injective
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        exact e
      rw [e', ← mul_assoc, mul_inv_cancel₀ hnP.ne', one_mul]
    · have h0 : Y.eE x = 0 :=
        hE.1 (by rw [mmap_eq_zero _ hv (R.HE.e (Y.eE x)), mmap_eq_zero _ hv (R.HE.e 0)])
      have h1 : (Y.Ish.jE x).1 = 0 := by
        rw [Y.eE_read, h0, map_zero]; exact map_zero _
      have hx0 : x = 0 := (LinearEquiv.map_eq_zero_iff _).1 (Submodule.coe_eq_zero.1 h1)
      simp [h0, hx0]

end GlobalTheory.Mem.R3.RowsLvl
end
end

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteSeries_formalDegree_product : DiscreteSeriesExist → FormalDegreeFormula₂ → ∀ (cd : CDHaar) (R : Ranks) (P : HCParam R), (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)), IsDS (epsSH R) (lamSH R P) σ ∧ IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ (trueDsig R P)) ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
  first | exact @GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig | exact GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig | (intros; apply GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Mem.SRe.UpS

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowHyp {D : D7} (p : RowPk D) : Prop :=
  p.R.toLevCh.Is p.A.μ0 ∧ p.R.grp_levels p.F ∧ GrpPin p.R ∧ p.R.IsModels ∧
    LinearMap.range p.eE = (p.R.EEat (p.R.levR p.F true)).comap p.R.HE.e ∧
    (∀ x, ‖p.eE x‖ ^ 2 = RealDat.nP p.F true * ‖x‖ ^ 2) ∧ DallTie p.R p.F

set_option maxHeartbeats 4000000 in

theorem rowHyp_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : R3.Pins R F cG)
    (hH : R3.Holds R F) : RowHyp (⟨G, Pl0, T, A3.A, Ks, R.toRealDat, F.lv2, Y.eE⟩ : RowPk D) := by
  have hr := R3.RowsLvl.range_eE_and_norm D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨plg, iso, h⟩ := hP.keep.grp
  exact ⟨hP.char.base.lev, hP.char.base.grp.levels, ⟨R.eG.trans cG, plg, iso, h⟩, hP.char.base.models, hr.1, hr.2, Y.dall⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 4000000 in

theorem rowHyp_pkOf {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) : RowHyp (pkOf r) :=
  (by with_unfolding_all exact ((rowHyp_read r.r.z.R r.r.z.F r.r.z.cG r.r.Y r.r.z.pins r.r.intersectionNumber_baseChange) :))

def reSt {C : Cols B} (a : Late B C) (Zs : SNew a.D) : SStage B C a.W := reStage a.st Zs

def SatNew : Prop :=
  ∀ (B : Base) (C : Cols B) (a : Late B C) (p : RowPk a.D) (F0 : ∀ u, Forms0 a.D u) (P : SPack a.D F0), GapHyp a.D →
    Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D →
    a.D.what₂.Dstar = StandardLattice.DstarD a.D → IdempotentRealFixed a.D → RowHyp p →
    ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁)

set_option maxHeartbeats 4000000 in
theorem satOfDiscreteSeries (h1 : GlobalTheory.Dec.DSInfChar) (h2 : GlobalTheory.Published.HarishChandraFinite) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.DiscreteSeriesUpqUnique) (h5 : Formalism.L2.SG.RowsDef.RowsFinDim) : SatNew :=
  fun B C a p F0 P g i l r d e ⟨a1, a2, a3, a4, a5, a6, a7⟩ =>
    GlobalTheory.T.exists_spectralObjects_over_replacedStages h1 h2 h3 h4 h5 B C a p.G' p.Pl0 p.T p.A p.Ks p.R p.F F0 p.eE P g i l r d a1 a2 a3 e a4 a5 a6 a7

set_option maxHeartbeats 8000000 in

theorem sat_col (a : w.Lt) (col : ColT w a) (p : RowPk (Late.D a)) (Zs : SNew (Late.D a))
    (H : ∀ (N : ∀ u, Submodule (𝓞 (Late.D a).what₂.LL) ((Late.D a).div.Nu u).V) (hh : (Late.D a).what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ (fun u => (col.C.forms u).to0) F₁ →
        Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁))
    (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) (col' : ColT w (upL a (reSt a Zs) N h)) :
    Nonempty ((p.up a (reSt a Zs) N h).SAt fun u => (col'.C.forms u).to0) := by
  let Zn : New (Late.D a) := ⟨Zs, (by with_unfolding_all exact (N :)), (by with_unfolding_all exact (h :))⟩
  obtain ⟨C', hC⟩ := ColRe.exists_colsTiedSym (Late.D a) Zn col.C
  let F₀ : ∀ u, Forms0 (reD (Late.D a) Zn) u := fun u => (C'.forms u).to0
  let F₁ : ∀ u, Forms0 (reL a Zn).D u := (by with_unfolding_all exact (F₀ :))
  have hF : SameL a Zn (fun u => (col.C.forms u).to0) F₁ := (by with_unfolding_all exact (hC :))
  obtain ⟨s⟩ := H Zn.N Zn.h F₁ hF
  have c := CarModel.sameStd B f T w a Zn col ((by with_unfolding_all exact (col' :))) F₁ hF
  exact ⟨CarModel.satCar (D := Late.D (upL a (reSt a Zs) N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) (p.up a (reSt a Zs) N h) ((by with_unfolding_all exact (s :)))⟩

def RealOf : Prop := ∀ D : D7, VolTieG D → D.s.cdScale = Vol.trueScale D.cd → (∀ τ, D.dsig τ = Vol.trueDsig D.R (D.hc τ)) → RealTied D

def PackEx : Prop := ∀ (D : D7) (F : ∀ u, Forms0 D u), GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D →
  ∃ P : SPack D F, Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I)

set_option maxHeartbeats 4000000 in

theorem real_of (hR : RealOf) (a : w.Lt) (g : GIs2 K w a.G) (hs : a.S.s.cdScale = Vol.trueScale a.G.cd)
    (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ)) : RealTied (w.D a) :=
  hR (w.D a) (g a.W a.V a.S a.N).1 ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :)))

set_option maxHeartbeats 8000000 in

theorem lv4_of {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) (hO : K.Over B.toPre)
    (a : w.Lt) (l : Lv3 p.s K w a) (gap : GapHyp (Late.D a)) (hdel : a.S.s.Del = (Delv K.s K.cD : ℚ))
    (hs : a.S.s.cdScale = Vol.trueScale a.G.cd) (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ))
    (loc : Formalism.L2.SG.Pf.LocCP.LocTied (Late.D a)) : ∃ b : w.Lt, Nonempty (Lv4 p.s K w b) := by
  obtain ⟨vt, -, ⟨col⟩⟩ := l.g a.W a.V a.S a.N
  have col₀ : ColT w a := col.toColT
  obtain ⟨P, hI⟩ := hP (Late.D a) (fun u => (col₀.C.forms u).to0) gap loc
  have real₀ : RealTied (Late.D a) := (by with_unfolding_all exact ((real_of hR a l.g hs hd) :))
  have dstar : (Late.D a).what₂.Dstar = StandardLattice.DstarD (Late.D a) := (sizes_eq_count K (Late.st a) hO (hV _ real₀.vol) hd).2
  have e0 : IdempotentRealFixed (Late.D a) := hE _ (l.what₂.grp.eSerTie a.V a.S a.G)
  obtain ⟨Zs, H⟩ := hN B w.C a (pkOf l.what₂) _ P gap hI loc real₀ dstar e0 (rowHyp_pkOf l.what₂)
  let b : w.Lt := upL a (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨l', e⟩ := hM K B f T w a l (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨-, -, ⟨col'⟩⟩ := l'.g b.W b.V b.S b.N
  have col₁ : ColumnDataSplitPrimes K w b := col'
  obtain ⟨s⟩ := sat_col a col₀ (pkOf l.what₂) Zs H _ _ col₁.toColT
  have s' : SX K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT := by
    rw [sx_eq l'.what₂ col₁.toColT, e]
    exact s
  have x : p.S K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT s' := by
    rw [hS]
    exact PUnit.unit
  exact ⟨b, ⟨⟨l', col₁, real_of hR b l'.g ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :))), (by with_unfolding_all exact (hd :)), (by with_unfolding_all exact (hdel :)), ⟨s', x⟩⟩⟩⟩

set_option maxHeartbeats 8000000 in

theorem step_of {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) :
    StepW (pinAnd (Has3 p.s)) (Has4 p.s) := by
  refine Step.of_evG ((evG_of_ev GlobalTheory.Mem.Top.NodeGap.ev_gapHyp).imp fun K _ _ _ _ gap B f T hO _ _ _ w => ?_)
  rintro ⟨-, Z, ⟨l⟩⟩
  obtain ⟨S, hdel, hs, hd, loc⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C Z.W Z.G.cd hO (SpectralModel.colsPos_of Z.S) (SpectralModel.rows_le_of Z.S)
  obtain ⟨l₀, -⟩ := hM K B f T w Z l S (fun u => (Z.V.div.Nu u).L) Z.V.div.h
  exact lv4_of p hS hM hN hR hP hV hE hO _ l₀ (gap _ hO) hdel hs hd ((by with_unfolding_all exact ((loc (upL Z S (fun u => (Z.V.div.Nu u).L) Z.V.div.h).V Z.N Z.G) :)))

theorem realOf (h1 : Vol.DiscreteSeriesExist) (h2 : Vol.FormalDegreeFormula₂) : RealOf := by
  intro D hv hs hd
  refine ⟨?_, ?_, ?_, hv⟩
  · rw [Vol.cdScaleTie_iff, hs]
    exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd
  · intro τ
    unfold Formalism.L2.Theta.IsDsig
    rw [hs, hd τ]
    exact (GlobalTheory.T.exists_discreteSeries_formalDegree_product h1 h2 D.cd D.R (D.hc τ)).1
  · intro τ H _ _ σ d hσ hf
    rw [hs] at hf
    rw [hd τ]
    exact (GlobalTheory.T.exists_discreteSeries_formalDegree_product h1 h2 D.cd D.R (D.hc τ)).2 H σ d hσ hf

theorem goodIdempotent_real_of_harishChandra_series (D : D7) (h : GlobalTheory.GLq.ESerTie D) : IdempotentRealFixed D :=
  GlobalTheory.GoodIdemReal.star_coeff_of_reverse D fun k g hm h0 x => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨L, -, he⟩ := h k
    rw [he, he]
    exact DFunLike.congr_fun (GlobalTheory.GLq.GalSer.eSerC_map L _ D.R.r hm (GlobalTheory.SeriesSupport.rel_dual L hm h0)) x

theorem stepW_has4 : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), p.S = SExt.none → LevelThreeCondition p.s → StepW (pinAnd (Has3 p.s)) (Has4 p.s) :=
  fun h1 h2 h3 h4 h5 hW hB hD hF _ _ p hS hM =>
    step_of p hS hM (satOfDiscreteSeries h1 h2 h3 h4 h5) (realOf hD hF) (GlobalTheory.Mem.SRe.exists_sPack_integrable hW hB h5)
      (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hW)) goodIdempotent_real_of_harishChandra_series

end GlobalTheory.Mem.SRe.UpS

end
end
