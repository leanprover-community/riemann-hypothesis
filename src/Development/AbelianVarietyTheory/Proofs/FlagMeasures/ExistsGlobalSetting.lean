import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOnto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatExistsOfForms0
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasWCore
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasInfXfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFromLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScGapBig
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMatchHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelConjHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RescaleStep3
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColDictCoreHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NeatTies
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IotaKerHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfLowest
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhLocOfIntegrablePh

section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), JExists D F := by
  intro D F X u wt hw
  obtain ⟨J, hJ, -⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u (F u) wt hw
  exact ⟨J, hJ⟩

end GlobalTheory
end

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St

theorem mExists_holds : ∀ D : D7, MExists D :=
  fun D => Formalism.L2.SG.Pf.mExists_of_cuts D weil_measure_compat infinite_measure_transfer

end GlobalTheory.St
end

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.GapAtRealPlaces

theorem gapBig_of_comparison (h : PI.ScGapBig.ScGapBig) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.GapBigOfGapHyp D := by
  intro hm hG τ

  have hr : PI.ScGapBig.rk48 D.R.k D.R.rS = D.R.r := by
    simp only [PI.ScGapBig.rk48, Formalism.BasicNotions.Ranks.r]
    omega

  have hgaps : ∀ (j : Fin (2 * D.R.rS + 2)) (hj : j.val + 1 < 2 * D.R.rS + 2),
      16 * (PI.ScGapBig.rk48 D.R.k D.R.rS : ℝ) ^ 19 ≤
        ((D.hc τ).b (Fin.cast hm.symm ⟨j.val + 1, hj⟩) : ℝ) - ((D.hc τ).b (Fin.cast hm.symm j) : ℝ) := by
    intro j hj
    have hlt : (Fin.cast hm.symm j).val + 1 < D.R.m := by
      rw [Fin.val_cast]
      omega
    have key := hG.2 τ (Fin.cast hm.symm j) hlt
    have hidx : (⟨(Fin.cast hm.symm j).val + 1, hlt⟩ : Fin D.R.m) = Fin.cast hm.symm ⟨j.val + 1, hj⟩ :=
      Fin.ext rfl
    rw [hidx] at key
    rw [hr]
    exact_mod_cast key
  obtain ⟨t, hto, ht5, ht1801, hgap⟩ :=
    h D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ)) (hr ▸ hG.1) hgaps
  exact ⟨t, hto, ht5, ht1801, hgap⟩

theorem gapBigOfGapHyp : ∀ D : D7, GapBigOfGapHyp D := by
  intro D
  exact gapBig_of_comparison scGapBig D

end GlobalTheory.GapAtRealPlaces
end

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem wlocExists_real : WlocExists :=
  scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

end GlobalTheory
end

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.WBlockExists

theorem nUnimodLoc : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  intro k r ε e f wf z0 z c hF hc hz
  exact n_unimodular_local k r ε e f wf z0 z c
    ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem realPlaceFunctionBlockExists_of_bessel_coef : BesselNVGap → CoefWeightedLoc → ∀ D : D7, GlobalTheory.St.WBlkExists D :=
  fun hB hCW D =>
    Formalism.L2.SG.Pf.WFL.weighted_block_exists_of_local_data quotient_product_compact Formalism.L2.SG.Pf.WFL.locHNProps_holds nUnimodLoc D hB hCW
      GlobalTheory.wlocExists_real (GlobalTheory.GapAtRealPlaces.gapBigOfGapHyp D)

end GlobalTheory.WBlockExists
end

section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem hcExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), HcExists D F := by
  intro D F X u wt ιA h0 hW hA c
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u wt ιA hW hA (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA)
  exact ⟨Φ.symm ((F u).cls0.y c * h0⁻¹), (hΦ _ _).2 (Φ.apply_symm_apply _)⟩

end GlobalTheory.St.G
end

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem fullExists_of_locTied : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.Pf.LocCP.LocTied D → Nonempty (Formalism.L2.SG.Full.Full X) := by

  intro D X hT
  exact Formalism.L2.SG.Pf.fullExists_tied Formalism.L2.SG.Pf.trExistsC_holds Formalism.L2.SG.Pf.lattice_steps_hold
    Formalism.L2.SG.Closed.LocCTied_holds D X (Formalism.L2.SG.Closed.level_subgroup_is_group X) hT

end GlobalTheory
end

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.RowsFiniteDim

theorem finiteDimensional_HHX : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (X : HidaSetting D),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → FiniteDimensional ℂ (HHX X) := by
  intro hHC D X h
  exact hHC X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.e X.B.Re X.B.e_adm.1
    X.B.e_adm.2.2.2.2.1 X.B.Re_spec
    X.B.H X.B.σ (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.w
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X v) (fun v => (X.low v).1)
    (GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X h) X.Rph X.Rph_spec

end GlobalTheory.RowsFiniteDim
end

section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory.FinitenessBundle

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_Gflag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} (n m : ℕ)
    (F : FlagG S r (n : E)) (F' : FlagG S r (m : E)) : star (Gflag F F') = Gflag F F' := by
  simp only [Gflag, star_sub, star_mul', star_star, star_natCast]
  ring

theorem finX_of_decay : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X),
    Formalism.L2.SG.WuDecay.WuDecay X → Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → FinX Y := by
  intro hR D X Y hW hI
  refine Formalism.L2.SG.Pf.finX_of_neat Y (fun u => Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) (fun u => ?_)
    (GlobalTheory.RowsFiniteDim.finiteDimensional_HHX hR D X hI) (fun u u' t => Formalism.L2.SG.Pf.FinXP.fibFin_holds D X Y u u' t)
    (fun u u' s₁ s₂ s₁' s₂' => Formalism.L2.SG.Pf.FinXP.pairIndep_of Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds D X Y u u' s₁ s₂ s₁' s₂')
    (fun u u' t => ?_) Formalism.L2.SG.Closed.VolPosC_holds
  · have hL : X.LevelSubgroupNormalized := Formalism.L2.SG.Closed.level_subgroup_properties X
    exact Formalism.L2.SG.Closed.InHHC_holds D X Y u hI (Formalism.L2.SG.Closed.FoldOKC_holds Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds D X Y u hL hW)
  · rw [← NumberField.IsCMField.complexConj_eq_self_iff]
    exact star_Gflag _ _ _ _

end GlobalTheory.FinitenessBundle
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict

namespace GlobalTheory.St.SpectralData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transport {D : D7} (F : ∀ u, Formalism.L2.Forms.Forms0 D u)
    (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (hι : ∃ ιA, GlobalTheory.St.IsAdeleIso X ιA) (u : D.what₂.Word) :
    ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  obtain ⟨wt, hw⟩ := GlobalTheory.St.WittT.wittExists D X u
  obtain ⟨ιA, hι⟩ := hι
  obtain ⟨g0, hg0⟩ := GlobalTheory.St.G.genusMatch_holds D F X u wt ιA hw hι
  obtain ⟨h0, hL, hKm⟩ := GlobalTheory.St.G.levelConj_holds D F X hK u wt ιA g0 hw hι hg0
  choose hcf hcr using GlobalTheory.St.G.hcExists_all D F X u wt ιA h0 hw hι
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := GlobalTheory.jExists_all D F X u wt hw
  exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hKm⟩

open Formalism.L2.SG.SplitPrimeNormLemmas in

theorem exists_setting (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent)
    (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
      ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧
        (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
        ∀ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  have hB : BesselNVGap := Formalism.L2.SG.Closed.BesselNVGap_holds
  have hC : CoefWeightedLoc := Formalism.L2.SG.Closed.CoefWeightedLoc_holds
  let A := Formalism.L2.SG.InstExistsPf.instanceOfRecord D
  obtain ⟨L⟩ := GlobalTheory.St.Lat.latExists_of_forms0 D (F D.u₀)
  obtain ⟨P⟩ := Formalism.L2.SG.Closed.PsiExists_holds D A
  obtain ⟨Rf⟩ := Formalism.L2.SG.Closed.RefExists_holds D A L
  obtain ⟨Xu⟩ := Formalism.L2.SG.Closed.XuExists_holds D A L Rf
  obtain ⟨Bu⟩ := Formalism.L2.SG.Closed.BunExists_holds D hC hG A L P Rf
  obtain ⟨Pi⟩ := Formalism.L2.SG.Closed.PiExists_holds D A L
  obtain ⟨Mu⟩ := Formalism.L2.SG.Closed.MuExists_holds D A L
  obtain ⟨Wb⟩ := GlobalTheory.WBlockExists.realPlaceFunctionBlockExists_of_bessel_coef hB hC D hG A L P Rf Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := GlobalTheory.St.mExists_holds D A L P Rf Xu Bu Pi Mu Wb
  obtain ⟨mg, hg, mw, hw, hM', ψ, hψ, hstd, hCm, hL⟩ :=
    GlobalTheory.St.Rescale.rescaleStep3 hSW D (mk A L P Rf Xu Bu Pi Mu Wb Mb) hb hM
  refine ⟨Formalism.L2.SG.SettingExistsMeasured.withMeas (mk A L P Rf Xu Bu Pi Mu Wb Mb) mg hg mw hw, hb, ψ, rfl,
    fun _ => HEq.rfl, hM', hψ, hstd, hCm, hL, fun hK u => ?_⟩
  exact exists_transport F _ hK ⟨RingEquiv.refl _, fun _ => rfl, fun _ => Iff.rfl⟩ u

theorem exists_spectralData : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (tr : ∀ u, Transport X u (F u)), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧ (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ u, LevelMatch X (tr u) Y.hK ∧ ColDictInto X (tr u) Y.hK ∧ ColDictBij X (tr u) Y.hK ∧ ColDictIsom X (tr u) Y.hK (Y.cs u) (hF.shInj u) := by
  intro hSW hMU hRF D F hG hLT
  obtain ⟨X, hb, ψ, hI, hι, hM, hψ, hstd, hCm, hL, hT⟩ := exists_setting hSW D F hG
  obtain ⟨Y⟩ := GlobalTheory.fullExists_of_locTied D X hLT
  obtain ⟨hWD, hph⟩ := Formalism.L2.SG.Pf.wuDecayOfGap_of_jsz hMU D hG X
  have hF : FinX Y := GlobalTheory.FinitenessBundle.finX_of_decay hRF D X Y hWD hph
  choose tr htr using hT Y.hK
  refine ⟨X, hb, ψ, Y, hF, tr, hI, hι, hM, hψ, hstd, hCm, hL, hph, fun u => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.St.colDictCore_holds D X u (F u) (tr u) Y.hK (htr u)
    (GlobalTheory.columnLevel_stabTriv D X Y.hK u)
  exact ⟨htr u, h1, h2, h3 _ (Y.cs u) (hF.shInj u) (Y.colReps u)⟩

end GlobalTheory.St.SpectralData
end
end
