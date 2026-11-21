import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportStatementOfDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportStatementOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtCompStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateBaseOfReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateBaseOfReciprocity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesUnitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwOneOfStepsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeriesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseGeOfStepsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGeStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_admissible' : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.twAdm_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie
namespace GlobalTheory.TwistChr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}
end Point
theorem twChr_of_twAdm_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter := fun _ h =>
  Closed.imp h fun _ _ _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p r hm w hw j _ hρ hA =>
    have hw' := (p.tw_iff w).1 hw
    have h1 := chrEq_tw hm.2.2 hw' (H x hx h0 i p r hm w hw j).1 hρ hA
    ⟨h1, xi_eq hw' hA.1 j _ h1⟩⟩
end GlobalTheory.TwistChr
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_of_artin' : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter := by
  atlas_forward_decl _root_.GlobalTheory.TwistChr.twChr_of_twAdm_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowAt : _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem canEx_holds_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalExists :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p _ _ w _ j => canEx_at p w j⟩⟩⟩
end GlobalTheory.BigOn.Exp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigOn_canEx : _root_.GlobalTheory.BigOn.Exp.CanonicalExists := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.canEx_holds_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
noncomputable section
open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion
namespace GlobalTheory.BigOn.Exp.ProjRd
attribute [local instance] GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.algKK
end GlobalTheory.BigOn.Exp.ProjRd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.BigOn.Exp.canProj_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ w _ j rd hrd y => ?_⟩⟩
  obtain ⟨-, -, -, hid, -⟩ := p.grpRecPin
  exact GlobalTheory.BigOn.Exp.ProjRd.rd_eOp (Fm.ex x hx i).nch_tie (p.R.eG.trans p.cG) p.Sx ((j : ℕ) + 1) ((R2 p).FW j)
    (p.nexp.fi j) (GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)) (p.nexp.geq j) (p.nexp.rho _ (Nat.le_add_left _ _) j.2) (p.nexp.chi _ (Nat.le_add_left _ _) j.2)
    (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2) (p.nexp.act _ _ _ (Nat.le_add_left _ _) j.2)
    (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    (fun g => (Fm.D x i).what₂.embLL.injective ((hid g).trans ((Fm.D x i).nStage_trivialCharacter_coeff_eq _).symm)) rd hrd y
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigOn_canProj : _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.canProj_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem tieRat_of_alt (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hR : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) : _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  unfold _root_.GlobalTheory.BigOn.Exp.CompatibilityRational _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hA hR).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j Z => ?_⟩
  obtain ⟨hA', hR'⟩ := hx0 x hx hle i p hp
  have hrow := hR' hm w hw j Z.ρ Z.good Z.pin (levelOf_exportTie Z)
  have hs := Z.scalar ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hrat := hs.rat hrow
  obtain ⟨ν, hn, -⟩ := hrow
  obtain ⟨hok, hcl, -⟩ := hA' hm w hw j
  exact ⟨hs.norm ⟨ν, hn⟩, hrat.1, fun s h P hd => hrat.2.1 _ _ _ hok hcl s h P hd⟩
end GlobalTheory.BigOn.Exp
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieRat_of_twAdm_and_at : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace → _root_.GlobalTheory.BigOn.Exp.CompatibilityRational := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.tieRat_of_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp.Adapt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
section Point
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
end GlobalTheory.BigOn.Exp.Adapt
open GlobalTheory.BigOn.Exp.Adapt in
theorem GlobalTheory.BigOn.Exp.adaptEx_alt : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH _ _ => ⟨0, fun x hx _ i p _ hm w _ j => adapt_at p w j hm⟩⟩⟩
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptEx' : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.adaptEx_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
end Point
def SeriesUnitLAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f
theorem conjBase_of_readInj_latSmallGen_seriesUnit (hI : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt) (hG : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators) (hU : _root_.GlobalTheory.BigOn.Exp.SeriesUnitLAlt) : _root_.GlobalTheory.BigOn.Exp.ConjugateBase := by
  unfold _root_.GlobalTheory.BigOn.Exp.ConjugateBase _root_.GlobalTheory.BigOn.Exp.ReadInjAlt _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators _root_.GlobalTheory.BigOn.Exp.SeriesUnitLAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine ((Formalism.MainNotions.Closed.and hI hG).and hU).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := (h.1.1.and h.1.2).and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hS hN hR hF => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := hx0 x hx hle i p hp
  have hL : ρ.LevelOf (Fm.D x i).nexp := levelOf_of_sameBut hm.2.2 hρ' hρ hF.1.1 hpin hS.symm hF.2.2.2
  exact le_antisymm
    (baseLat_le p w j (a1 hm w hw j) (a2 hm w hw j) (a3 hm w hw j) ρ ρ' hρ hρ' ν ν' hpin hL hF.1.1 hS hN hF.2.1 hR.1 hF.2.2.1.1)
    (baseLat_le p w j (a1 hm w hw j) (a2 hm w hw j) (a3 hm w hw j) ρ' ρ hρ' hρ ν' ν hF.1.1 hF.2.2.2 hpin hS.symm hF.2.1 hN hF.2.2.1.1 hR.1)
theorem conjBase_of_cusp_decay_and_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ConjugateBase := fun h1 h2 h3 h4 =>
  _root_.GlobalTheory.BigOn.Exp.conjBase_of_readInj_latSmallGen_seriesUnit _root_.GlobalTheory.BigOn.Exp.readInj_alt _root_.GlobalTheory.T.latSmallGen' (_root_.GlobalTheory.T.norm_ratio_realization_same_alt h1 h2 h3 h4)
end GlobalTheory.BigOn.Exp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ConjugateBase := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem exportSt_of_hypotheses_alt (hC : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity)
    (hR : GlobalTheory.Published.RayClassFieldSt) (hD : GlobalTheory.Published.DiscreteSeriesCover) (hW : GlobalTheory.Published.CasselmanWallach)
    (hS : GlobalTheory.SerStd.SeriesRatS) : _root_.GlobalTheory.BigOn.ExportedStatement :=
  have tA := _root_.GlobalTheory.T.twist_admissible'
  have tC := _root_.GlobalTheory.T.twist_character_of_artin' hA tA
  have row := _root_.GlobalTheory.T.at_statement_of_low_weight_twAdm hC hA hR hS _root_.GlobalTheory.T.lowAt tA
  _root_.GlobalTheory.BigOn.Exp.InductionConditions.exportSt ⟨_root_.GlobalTheory.T.bigOn_canEx, _root_.GlobalTheory.T.bigOn_canProj, tA, row, _root_.GlobalTheory.T.tieRat_of_twAdm_and_at tA row, _root_.GlobalTheory.T.reciprocity_side_of_twAdm tA, _root_.GlobalTheory.T.adaptEx',
    _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat hC hA hR hS, _root_.GlobalTheory.T.conjTw_of_discrete_series_and_casselman_wallach hC hA hR hD hW hS tA tC, _root_.GlobalTheory.T.baseLe_of_cuspRapidDecay_artin_rayClassField hC hA hR, _root_.GlobalTheory.T.baseGe_of_cuspRapidDecay_artin_rayClassField_seriesRat hC hA hR hS,
    _root_.GlobalTheory.T.twist_upper_bound_of_prints hC hA hR tA tC, _root_.GlobalTheory.T.twist_lower_bound_of_prints hC hA hR hS tA tC⟩
end GlobalTheory.BigOn.Exp
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exportSt_of_discrete_series_cover : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt
end
end
