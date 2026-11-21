import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsOfInputsAndJumps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCountStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisTailStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointsOfTiedLattices
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisLastStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroRecursionOfEigenStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroRecursionOfEigen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigStringAllStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenGoodOfAdmissibilityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenGoodOfAdmissibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsAClose
end GlobalTheory.RowsAClose
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLocal_a_conditions_of_jumpsCard : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.RowsAAlt D := by
  first | exact @_root_.UpperTheory.GalS.a_close_main | exact _root_.UpperTheory.GalS.a_close_main | (intros; apply _root_.UpperTheory.GalS.a_close_main <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsBClosing
end GlobalTheory.RowsBClosing
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.b_conditions_pairLift_splitBC_repOfLoc_of_a : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  first | exact @_root_.UpperTheory.One.M.latticesB_closing_alt | exact _root_.UpperTheory.One.M.latticesB_closing_alt | (intros; apply _root_.UpperTheory.One.M.latticesB_closing_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.TypeNZJoin
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
theorem typeNZRec_of_join_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) →
    ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i := by
  intro hL D P X _ hT i hS hG x hx
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hr := D.nd.j_range i
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i := ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  exact of_cast hj _ fun f hf h0 => inj_at X hT i hS hG hμ j hj x hx f hf h0
end GlobalTheory.TypeNZJoin
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_nonzero_recursion_of_eigen' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) → ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i := by
  atlas_forward_decl _root_.GlobalTheory.TypeNZJoin.typeNZRec_of_join_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.EigGoodTypes
theorem eigC_le_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (hMt : MtParTie D.nd D.naut D.ntypes) (hbc : Formalism.MainNotions.SumRepresentations.adm1 D) (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D)
    (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) :
    ∃ σ' : D.ntypes.Par, eigC D.nd D.naut i x ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' ∧ D.ntypes.goodPar σ' := by
  obtain ⟨-, Sig, ⟨P0, hP0, hB0⟩, hg⟩ := hx
  let σ' : D.ntypes.Par := P.ty.par.eP.symm ⟨Sig, sig_parC h0 h4 h5 hB0 hg⟩
  have hloc : ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w := fun w => by
    have e : P.ty.par.eP σ' = ⟨Sig, sig_parC h0 h4 h5 hB0 hg⟩ := Equiv.apply_symm_apply _ _
    rw [P.ty.par.locPar_def, e]
  refine ⟨σ', ?_, ?_⟩
  · rw [hMt i σ']
    refine iSup₂_le fun Q hQ => le_iSup₂_of_le Q ⟨Sig, fun w => (hloc w).symm, ?_⟩ le_rfl
    have hQ' : D.naut.ptV i Q = some x := hQ
    obtain ⟨Pa, hPa⟩ := hbc i Q
    have hperm := ((h41 i).2.1 P0 Q (by rw [hP0]; simp) (hP0.trans hQ'.symm)).1 _ _ hB0 hPa
    exact GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hPa
  · intro k
    simp only [D.ntypes.labPar_def, hloc]
    exact hg k
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp),
    _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → Formalism.MainNotions.SumRepresentations.tieLab D → MtParTie D.nd D.naut D.ntypes → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.tie0 D →
    Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → GlobalTheory.NRows.GoodIdempotentFixesLocalisationForms D → GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X → ∀ i, GlobalTheory.NJoin.EigGood X i := by
  intro hL D P X h41 _ hMt hbc h0 h4 h5 hE0 hRead i hμ j hj x hx f hf y hy
  obtain ⟨σ', hle, hgood⟩ := _root_.GlobalTheory.EigGoodTypes.eigC_le_alt P h41 hMt hbc h0 h4 h5 i x hx
  exact (hRead _ hμ j f y hy).1 (onMt_cast hj f (hE0 i σ' _ (hle hf) hgood))
end GlobalTheory.EigGoodTypes
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigGood_of_archimedean_signature_adm5 : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → Formalism.MainNotions.SumRepresentations.tieLab D → MtParTie D.nd D.naut D.ntypes → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → GlobalTheory.NRows.GoodIdempotentFixesLocalisationForms D → GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X → ∀ i, GlobalTheory.NJoin.EigGood X i := by
  atlas_forward_decl _root_.GlobalTheory.EigGoodTypes.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsAll
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.PointConditions' D := by
  intro hP hHC hCusp hL D I hJ
  have a : _root_.GlobalTheory.NRows.RowsAAlt D := _root_.GlobalTheory.T.thetaLocal_a_conditions_of_jumpsCard hP hL D I.P hJ
  obtain ⟨J⟩ := _root_.GlobalTheory.T.nonempty_join_of_agree hHC hCusp hL D I.P I.X I.agree
  obtain ⟨lamLoc, rank⟩ := GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars D I.isot I.lam
  obtain ⟨b, trip⟩ := _root_.GlobalTheory.T.b_conditions_pairLift_splitBC_repOfLoc_of_a hP hL D I.P J a I.adm1 lamLoc
  have Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D := I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) a b
  have c : GlobalTheory.NRows.RowsC D := _root_.GlobalTheory.T.c_statement_of_pair_lift_splitBC_repOfLoc hL D I.P J a b I.adm1 I.isot Conclusion1 trip
  refine ⟨a, b, c, fun i => ?_, rank⟩
  exact _root_.GlobalTheory.T.type_nonzero_recursion_of_eigen' hL D I.P I.X I.agree I.typeNZ i
    (_root_.GlobalTheory.T.eigString_of_agree_aux41_adm7_tieLab hP.fin hL D I.P I.X I.agree Conclusion1.1 a.temp a.tieLab i)
    (_root_.GlobalTheory.T.eigGood_of_archimedean_signature_adm5 hL D I.P I.X Conclusion1.1 a.tieLab I.mtPar I.adm1 a.tie0 b.a4 a.a5 I.e0loc I.e0read i)
end GlobalTheory.RowsAll
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_conditions_of_inputs_of_jumpsCard : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.PointConditions' D := by
  first | exact @_root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
