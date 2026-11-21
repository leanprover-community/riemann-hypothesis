import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLiftOfPairLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitBCOfGalIso
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweThetaLiftComponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySphericalComponentOfReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm4OfRowsA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoinStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalRepOfReadingLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthogonalityOfFormStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem split_theta_correspondence_of_local_pairings : ∀ D : D7, (∀ i, PairLift D.nd D.naut i) → Formalism.MainNotions.SumRepresentations.adm3 D := by
  intro D h i σ P hθ w hw
  exact GlobalTheory.RowTie.splitLift_of_pairLift _ _ _ D.nd D.naut i (h i) σ P hθ w hw

end GlobalTheory.RowTie
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowSizeClosing

theorem rowSize_of_unitarySphericalComponent :
    ∀ (D : D7), GlobalTheory.RowSatakeBound.UnitarySphericalComponent D.nd D.naut → GlobalTheory.RowCopy.RowSize D :=
  fun D h => GlobalTheory.RowSatakeBound.rowSize_of_component D.nd D.naut h

end GlobalTheory.RowSizeClosing
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem howeUp_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i →
    GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  intro R H what₂ N A i hL hB hS hR σ P P' hP hP'
  refine GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places R H what₂ N A i hB hS hR P P' (Filter.Eventually.of_forall fun w hw => ?_)
  rw [hL σ P hP w hw, hL σ P' hP' w hw]

end GlobalTheory.RowTie
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  atlas_forward_decl GlobalTheory.RowTie.howeUp_of_pairLift
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Proof.ThetaOneGenusOne

theorem thetaOne_of_ties : ∀ (D : D7), (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) → GlobalTheory.RowCopy.ThetaOne D := by
  intro D hpos hpair horth hbc hsplit hrep
  exact GlobalTheory.Proof.HoweThetaLiftComponents.eachRowHasThetaLift_of_howe _ _ _ D.nd D.naut hpos
    (fun i => GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces _ _ _ D.nd D.naut i (hpair i) (hbc i) (hsplit i) (hrep i)) horth

end GlobalTheory.Proof.ThetaOneGenusOne
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsBClosing

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P →
    GlobalTheory.NRows.RowsA D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) →
    GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  intro hPr hL D P J hA h1 hpos
  have hRM : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) := fun i => ⟨J.rowM i⟩
  obtain ⟨S, hT, hLaws, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hPr.fin hL D P hRM
  have hU : RowUnit S := GlobalTheory.RowUnitProof.rowUnit_of_isTrue hL D P hRM S hT
  have hPR : PairRead S := GlobalTheory.T.pair_reading_of_join hPr.bz hL D P J S hT hU
  have hpair : ∀ i, PairLift D.nd D.naut i :=
    GlobalTheory.SplitPairLift.main hPr.bz hPr.bern hPr.howe _ _ _ D.nd D.naut P.T S hLaws hU hPR
  have hIf := GlobalTheory.AdmIface.main D
  have hcheb : ChebSplit D.nd := (hIf.2.1 hA.a5).1
  have hsplit : ∀ i, SplitBC D.nd D.naut i := fun i =>
    GlobalTheory.RowTie.splitBC_of_galIso _ _ _ D.nd D.naut i (GlobalTheory.BCGal.main D hA.tie0 hA.a2 hA.temp i) hcheb hA.an2
  have hrep : ∀ i, RepOfLoc D.nd D.naut i := GlobalTheory.T.local_rep_of_reading_laws hL D P S hT hLaws
  have hbc : ∀ i, BCEx D.nd D.naut i := hIf.1 h1
  have horth : ∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := fun i => GlobalTheory.T.type_orthogonality_of_form hL D P i (J.form i)
  refine ⟨⟨?_, GlobalTheory.RowTie.split_theta_correspondence_of_local_pairings D hpair, GlobalTheory.T.adm4_of_rows_a hPr hL D P hRM hA,
    GlobalTheory.Proof.ThetaOneGenusOne.thetaOne_of_ties D hpos hpair horth hbc hsplit hrep⟩, fun i => ⟨hpair i, hsplit i, hrep i⟩⟩
  exact GlobalTheory.RowSizeClosing.rowSize_of_unitarySphericalComponent D
    (GlobalTheory.SplitRead.unitarySphericalComponent_of_reading hPr.bz _ _ _ D.nd D.naut P.T S hLaws hU)

end GlobalTheory.RowsBClosing
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_b_and_local_lifts : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P → GlobalTheory.NRows.RowsA D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  atlas_forward_decl GlobalTheory.RowsBClosing.main
end
