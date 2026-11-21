import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnrCrysAtRangePrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromTypeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltMore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficients
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CrysBridge

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiOne_of_not_mem_gset : GlobalTheory.Published.FontaineBcris → ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → GlobalTheory.PtCore.ChiOneE D i := by
  first | exact @_root_.GlobalTheory.ChiOneNoPt.main_alt_alt_alt | exact _root_.GlobalTheory.ChiOneNoPt.main_alt_alt_alt | (intros; apply _root_.GlobalTheory.ChiOneNoPt.main_alt_alt_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → GlobalTheory.PtCore.ChiOneE D i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) :=
  fun _ D i r hR hCr h0 h1 hChi w hw C x =>
    dual_crys D i r w hw C x (tw_crys D i r w hw C x (crys_chi D i hChi w hw C)
      (crys_coef D i r w hw C x (_root_.GlobalTheory.DualTwistCrys.crys_bridge_alt_alt D i r hR hCr h0 h1 w hw x)))
end GlobalTheory.DualTwistCrys
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_locC_of_chiOneE : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → GlobalTheory.PtCore.ChiOneE D i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) := by
  atlas_forward_decl _root_.GlobalTheory.DualTwistCrys.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem unrCrysAtRangePrime_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (X : KillingConditions.HubData D), (∀ i, GoodR D.nd i (X.r i)) → SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i)) ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), C.IsGood → ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) := by
  intro hF D L X hgood ht0 ha2 ha5 hG2 hpar hmu i _ hg hR _
  obtain ⟨h23, hqd, -⟩ := hR
  have hchi := _root_.GlobalTheory.T.chiOne_of_not_mem_gset hF D ht0 ha2 ha5 hpar hmu i hg
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  refine ⟨GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i (fun h => h23 (Or.inl h)) (fun h => hqd (Or.inl h)) (fun h => hqd (Or.inr h)), ?_⟩
  intro w hw C _ x
  exact _root_.GlobalTheory.T.isCrys_locC_of_chiOneE hF D i (X.r i) (hgood i) (hG2 i (X.r i) (hgood i)) hg0 hg1 hchi w hw C x
end GlobalTheory.HubX
end
end
