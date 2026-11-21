import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.JointConditionOfConstituentConditionSplit

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
theorem crys_loc_alt_alt (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (hG : _root_.UpperTheory.GalS.G2a D.nd D.naut i r) (h0 : D.nd.l i ≠ D.host.g 0)
    (h1 : D.nd.l i ≠ D.host.g 1) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) := by
  have hc := (_root_.UpperTheory.GalS.g2a' hG w hw h0 h1 x).1
  exact ((D.loc_tie i w hw).2.1 D.R.nV (r x) (hr x).1).1.mp hc
end GlobalTheory.CrysFromGTwo
end
section
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
namespace GlobalTheory.CrysChiOne
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  intro hF D i r ρ π hr hG h0 h1 hD w hw C
  have hχ := crys_chi hF D i r ρ π hD (fun w' hw' => _root_.GlobalTheory.CrysFromGTwo.crys_loc_alt_alt D i r hr hG h0 h1 w' hw' π) w hw C
  have hx : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := fun x =>
    crys_coef D i r w hw C x (_root_.GlobalTheory.CrysFromGTwo.crys_loc_alt_alt D i r hr hG h0 h1 w hw x)
  exact ⟨hχ, fun x => ⟨hx x, crys_tw D i r w hw C x hχ (hx x)⟩⟩
end GlobalTheory.CrysFromGTwo
end
end
end
