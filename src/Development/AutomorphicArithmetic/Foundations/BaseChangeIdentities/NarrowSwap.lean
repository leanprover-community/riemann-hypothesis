import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowCondition
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.UsedAsc
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfPublishedStatement

section
open PositivityTheory.Rg.Rs in
theorem UpperTheory.BaseChangeIdentities.ascComp : UpperTheory.BaseChangeIdentities.AscComp := by
  intro E _ _ _ N hN
  refine ⟨fun a π ha hn => ?_, fun V hV a d π hn e =>
    Re.Asc.hasSpehComp ascSeed_holds2.2 PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL hN hV hn e⟩
  subst ha
  exact ⟨π.V, PositivityTheory.RSHS.L1.cuspDiscrete E _ hN π (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn) hn,
    PDich.ascEmb_one (Setoid.refl π)⟩
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities

theorem speh (h : PositivityTheory.Rg.BcN.BaseChangeIsobaricN) : GlobalTheory.BcSpeh.BcSpeh := bcSpeh_of ascComp (definiteN_of h)

theorem Conclusion1 : DefiniteN → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D),
      CGTrue hL D T → AUTrue hL D T A → SphericalInertData.Conclusion1 D :=
  fun h _ _ => baseChange_preserves_unitary_of ascComp h

end UpperTheory.BaseChangeIdentities

end
end
