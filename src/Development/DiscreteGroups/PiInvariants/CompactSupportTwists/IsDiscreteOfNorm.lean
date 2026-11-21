import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescentOfLocalGlobalInputs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace DiscreteGroups.T1.G

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in

theorem phiU_ad : PhiU n (Ad E) = ratGL E n (PhiU n E) :=
  (GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU (algebraMap E (Ad E)) n).symm




theorem isDiscrete_of_norm {π : CuspSub E n} (hu : π.IsUnitary)
    (hN : ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) : IsDiscrete π.V :=
  isDiscrete_of_cuspSub π fun φ hφ => by
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_isUnitary hu hφ
    exact GlobalTheory.DiscChar.isSqInt_of_bounded (hN φ hφ) (C := C) fun g => by simpa using hC g

theorem reg_of {π : CuspSub E n} (hreg : (CG.mk π).IsRegAlg) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : HasInfCharGL π.V τ m) : ∃ lam : DomWeight n, m = infOfWeight lam := by
  have h1 : (CG.mk π).HasInfChar τ m := hm
  obtain ⟨hnd, hz⟩ := hreg τ
  rw [h1.infChar_eq] at hnd hz
  obtain ⟨lam, hl⟩ := GlobalTheory.WtComb.exists_domWeight_infOf n m hm.1 hnd hz
  exact ⟨lam, hl.symm.trans (GlobalTheory.UnitaryReadTrue.infOf_eq_infOfWeight lam)⟩


end DiscreteGroups.T1.G

end
