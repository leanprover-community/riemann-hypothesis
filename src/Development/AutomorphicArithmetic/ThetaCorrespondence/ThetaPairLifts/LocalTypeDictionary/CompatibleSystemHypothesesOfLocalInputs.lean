import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanInputsImply
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanInputsImplyStatement

section
section
noncomputable section
open Matrix Topology Filter
open scoped ContDiff
namespace GlobalTheory.BesselMapOne
section Smooth
open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end
end Smooth
section Frame
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k r : ℕ}
variable {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
end Frame
section Dual
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
end Dual
section Main
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel PI.BesselMapUniq GlobalTheory.SmVec
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
end Main
end GlobalTheory.BesselMapOne
end
end
end

section
section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory
theorem compatibleSystem_hypotheses_of_localInputs : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Mem.Top.Bl.HypAAlt :=
fun ar cm we hm cd cw hf cl ce fd sw =>
  have c := GlobalTheory.DiscreteSeriesConsequences.of_classification cl
  have u : GlobalTheory.Published.DiscreteSeriesUpqUnique := GlobalTheory.Published.discreteSeriesUpqUnique_of_classification cl
  have d := GlobalTheory.discreteSeries_three_of_hypotheses ce c.2.2.2.2 u
  ⟨ar.rayClassFieldSt, ar.principalIdealSt, cm, hm, cd, cw, GlobalTheory.weilRepresentationUnitaryPair, c.2.2.1, hf, c.2.1, u,
    GlobalTheory.rowsFinDim_link, sw, c.2.2.2.2, fd, GlobalTheory.Mass.massRatio_all_unramified_cmFields,
    d.1, d.2.1, d.2.2, ar, we⟩
end GlobalTheory
end

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_member_hypotheses : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Mem.Top.Bl.HypAAlt := by
  first | exact @_root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs | exact _root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs | (intros; apply _root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs <;> assumption)
end
end
