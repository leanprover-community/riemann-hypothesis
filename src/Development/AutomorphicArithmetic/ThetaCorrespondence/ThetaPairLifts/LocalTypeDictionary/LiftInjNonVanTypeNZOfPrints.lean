import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHoweLiftRows
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EulerFactorFromDoubling
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Rethread
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.ResCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHoweLiftRowsStatement

section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section
namespace GlobalTheory.Core.Rk.Exh.Top
theorem downNe_k_of_hypotheses' : ResidueKilled.DM → GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D :=
  fun hDM hSP => downNe_of_core hDM PositivityTheory.Rg.Rsw.resCore hSP
end GlobalTheory.Core.Rk.Exh.Top
end
end
end

section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downNe_of_eulerRight_doubling : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D := by
  atlas_forward_decl _root_.GlobalTheory.Core.Rk.Exh.Top.downNe_k_of_hypotheses'
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
namespace GlobalTheory.Core.Rk.LiftOnto
theorem liftInj_nonVan_typeNZ_of_hypotheses_alt : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    GlobalTheory.Published.UnramifiedDoublingGL →
    GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram →
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
      [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
      GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  intro hDec hDbl hGL hHecke hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull
  have hEul : GlobalTheory.Core.Rk.IP.EulerRight D := GlobalTheory.T.doublingEulerProductFarRight_of_rapidDecay_unramified hDec hGL D
  have hPole : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole := GlobalTheory.LiftPoleObj.simplePole_of_hecke hHecke
  have hNe : DownNe D := _root_.GlobalTheory.T.downNe_of_eulerRight_doubling hDbl hPole D hEul
  have hNV : ∀ i t, NonVan R i t := GlobalTheory.T.thetaLift_nonvanishing_onString_of_definiteDown D hNe G Pl0 T A Ks R F hG hFull
  have hEig : ∀ i t, DownEig R i t := GlobalTheory.T.downwardThetaLift_eigenform_is_eigenform hHowe D G Pl0 T A Ks R F hG hFull
  have hGF : ∀ i t, GenFin R i t := GlobalTheory.T.thetaLift_generation_finitePlaces hHowe D G Pl0 T A Ks R F hG hFull
  have hGI : ∀ i t, GenInf R i t := GlobalTheory.T.thetaLift_generation_at_realPlaces D G Pl0 T A Ks R F hG hFull
  have hGM : ∀ i t, GoodMem R i t := GlobalTheory.T.downwardThetaLift_preserves_good D G Pl0 T A Ks R F hG hFull
  have hNC : ∀ i t, GoodNoChi R i t := GlobalTheory.T.goodTypes_exclude_levelCharacter D G Pl0 T A Ks R F hG hFull
  have hPar : ∀ i t, ParamsEx R i t := GlobalTheory.DownLift.Params.paramsEx hDec D G Pl0 T A Ks R F hG hFull
  have hU : ∀ i t, UnrCorr R i t (fun _ => True) := GlobalTheory.T.unramifiedThetaCorrespondence_all_goodPrimes hDec hHowe D G Pl0 T A Ks R F hG hFull
  have hOk : ∀ i t (ok : Pl D.host.E → Prop), UnrCorr R i t ok := by
    intro i t ok h hh s c y hy h1 h2 B B' hB hB' w hw _
    exact hU i t h hh s c y hy h1 h2 B B' hB hB' w hw trivial
  have hTNZ : ∀ i t, TypeNZ R i t := fun i t =>
    GlobalTheory.DownLift.typeNZ_of_nonVan_gen D G Pl0 T A Ks R F hG hFull i t (hNV i t) (hGI i t) (hGF i t) (hNC i t) (hGM i t)
  exact ⟨GlobalTheory.LiftInjProof.liftInj_of_typeNZ D G Pl0 T A Ks R F hG hFull
      (fun i => ⟨hTNZ i A.μ0, hEig i A.μ0, hOk i A.μ0 _, hOk i A.μ0 _, hPar i A.μ0⟩),
    fun i t => ⟨hNV i t, hTNZ i t⟩⟩
end GlobalTheory.Core.Rk.LiftOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftInj_and_nonVan_typeNZ_of_given : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  first | exact @_root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | exact _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt <;> assumption)
end
end
