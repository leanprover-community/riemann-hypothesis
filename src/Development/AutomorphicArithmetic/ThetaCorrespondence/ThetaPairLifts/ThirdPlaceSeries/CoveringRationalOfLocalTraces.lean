import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringRationalOfLocalTraces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCoverBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitaryStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCore

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m), p.PointConditions' → GlobalTheory.CovTop.RecTied D L → ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈ Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  first | exact @_root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | exact _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | (intros; apply _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField
namespace GlobalTheory.CovTop
open GlobalTheory.BigTop Formalism.IndefR.FWT
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem ratAt_of_rows_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (ht : RecTied D L) : RatAt p i :=
  GlobalTheory.T.integralForms_eq_span_integralRationalForms _ _ _ _ _ _ _ _ (p.fw.ks i) (fun u f hf => rho_mem_WK p i u f hf) (_root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap p i hp ht)
end GlobalTheory.CovTop
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField
namespace GlobalTheory.CovTop
open GlobalTheory.BigTop Formalism.IndefR.FWT
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem covering_rational_of_local_traces_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftRational := by
  intro _
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, le_rfl, ⟨0, fun x hx _ ι p hp i => _root_.GlobalTheory.CovTop.ratAt_of_rows_alt p i hp.1 hp.2⟩⟩⟩⟩
end GlobalTheory.CovTop
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftRational_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftRational := by
  first | exact @_root_.GlobalTheory.CovTop.covering_rational_of_local_traces_alt | exact _root_.GlobalTheory.CovTop.covering_rational_of_local_traces_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_rational_of_local_traces_alt <;> assumption)
end
end
end
