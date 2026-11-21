import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTopOfCore
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullDataExtension

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_threshold_run_holds : ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → RunHolds x₀ h hinj EX p := by
  first | exact @GlobalTheory.FinalJoin.runHolds_of_parOK | exact GlobalTheory.FinalJoin.runHolds_of_parOK | (intros; apply GlobalTheory.FinalJoin.runHolds_of_parOK <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameters_ok_of_laws : ∀ (D : D7) (J : CoreJ D) (T : Top D) (EX : ErrX D) (p : ℕ), LawsJ J → LawsP T → LawsSh T → T.toCore = J.toCore → T.Q.Canon → FieldOK0 D p → HalfEX T.toCore EX → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1 ∧ (T.dδ j n).pd = p) → ∀ j, InR D j → ParOK T EX p j := by
  first | exact @GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws | exact GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws | (intros; apply GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_full_data_extension : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ xi, XiOK D p xi → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ TF.xi = xi ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  first | exact @GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiOK_noVol | exact GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiOK_noVol | (intros; apply GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiOK_noVol <;> assumption)
end

section
set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_full_runHolds_of_core : ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (J : CoreJ D) (EX : ErrX D), LawsJ J → LawsCore J.toCore → J.Q.Canon → (∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) → HalfEX J.toCore EX → OKPsi D → ∃ T : Top D, LawsP T ∧ T.toCore = J.toCore ∧ ∀ (p : ℕ) (hK : FieldOK0 D p) (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ xi, XiOK D p xi → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D) (hF : LawsFull TF), TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ TF.xi = xi ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ (∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p) ∧ (∀ j, InR D j → ParOK TF.toTop EX p j) ∧ RunHolds x₀ hF.p hK.full.1 EX p := by
  obtain ⟨x₀, hrun⟩ := GlobalTheory.T.exists_threshold_run_holds
  refine ⟨x₀, fun D J EX hJ hJc hcan hpos hH hk => ?_⟩
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.FinalJoin.exists_top_of_core D J.toCore hJc hpos hk
  have hTH : HalfEX T.toCore EX := by rw [hTc]; exact hH
  have hTcan : T.toCore.Q.Canon := by rw [hTc]; exact hcan
  refine ⟨T, hT, hTc, fun p hK P hP xi hxi => ?_⟩
  obtain ⟨dd, TF, hF, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_full_data_extension D J T hJ hT hTc hTcan p hK P hP xi hxi
  have hH' : HalfEX TF.toTop.toCore EX := by rw [h1]; exact hTH
  have hpar : ∀ j, InR D j → ParOK TF.toTop EX p j :=
    GlobalTheory.T.parameters_ok_of_laws D TF.J TF.toTop EX p hF.j hF.p hF.sh rfl hF.canon hK hH'
      (fun j hj n => ⟨hF.lvA j hj n, (h5 j hj).2 n⟩)
  exact ⟨dd, TF, hF, h1, h2, h3, h4, h5, hpar, hrun D TF.toTop hF.p hK.full.1 EX p hpar⟩

end GlobalTheory.FinalJoin2
end
