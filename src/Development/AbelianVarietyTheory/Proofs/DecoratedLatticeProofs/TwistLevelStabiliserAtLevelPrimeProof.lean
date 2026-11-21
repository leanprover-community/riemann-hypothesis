import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairStabiliserMemChartLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelComponentFixesStandardPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOffStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.twLev_prime : GlobalTheory.AdForm.TwLev' := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ hJall j hj b
  refine ⟨fun i g hg => ⟨GlobalTheory.T.standardPair_stabiliser_mem_chartLevel I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg,
    GlobalTheory.T.chartCharacter_trivial_on_standardPairStabilizer I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg _⟩, fun κ hκ => ?_⟩
  obtain ⟨g, hg1, κ', hκ', heq⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_prod_splitComponents_mul_off (I.rec7 l Z) ((I.rec7 l Z).sp.X j) k ι p _ (β j)
    (GlobalTheory.T.splitPoints_lie_over_distinct_places I hOk hPins l Z u p β Q L hS) J hJ hJall κ
  exact ⟨g, fun i => GlobalTheory.T.chartLevel_component_fixes_standardPair I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b κ hκ i (g i) (hg1 i), κ', hκ', heq⟩
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof : GlobalTheory.AdForm.TwLev' := by
  atlas_forward_decl GlobalTheory.AdForm.twLev_prime
