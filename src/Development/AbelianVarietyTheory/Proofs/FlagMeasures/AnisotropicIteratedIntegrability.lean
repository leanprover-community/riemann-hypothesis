module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.BesselDatum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct

namespace GlobalTheory.Per.FJConv

theorem iterated_integrableOn {G N : Type} [TopologicalSpace G] [FirstCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [TopologicalSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
    {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N} (hμ : μ 𝓕 ≠ ⊤) (hν : ν 𝓝 ≠ ⊤) {P : G → N → ℂ}
    (hP : Continuous fun q : G × N => P q.1 q.2) {M : ℝ} (hM : ∀ g n, ‖P g n‖ ≤ M) :
    (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ := by
  have h1 : ∀ g, Continuous (P g) := fun g => hP.comp (Continuous.prodMk_right g)
  have h2 : ∀ n, Continuous fun g => P g n := fun n => hP.comp (Continuous.prodMk_left n)
  have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hν
  refine ⟨fun g => Measure.integrableOn_of_bounded (M := M) hν (h1 g).measurable.aestronglyMeasurable
    (.of_forall (hM g)), ?_⟩
  have hc : Continuous fun g => ∫ n in 𝓝, P g n ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun g => (h1 g).measurable.aestronglyMeasurable)
      (fun g => .of_forall (hM g)) (integrable_const M) (.of_forall h2)
  exact Measure.integrableOn_of_bounded (M := M * ν.real 𝓝) hμ hc.measurable.aestronglyMeasurable
    (.of_forall fun g => norm_setIntegral_le_of_norm_le_const hν.lt_top fun n _ => hM g n)

end GlobalTheory.Per.FJConv
