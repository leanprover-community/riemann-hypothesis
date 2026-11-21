import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerClassesOfPartsC

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem sfinite_of_isHaarOn {k r : ℕ} (U : Set (B.Mat k r)) (μ : Measure (Mt k r)) (h : B.IsHaarOn U μ) :
    SFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance





end Formalism.FourierDecayAlt.P5
