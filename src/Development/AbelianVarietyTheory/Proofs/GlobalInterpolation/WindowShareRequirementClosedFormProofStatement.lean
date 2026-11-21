import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProof
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import BuildAid.ForwardExisting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.windowShareRequirementClosedForm_proof : DC.WClosed := by
  atlas_forward_decl GlobalTheory.EX.G4.wClosed
