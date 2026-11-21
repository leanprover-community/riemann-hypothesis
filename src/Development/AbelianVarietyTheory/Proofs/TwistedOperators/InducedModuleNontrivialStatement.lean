import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedModuleNontrivial
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_module_nontrivial : ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), Nontrivial I.H := by
  atlas_forward_decl GlobalTheory.IndNonzero.indModule_nontrivial
