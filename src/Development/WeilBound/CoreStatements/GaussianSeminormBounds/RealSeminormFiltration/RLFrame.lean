module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Mathlib.Analysis.Matrix.Order
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder
open Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.RL.Frame

def sg (r s : ℕ) : Fin r ⊕ Fin s → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

end PositivityTheory.RL.Frame

namespace PositivityTheory.RL

open _root_.PositivityTheory.RL.Frame

theorem frameEx : GlobalTheory.RealLift.FrameEx := by
  apply GlobalTheory.RealLift.frameEx_holds

end PositivityTheory.RL
