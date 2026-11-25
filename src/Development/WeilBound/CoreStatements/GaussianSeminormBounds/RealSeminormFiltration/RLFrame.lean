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

theorem blocks_eq (r s : ℕ) :
    (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) = Matrix.diagonal (fun a => (sg r s a : ℂ)) := by
  ext (i | i) (j | j) <;> simp [sg, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem Jm_eq (r s : ℕ) : Jm r s = Matrix.diagonal (fun a => (sg r s a : ℂ)) := by
  rw [← blocks_eq]; rfl

theorem sg_sq (r s : ℕ) :
    Matrix.diagonal (fun a => (sg r s a : ℂ)) * Matrix.diagonal (fun a => (sg r s a : ℂ)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases a with a | a <;> simp [sg]

theorem card_pos (r s : ℕ) : Fintype.card {a // 0 < sg r s a} ≤ r := by
  have hs : Function.Surjective (fun a : Fin r => (⟨Sum.inl a, by simp [sg]⟩ : {a // 0 < sg r s a})) := by
    rintro ⟨a | a, ha⟩
    · exact ⟨a, rfl⟩
    · simp [sg] at ha; linarith
  simpa using Fintype.card_le_of_surjective _ hs

end PositivityTheory.RL.Frame

namespace PositivityTheory.RL

open _root_.PositivityTheory.RL.Frame

theorem frameEx : GlobalTheory.RealLift.FrameEx := by
  apply GlobalTheory.RealLift.frameEx_holds

end PositivityTheory.RL
