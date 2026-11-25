module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
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
