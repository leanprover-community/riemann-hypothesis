module

public import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

def bwA_N {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => if τ = τv then atInf (embT D) (B'⁻¹ * B : GL (Fin n) D.host.E).1 τ else 1

theorem bwA_N_mul {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    (fun τ => bwA_N D τv B B' τ * atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ) =
      fun τ => if τ = τv then atInf (embT D) (B'⁻¹ : GL (Fin n) D.host.E).1 τ
        else atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ := by
  funext τ
  unfold bwA_N
  split_ifs with h
  · simp only [atInf]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  · rw [one_mul]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
