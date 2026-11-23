module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScCApplyInlInl
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA2

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def toOm {ι : Type} (X : Matrix ι ι E) (h : ∀ i j, X i j ∈ O) : Matrix ι ι O := Matrix.of fun i j => ⟨X i j, h i j⟩

theorem scC_mem (α β : E) (hα : α ∈ O) (hβ : β ∈ O) (i j : Ix r) : scC r α β i j ∈ O := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scC, liftE, dlast, Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply] <;>
    split_ifs <;> simp_all [O.one_mem, O.zero_mem]

theorem scC_mul_inv (α β α' β' : E) (h1 : α * α' = 1) (h2 : β' = -(β * α')) :
    scC r α β * scC r α' β' = 1 := by
  unfold scC
  rw [Matrix.fromBlocks_multiply]
  have hL : liftE (R := E) r * dlast r α' = α' • liftE r := by
    ext a b
    simp only [liftE, dlast, Matrix.mul_diagonal, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs with h1 h2 <;> simp_all
  have hD : dlast r α * dlast r α' = 1 := by
    rw [dlast, dlast, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [h1]
  simp only [Matrix.smul_mul, hL, hD, h2, smul_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add, smul_zero]
  rw [← Matrix.fromBlocks_one, ← add_smul]
  congr 1
  simp [mul_comm]

theorem scC_det (α β : E) : (scC r α β).det = α := by
  rw [scC, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, dlast, Matrix.det_diagonal]
  rw [Finset.prod_eq_single (Fin.last r)]
  · simp
  · intro b _ hb; simp [hb]
  · simp

end ScaleA2

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
