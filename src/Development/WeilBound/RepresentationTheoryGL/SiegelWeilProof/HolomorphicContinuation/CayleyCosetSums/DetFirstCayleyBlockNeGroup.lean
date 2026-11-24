module

import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def nbar (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

theorem inG_nbar (t : ℝ) : InG (nbar (n := n) t) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem nbar_block (y : M2 n) (t : ℝ) : (y * nbar t).toBlocks₂₁ = y.toBlocks₂₁ + (t : ℂ) • y.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [nbar, Matrix.fromBlocks_multiply]

private theorem JJ_mul_JJ_eq_neg_one : JJ n * JJ n = -1 := by
  rw [JJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem det_ne_of_inG (x : M2 n) (hx : InG x) : x.det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hx', JJ_mul_JJ_eq_neg_one, neg_neg]
  exact (Matrix.isUnit_det_of_left_inverse h).ne_zero

theorem det_first_cayley_block_ne_group (x : M2 n) (hx : InG x) : (u1 x).det ≠ 0 := by
  apply PositivityTheory.Rg.Sw.HSt.LoweringDerivative.det_first_block_ne_zero_group <;> assumption

end PositivityTheory.Rg.Sw.HSt.L3
