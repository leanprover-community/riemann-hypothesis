module

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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix
open Matrix

noncomputable section

namespace PositivityTheory.Rg.Sw.KAKB

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def S0 (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

def C0 (n : ℕ) : M2 n := fromBlocks 1 1 (Complex.I • 1) (-(Complex.I • 1))

def C1 (n : ℕ) : M2 n := (1 / 2 : ℂ) • (C0 n)ᴴ

theorem cayley_conjTranspose_eq : (C0 n)ᴴ = fromBlocks 1 (-(Complex.I • 1)) 1 (Complex.I • 1) := by
  simp [C0, fromBlocks_conjTranspose, conjTranspose_smul]

theorem cayley_conjTranspose_mul : (C0 n)ᴴ * C0 n = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module

theorem cayley_mul_conjTranspose : C0 n * (C0 n)ᴴ = (2 : ℂ) • 1 := by
  rw [cayley_conjTranspose_eq, C0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, two_smul] <;> module

theorem cayley_inverse_mul : C1 n * C0 n = 1 := by
  rw [C1, Matrix.smul_mul, cayley_conjTranspose_mul, smul_smul]; norm_num

theorem cayley_mul_inverse : C0 n * C1 n = 1 := by
  rw [C1, Matrix.mul_smul, cayley_mul_conjTranspose, smul_smul]; norm_num

theorem complex_structure_cayley : JJ n * C0 n = C0 n * (Complex.I • S0 n) := by
  simp only [JJ, C0, S0, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul] <;> module

end PositivityTheory.Rg.Sw.KAKB

end
