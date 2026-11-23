module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLowG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_inG : InG (JJ n) := by
  have hc : (JJ n)ᴴ = -JJ n := by
    unfold JJ
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  show (JJ n)ᴴ * JJ n * JJ n = JJ n
  rw [hc, Matrix.mul_assoc, JJ_mul_JJ]
  simp

def JG : GR n :=
  ⟨⟨JJ n, -JJ n, by simp [JJ_mul_JJ], by simp [JJ_mul_JJ]⟩, JJ_inG⟩

theorem lower_mul_JG (y : GR n) :
    (mR (y * JG)).toBlocks₂₁ = -(mR y).toBlocks₂₂ := by
  have h : mR (y * JG) = mR y * JJ n := rfl
  rw [h, ← Matrix.fromBlocks_toBlocks (mR y)]
  unfold JJ
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

theorem dense_bigCell₂₂ : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} := by
  intro n
  have hset : {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} =
      (fun y => y * (JG (n := n))) ⁻¹' {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, lower_mul_JG, Matrix.det_neg]
    constructor
    · intro h
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
    · intro h h0
      exact h (by rw [h0, mul_zero])
  rw [hset]
  exact (dense_bigCell n).preimage (isOpenMap_mul_right _)

end GlobalTheory.CompanionTheory.BigCell
