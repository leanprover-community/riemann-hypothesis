module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PSymplReduceStep

theorem symplExt_map {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
    (symplExt (1 : ℤ) 0 0 1 Q).map (Int.cast : ℤ → ℝ) =
      symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [symplExt, symplCons]

theorem schur_toBlocks {n : ℕ} (K : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    (Matrix.of fun i j : Fin n => K.toBlocks₁₁ i.succ j.succ -
        K.toBlocks₁₁ i.succ 0 * K.toBlocks₁₁ 0 j.succ / K.toBlocks₁₁ 0 0) =
      (symplReduce K).toBlocks₁₁ := by
  ext i j
  simp [symplReduce, Matrix.toBlocks₁₁]

end PSymplReduceStep

theorem SymplReduceStep.proof (h1 : SymplExtMem.Statement) (h2 : SymplReduceConj.Statement)
    (h3 : SymplDetSchur.Statement) : SymplReduceStep.Statement := by
  intro n H Q hH hQ
  refine ⟨symplExt 1 0 0 1 Q, h1 ℤ n 1 0 0 1 Q (by norm_num) hQ, ?_⟩
  obtain ⟨he, hred⟩ := h2 n H (Q.map (Int.cast : ℤ → ℝ))
  rw [symplGram, PSymplReduceStep.symplExt_map]
  generalize symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) * H *
    (symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)))ᵀ = K at he hred ⊢
  refine ⟨he, ?_⟩
  have hk0 : K.toBlocks₁₁ 0 0 = H (Sum.inl 0) (Sum.inl 0) := he
  rw [h3 n K.toBlocks₁₁ (hk0 ▸ hH), PSymplReduceStep.schur_toBlocks, hred, hk0]
  rfl

end

end GroundTheory.Heights₂.Heights
