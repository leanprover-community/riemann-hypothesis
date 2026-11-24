module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.ElementaryGeneratorAdjoint
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolS
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem exp_mulVec_of_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (h : A *ᵥ v = 0) :
    NormedSpace.exp A *ᵥ v = v := by
  apply PI.QnHermHaar.HermitianAdjointLemmas.exp_mulVec_fix <;> assumption

theorem adjH_def {k r : ℕ} (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.BridgeCSB.adjH X = Hpk k r * Xᴴ * Hpk k r := rfl

theorem exp_mem_UH {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Hpk k r * Xᴴ * Hpk k r + X = 0) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  rw [Formalism.MainNotions.BridgeCSB.mem_UH_iff, Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul]
  have ha : Formalism.MainNotions.BridgeCSB.adjH X = -X := eq_neg_of_add_eq_zero_left hX
  rw [ha, Complex.star_def, Complex.conj_ofReal, smul_neg, ← Matrix.exp_add_of_commute]
  · rw [neg_add_cancel, NormedSpace.exp_zero]
  · exact (Commute.refl _).neg_left

theorem adj_of_lie {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r)) : Hpk k r * Xᴴ * Hpk k r + X = 0 := by
  have hadj : Formalism.MainNotions.BridgeCSB.adjH X = -X := by
    apply Formalism.MainNotions.BridgeCSB.exp_smul_inj
    intro t
    have hU := hX t
    have h1 : Formalism.MainNotions.BridgeCSB.adjH (NormedSpace.exp ((t : ℂ) • X)) = (NormedSpace.exp ((t : ℂ) • X))⁻¹ :=
      (Matrix.inv_eq_left_inv ((Formalism.MainNotions.BridgeCSB.mem_UH_iff _).1 hU)).symm
    rw [Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul, Complex.star_def, Complex.conj_ofReal,
      ← Matrix.exp_neg] at h1
    rw [h1, smul_neg]
  rw [← adjH_def, hadj, neg_add_cancel]

theorem lieG : LieG := by
  intro k r
  ext X
  constructor
  · intro hX
    exact adj_of_lie hX
  · intro hX t
    exact exp_mem_UH hX t

theorem col_zero {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (j : Fin d)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) : X *ᵥ bvec j = 0 := by
  funext i
  have hij : X i j = 0 := by
    refine Formalism.MainNotions.BridgeCSB.entry_zero_of_const' X i j (bvec j i) fun t => ?_
    have := congrFun (h t) i
    rw [← this, Matrix.mulVec, dotProduct]
    simp [bvec, Pi.single_apply]
  rw [Matrix.mulVec, dotProduct]
  simp [bvec, Pi.single_apply, hij]

theorem lieWb : LieWb := by
  intro k r
  ext X
  constructor
  · intro hX
    refine ⟨adj_of_lie fun t => (hX t).1, fun a => ⟨?_, ?_⟩⟩
    · exact col_zero _ fun t => ((hX t).2 a).1
    · exact col_zero _ fun t => ((hX t).2 a).2
  · rintro ⟨hX, hk⟩ t
    refine ⟨exp_mem_UH hX t, fun a => ⟨?_, ?_⟩⟩
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).1, smul_zero])
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).2, smul_zero])

end Formalism.L2.SG.Pf.BH
