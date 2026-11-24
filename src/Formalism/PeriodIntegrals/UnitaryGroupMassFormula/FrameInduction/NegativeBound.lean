module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap", "h": "module\n\npublic import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.BitVec\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

noncomputable section
namespace PI.FrameInd.NegB

lemma herm_Pk (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x x = ∑ i, star ((Pk k r *ᵥ x) i) * (dK k r i * (Pk k r *ᵥ x) i) := by
  unfold herm
  rw [← PJP k r, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
  simp only [dotProduct, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dK, Pi.star_apply]

lemma re_herm (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) :
    (herm (Hpk k r) x x).re =
      ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) := by
  rw [herm_Pk, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i.val < r + k <;>
    simp [h, dK, epsK, Complex.mul_re, Complex.normSq_apply]

lemma Pk_inj (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (h : Pk k r *ᵥ x = 0) : x = 0 := by
  have hA : (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) * Pk k r = 1 := by
    rw [Matrix.mul_assoc, PJP, Hpk_sq]
  calc x = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) *ᵥ x := (Matrix.one_mulVec x).symm
    _ = (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) *ᵥ (Pk k r *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hA]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

def negMap (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (fun a : Fin (r + 1) => (⟨r + k + a.val, by omega⟩ : Fin (2 * r + k + 1)))).comp
    (Matrix.mulVecLin (Pk k r))

lemma eq_zero_of_negMap (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (hx : negMap k r x = 0)
    (hre : (herm (Hpk k r) x x).re ≤ 0) : x = 0 := by
  apply Pk_inj k r x
  have hneg : ∀ i : Fin (2 * r + k + 1), ¬ i.val < r + k → (Pk k r *ᵥ x) i = 0 := by
    intro i hi
    have h1 := congrFun hx ⟨i.val - (r + k), by omega⟩
    simp only [negMap, LinearMap.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
      Pi.zero_apply] at h1
    have h2 : (⟨r + k + (i.val - (r + k)), by omega⟩ : Fin (2 * r + k + 1)) = i := by
      ext
      simp only
      omega
    rw [h2] at h1
    exact h1
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ (if i.val < r + k then (1 : ℝ) else -1) *
      Complex.normSq ((Pk k r *ᵥ x) i) := by
    intro i _
    by_cases h : i.val < r + k
    · rw [if_pos h, one_mul]
      exact Complex.normSq_nonneg _
    · rw [if_neg h, hneg i h, map_zero, mul_zero]
  have hsum := re_herm k r x
  have hzero : ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) = 0 :=
    le_antisymm (hsum ▸ hre) (Finset.sum_nonneg hterm)
  ext i
  by_cases h : i.val < r + k
  · have h1 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)
    rw [if_pos h, one_mul] at h1
    simpa using Complex.normSq_eq_zero.mp h1
  · simpa using hneg i h

theorem negBound (k r : ℕ) (W : Submodule ℂ (Fin (2 * r + k + 1) → ℂ))
    (hW : ∀ x ∈ W, (herm (Hpk k r) x x).re ≤ 0) : Module.finrank ℂ W ≤ r + 1 := by
  have hinj : Function.Injective ((negMap k r).comp W.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : (a : Fin (2 * r + k + 1) → ℂ) = 0 :=
      eq_zero_of_negMap k r a ha (hW a a.2)
    exact Subtype.ext h1
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun] at h
  exact h

end PI.FrameInd.NegB
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Formalism.QuantumDeterminants

noncomputable section
namespace PI.FrameInd

theorem negative_bound : NegBound := fun k r S hS => NegB.negBound k r S hS

end PI.FrameInd
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound =====
