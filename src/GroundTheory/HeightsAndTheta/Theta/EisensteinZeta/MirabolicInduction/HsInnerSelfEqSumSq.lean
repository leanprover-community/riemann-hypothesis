module

public import GroundTheory.AutomorphicForms.RealGroupsLie
public import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements, GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq

-- ===== clump member: GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements", "h": "module\n\npublic import GroundTheory.AutomorphicForms.RealGroupsLie\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace SecondKind

abbrev MatProd {f : ℕ} (p q : Fin f → ℕ) : Type :=
  (τ : Fin f) → Matrix (Fin (p τ) ⊕ Fin (q τ)) (Fin (p τ) ⊕ Fin (q τ)) ℂ

def lieProd {f : ℕ} (p q : Fin f → ℕ) : Submodule ℝ (MatProd p q) :=
  Submodule.pi Set.univ fun τ => indefiniteUnitaryLieAlgebra (p τ) (q τ)

def hsInner {f : ℕ} {p q : Fin f → ℕ} (X X' : MatProd p q) : ℝ :=
  ∑ τ, (trace (X τ * (X' τ)ᴴ)).re

structure OrthoFrame where

  f : ℕ

  r : ℕ
  f_pos : 1 ≤ f
  r_pos : 1 ≤ r

  p : Fin f → ℕ

  q : Fin f → ℕ
  sig : ∀ τ, p τ + q τ = r

  place : Fin (f * r ^ 2) → Fin f

  E : Fin (f * r ^ 2) → MatProd p q
  span : Submodule.span ℝ (Set.range E) = lieProd p q
  orthonormal : ∀ k l, hsInner (E k) (E l) = if k = l then 1 else 0
  supp : ∀ l τ, τ ≠ place l → E l τ = 0

namespace OrthoFrame

variable (F : OrthoFrame)

end OrthoFrame

end SecondKind

end

end GroundTheory.Heights₂.Theta
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Matrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport GroundTheory.AutomorphicForms.RealGroupsLie\npublic import GroundTheory.HeightsAndTheta.Theta.LieCoordinates.SecondKindStatements\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option linter.unusedSectionVars false

namespace SecondKind

namespace UnitaryRecombination

section HS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hsVec (X : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 (fun ij => X ij.1 ij.2)

def hs (X : Matrix ι ι ℂ) : ℝ := ‖hsVec X‖

theorem hs_nonneg (X : Matrix ι ι ℂ) : 0 ≤ hs X := norm_nonneg _

theorem hs_sq (X : Matrix ι ι ℂ) : hs X ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [hs, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]; rfl

def tInner (X Y : Matrix ι ι ℂ) : ℝ := (trace (X * Yᴴ)).re

theorem tInner_self (X : Matrix ι ι ℂ) : tInner X X = hs X ^ 2 := by
  rw [hs_sq, tInner, trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem hs_conjTranspose (X : Matrix ι ι ℂ) : hs Xᴴ = hs X := by
  have h : hs Xᴴ ^ 2 = hs X ^ 2 := by
    rw [hs_sq, hs_sq, Finset.sum_comm]
    simp [conjTranspose_apply]
  exact (sq_eq_sq₀ (hs_nonneg _) (hs_nonneg _)).1 h

theorem opNorm_le_hs (X : Matrix ι ι ℂ) : ‖X‖ ≤ hs X := by
  rw [← l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (hs_nonneg _) fun v => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by have := hs_nonneg X; positivity)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, hs_sq, EuclideanSpace.norm_sq_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ofLp_toEuclideanCLM, mulVec, dotProduct]
  calc ‖∑ j, X i j * (WithLp.ofLp v) j‖ ^ 2 ≤ (∑ j, ‖X i j‖ * ‖(WithLp.ofLp v) j‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ (∑ j, ‖X i j‖ ^ 2) * ∑ j, ‖(WithLp.ofLp v) j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem hs_mul_left_le (A X : Matrix ι ι ℂ) : hs (A * X) ≤ ‖A‖ * hs X := by
  refine (sq_le_sq₀ (hs_nonneg _) (by have := hs_nonneg X; positivity)).1 ?_
  rw [hs_sq, mul_pow, hs_sq, Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have key := (toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 fun i => X i j)
  rw [l2_opNorm_toEuclideanCLM] at key
  have key2 := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at key2
  convert key2 using 2
  rw [ofLp_toEuclideanCLM]
  simp [mulVec, dotProduct, Matrix.mul_apply]

theorem hs_mul_right_le (X B : Matrix ι ι ℂ) : hs (X * B) ≤ hs X * ‖B‖ := by
  rw [← hs_conjTranspose, conjTranspose_mul, ← hs_conjTranspose X, ← l2_opNorm_conjTranspose B,
    mul_comm]
  exact hs_mul_left_le _ _

end HS

section Inner

variable {f : ℕ} {p q : Fin f → ℕ}

end Inner

section Frame

end Frame

end UnitaryRecombination

namespace UnitaryRecombination

section ExpBound

end ExpBound

section Dim

variable (p q : ℕ)

end Dim

end UnitaryRecombination

namespace UnitaryRecombination

section Places

variable {ι : Type*} [Fintype ι]

variable (F : OrthoFrame)

end Places

end UnitaryRecombination

namespace UnitaryRecombination

section Products

variable (F : OrthoFrame)

end Products

end UnitaryRecombination

end SecondKind

end

end GroundTheory.Heights₂.Theta
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq =====
