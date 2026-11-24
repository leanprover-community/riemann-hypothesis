module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify
public import Formalism.HermitianCurvature.StatementB
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

@[expose] public section

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.GrowthW

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def hsN {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j))

theorem hsN_nonneg {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hsN g :=
  Real.sqrt_nonneg _

def SUpper {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Prop := ∀ i j : Fin m, j ≤ i → X i j = 0

def LieNUpper : Prop := ∀ (k r : ℕ) (X : Formalism.FourierDecayAlt.B.Mat k r), PI.WUN.InLieN k r X → SUpper X

def ExpUpper : Prop :=
  ∀ m : ℕ, 0 < m → ∃ C D : ℝ, 0 < D ∧ ∀ X : Matrix (Fin m) (Fin m) ℂ, SUpper X →
    1 + hsN X ≤ C * hsN (NormedSpace.exp X) ^ D

section Assembly

variable {k r : ℕ}

theorem norm_le_hsN (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    ‖x‖ ≤ hsN (unrealify x) := by
  rw [EuclideanSpace.norm_eq]
  unfold hsN
  apply le_of_eq
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [unrealify, Complex.normSq_mk, Real.norm_eq_abs, sq_abs]
  ring

end Assembly

end Formalism.MainNotions.GrowthW
