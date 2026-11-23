module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

open Matrix in
theorem eh_inv_entry : ∀ (k r : ℕ) (a b c i : Fin (2 * r + k + 1)), ∀ g ∈ B.GV k r, Q.EH k r a b (fun y : B.Mat k r => y⁻¹ c i) g = -(if a = c then g⁻¹ b i else 0) := by
  intro k r a b c i g _
  have h := Formalism.FourierDecayAlt.P.Qx5.eh_inv (k := k) (r := r) (LinearMap.proj c) (Pi.single i 1) g a b
  have e : (fun y : B.Mat k r => y⁻¹ c i) = fun y : B.Mat k r => (LinearMap.proj c : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (y⁻¹ *ᵥ Pi.single i 1) := by
    funext y
    simp [Matrix.mulVec_single_one]
  rw [e]
  refine h.trans ?_
  by_cases hac : a = c
  · subst hac
    simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single, hac]
end GlobalTheory
