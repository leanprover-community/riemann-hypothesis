module

import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.LowHW

theorem height_root {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * Formalism.REAL.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem height_sum {n : ℕ} (c : Fin n → Fin n → ℕ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) i
      = ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
  simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h1 : CDom ε μ Λ) (h2 : CDom ε Λ μ) :
    μ = Λ := by
  apply Formalism.MainNotions.BridgeLemma.cdom_antisymm <;> assumption

end GlobalTheory.LowHW
