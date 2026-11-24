module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.doubledFlag_sum_eq_unipotentDim_and_layerProd : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = dimN n j ∧ layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  first | exact @GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq | exact GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq | (intros; apply GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq <;> assumption)
