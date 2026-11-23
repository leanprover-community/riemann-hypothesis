module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallS
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

theorem _root_.GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ), (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  first | exact @GlobalTheory.DeepPoint.deep_point | exact GlobalTheory.DeepPoint.deep_point | (intros; apply GlobalTheory.DeepPoint.deep_point <;> assumption)
