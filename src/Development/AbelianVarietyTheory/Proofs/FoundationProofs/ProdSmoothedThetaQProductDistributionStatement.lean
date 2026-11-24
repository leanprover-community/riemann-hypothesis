module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSmoothedThetaQProductDistribution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.prod_smoothedThetaQProduct_distribution : ∀ (c m : ℕ) (Q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖Q‖ < 1 → Q ≠ 0 → t ≠ 0 → (∀ n : ℤ, Q ^ n * t ^ c ≠ 1) → ∏ j ∈ Finset.range m, cth c (Q ^ m) (t * Q ^ j) = cth c Q t := by
  first | exact @GlobalTheory.Sieg.prod_cth_mul_pow | exact GlobalTheory.Sieg.prod_cth_mul_pow | (intros; apply GlobalTheory.Sieg.prod_cth_mul_pow <;> assumption)
