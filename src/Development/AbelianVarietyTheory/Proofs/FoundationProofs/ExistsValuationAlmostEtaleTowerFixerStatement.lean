module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationAlmostEtaleTowerFixer
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

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_valuation_almostEtale_towerFixer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω), ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ GlobalTheory.K5.IsInt (p := p) x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 ∧ ∀ S : Finset Ω, ∃ U : Subgroup ↥(⨅ n, Gn T n), U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix Ω U) ∧ AlmostSep v U := by
  first | exact @GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | exact GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | (intros; apply GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep <;> assumption)
