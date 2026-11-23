module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedQExpansionDouble
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double : ∀ (j : ℕ) (c : ℂ) (a b : ℤ → ℂ), (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → PolyB (eis j c a b) ∧ (∃ C : ℝ, ∀ n, n ≠ 0 → ‖eis j c a b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (j - 1)) ∧ ∀ τ : ℍ, HasSum (fun y : ℕ => b (y + 1 : ℕ) * ∑' x : ℕ, ((x + 1 : ℕ) : ℂ) ^ (j - 1) * a (x + 1 : ℕ) * cexp (2 * π * Complex.I * (x + 1 : ℕ) * ((y + 1 : ℕ) * τ))) (qs (eis j c a b) τ - c) := by
  first | exact @GlobalTheory.EisM.eis_qseries | exact GlobalTheory.EisM.eis_qseries | (intros; apply GlobalTheory.EisM.eis_qseries <;> assumption)
