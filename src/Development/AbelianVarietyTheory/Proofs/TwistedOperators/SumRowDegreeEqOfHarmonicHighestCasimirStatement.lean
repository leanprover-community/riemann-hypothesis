module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumRowDegreeEqOfHarmonicHighestCasimir
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

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

theorem _root_.GlobalTheory.T.sum_row_degree_eq_of_harmonic_highest_casimir : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (k l n : ℕ) (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ), Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) → ∀ (P : MvPolynomial σ ℂ) (a : Fin k → ℕ) (b : Fin l → ℕ) (κ : Fin n → ℤ), P ≠ 0 → Antitone a → Antitone b → Antitone κ → (∀ i j, i < j → rowOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i j, i < j → rowOp ℂ y i j P = 0) → (∀ i, rowOp ℂ y i i P = (b i : ℂ) • P) → (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0) → (∀ i j, i < j → mixedOp ℂ z y i j P = 0) → (∀ t, mixedOp ℂ z y t t P = (κ t : ℂ) • P) → ∑ i, (a i : ℤ) = ∑ t, max (κ t) 0 := by
  first | exact @GlobalTheory.HarmRowDegree.sum_row_degree_eq | exact GlobalTheory.HarmRowDegree.sum_row_degree_eq | (intros; apply GlobalTheory.HarmRowDegree.sum_row_degree_eq <;> assumption)
