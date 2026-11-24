module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
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

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique : (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧ (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) := by
  first | exact @GlobalTheory.QFam.hasQ_unique_both | exact GlobalTheory.QFam.hasQ_unique_both | (intros; apply GlobalTheory.QFam.hasQ_unique_both <;> assumption)
