module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndT
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

theorem _root_.GlobalTheory.T.modular_law_of_s_and_t : ∀ (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ), (∀ x γ, P x → P (act x γ)) → (∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ) → (∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) → ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.modular_law_of_generators | exact GlobalTheory.Sieg.modular_law_of_generators | (intros; apply GlobalTheory.Sieg.modular_law_of_generators <;> assumption)
