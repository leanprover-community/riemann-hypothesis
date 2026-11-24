module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict : (∃ A : (ℍ → ℂ) →+* Mero, ∀ f, A f = germ f) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (up f) Hs) ∧ (∀ a b : ℂ → ℂ, (∀ z ∈ Hs, a z = b z) → (a : Mero) = (b : Mero)) ∧ (∀ a : ℂ → ℂ, germ (fun τ : ℍ => a τ) = (a : Mero)) ∧ ∀ τ : ℍ, (τ : ℂ) ∈ Hs := by
  first | exact @GlobalTheory.FN.germ_ringHom_and_restrict | exact GlobalTheory.FN.germ_ringHom_and_restrict | (intros; apply GlobalTheory.FN.germ_ringHom_and_restrict <;> assumption)
