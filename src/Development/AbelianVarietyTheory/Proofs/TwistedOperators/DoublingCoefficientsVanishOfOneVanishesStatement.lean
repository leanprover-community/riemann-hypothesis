module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingCoefficientsVanishOfOneVanishes
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.doublingCoefficients_vanish_of_one_vanishes : ∀ (p q : ℕ) (T : GrpData p q) (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), Function.Injective j₂ → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') → (∀ U : Submodule ℂ E, (∀ k ∈ T.Kset, ∀ w ∈ U, ∀ w' : E, π₂.π k (j₂ w) = j₂ w' → w' ∈ U) → U = ⊥ ∨ U = ⊤) → ∀ v : E, v ≠ 0 → MeasureTheory.Integrable (fun g => inner ℂ (j₂ v) (π₂.π g (j₂ v))) T.haar → (∀ z : π₁.H, ∫ g, inner ℂ z (π₁.π g (j₁ v)) * star (inner ℂ (j₂ v) (π₂.π g (j₂ v))) ∂T.haar = 0) → (∀ x y u w : E, MeasureTheory.Integrable (fun g => inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w)))) T.haar ∧ ∫ g, inner ℂ (j₁ x) (π₁.π g (j₁ y)) * star (inner ℂ (j₂ u) (π₂.π g (j₂ w))) ∂T.haar = 0) := by
  first | exact @GlobalTheory.DoublingVanish.vanish | exact GlobalTheory.DoublingVanish.vanish | (intros; apply GlobalTheory.DoublingVanish.vanish <;> assumption)
