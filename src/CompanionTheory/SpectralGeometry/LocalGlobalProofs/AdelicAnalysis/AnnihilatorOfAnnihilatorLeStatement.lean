module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AnnihilatorOfAnnihilatorLe
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.annihilator_of_annihilator_le : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (μ : Measure V), μ.IsAddHaarMeasure → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → ∀ L₁ L L₂ : AddSubgroup V, L₁ ≤ L → L ≤ L₂ → IsOpen (L₁ : Set V) → IsCompact (L₂ : Set V) → IsCompact (perp χ L₁) → IsOpen (perp χ L₂) → perp χ (perp χ L₁) ⊆ L₁ → perp χ (perp χ L₂) ⊆ L₂ → μ L₁ * μ (perp χ L₁) = 1 → μ L₂ * μ (perp χ L₂) = 1 → IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.CofinalDual.selfDual_of_between | exact GlobalTheory.CompanionTheory.SW.CofinalDual.selfDual_of_between | (intros; apply GlobalTheory.CompanionTheory.SW.CofinalDual.selfDual_of_between <;> assumption)
