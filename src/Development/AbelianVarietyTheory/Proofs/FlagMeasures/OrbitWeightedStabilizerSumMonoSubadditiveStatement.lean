module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditive
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

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive : ∀ (G α : Type) [Group G] [MulAction G α] , (∀ (X Y : Set α) (N N' : α → ℝ≥0∞), X ⊆ Y → (∀ x ∈ X, N x ≤ N' x) → orbSum G X N ≤ orbSum G Y N') ∧ (∀ (X : Set α) (B : ℝ≥0∞), orbSum G X (fun _ => B) = B * orbMass G X) ∧ (∀ (ι : Type) (s : Finset ι) (X : Set α) (Xi : ι → Set α) (N : α → ℝ≥0∞), X ⊆ ⋃ i ∈ s, Xi i → orbSum G X N ≤ ∑ i ∈ s, orbSum G (Xi i) N) ∧ (∀ (X : Set α) (s : Set α), (∀ x ∈ X, ∃ y ∈ s, ∃ g : G, g • y = x) → orbMass G X ≤ ((s.encard : ℕ∞) : ℝ≥0∞)) ∧ (∀ (X : Set α) (N N' : α → ℝ≥0∞), orbSum G X (fun x => N x + N' x) = orbSum G X N + orbSum G X N') := by
  first | exact @GlobalTheory.Mass.OrbMono.main | exact GlobalTheory.Mass.OrbMono.main | (intros; apply GlobalTheory.Mass.OrbMono.main <;> assumption)
