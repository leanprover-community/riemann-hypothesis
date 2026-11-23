module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnfoldingKernelLevelSubgroupBruhat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_unfoldingKernel_levelSubgroup_bruhat_alt : ∀ (G G' T T' : Type) [Group G] [Group G'] [Group T] [Group T'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableSpace T] [MeasurableSpace T'] [MeasurableMul G'] [MeasurableMul T] [MeasurableInv T'] (μ : Measure G) (μ' : Measure G') [μ'.IsMulLeftInvariant] (m : Measure T) (m' : Measure T') [m'.IsInvInvariant] (K : Subgroup G) (K' : Subgroup G'), MeasurableSet (K : Set G) → MeasurableSet (K' : Set G') → ∀ (φ : G' →* G) (ψ : G →* T) (ψ' : G' →* T') (j : T' →* T), Measurable ψ → Measurable ψ' → Measurable j → (∀ g, φ g ∈ K ↔ g ∈ K') → (∀ g, ψ (φ g) = j (ψ' g)) → (μ.restrict K).map ψ = m → (μ'.restrict K').map ψ' = m' → ∀ (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∀ (f : T → ℝ≥0∞), Measurable f → (∀ s t, f (j s * t) = f t) → ∀ ν, IsQuotientMeasure j m' m ν → ∃ u : G → ℝ≥0∞, Measurable u ∧ ∫⁻ h, u h ∂μ = ∫⁻ c, f (Quotient.out c) ∂ν ∧ ∀ h, ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ' = {h | ∃ g, (φ g)⁻¹ * h ∈ K}.indicator 1 h * f (ψ h) := by
  first | exact @GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat | exact GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat | (intros; apply GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat <;> assumption)
