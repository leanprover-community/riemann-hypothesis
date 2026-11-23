module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvariantMeasureQuadricMulHaarStabilizer
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
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.invariant_measure_quadric_mul_haar_stabilizer : ∀ (P Q P' Q' : ℕ) (β : ℝ) (x₀ : Sp P Q) (j : UpqT P' Q' →* UpqT P Q) (ν : Measure (Sp P Q)) (μ : Measure (UpqT P Q)) (μ' : Measure (UpqT P' Q')), Topology.IsClosedEmbedding j → Set.range j = {g | act g x₀ = x₀} → IsFiniteMeasureOnCompacts ν → (∀ᵐ y ∂ν, qf y = β) → (∀ g : UpqT P Q, ν.map (act g) = ν) → μ.IsHaarMeasure → μ'.IsHaarMeasure → ∃ κ : ℝ≥0, ∀ s : Sp P Q → UpqT P Q, IsSection β x₀ s → ∀ f : UpqT P Q → ℝ≥0∞, Measurable f → ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν = κ * ∫⁻ g, f g ∂μ := by
  first | exact @GlobalTheory.QuadricHaar.quadric_haar | exact GlobalTheory.QuadricHaar.quadric_haar | (intros; apply GlobalTheory.QuadricHaar.quadric_haar <;> assumption)
