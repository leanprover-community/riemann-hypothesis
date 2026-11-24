module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantMeasureLowerBoundOfChart
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.ofReal_pow_le_measure_of_chart_cover : ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype ι] (mK : Measure G) [IsProbabilityMeasure mK] (K U : Set G) (θ : (ι → ℝ) → G) (T δ : ℝ), Continuous θ → IsClosed U → mK Kᶜ = 0 → (∀ R, Measure.map (fun x => θ R * x) mK = mK) → 0 < δ → 0 ≤ T → (∀ x ∈ K, ∃ R₀ : ι → ℝ, (∀ i, |R₀ i| ≤ T) ∧ ∀ R : ι → ℝ, (∀ i, |R i - R₀ i| ≤ δ) → (θ R)⁻¹ * x ∈ U) → ENNReal.ofReal ((δ / (T + δ)) ^ Fintype.card ι) ≤ mK U := by
  first | exact @GlobalTheory.CartanInt.invariant_measure_lower_bound_of_chart | exact GlobalTheory.CartanInt.invariant_measure_lower_bound_of_chart | (intros; apply GlobalTheory.CartanInt.invariant_measure_lower_bound_of_chart <;> assumption)
