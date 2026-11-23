module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeLeRankMulSlope
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull

@[expose] public section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.normalized_degree_le_rank_mul_slope : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (μ : ℝ), E.slopeMax ≤ (μ : EReal) → ∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E.rank F * μ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le | exact GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le | (intros; apply GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le <;> assumption)
