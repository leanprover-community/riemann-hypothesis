module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataProperties
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.regular_chart_data_properties : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A), IsOpen R.Yo ∧ (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0) ∧ ContinuousOn R.r R.Yo ∧ ∀ ℓ : ℝ, IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ ℓ} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part | exact GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part <;> assumption)
