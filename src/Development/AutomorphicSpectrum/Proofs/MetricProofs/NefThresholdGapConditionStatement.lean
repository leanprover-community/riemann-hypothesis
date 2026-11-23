module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefThresholdGapCondition
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.nef_threshold_gap_condition : ∀ (T : Type) [Fintype T] (N j p : ℕ) (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ), 2 < p → 1 ≤ j → j < N → GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu → (∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i) → (∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) → GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) ∧ lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum | exact GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum <;> assumption)
