module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityTimeDerivative
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

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.energy_density_time_derivative : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → ∀ (s : ℝ), ∀ y ∈ GLs n, HasDerivAt (fun r => dens u r y) (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ + 2 * ⟪dt u s y, u s y⟫_ℝ) s := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens | exact GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens <;> assumption)
