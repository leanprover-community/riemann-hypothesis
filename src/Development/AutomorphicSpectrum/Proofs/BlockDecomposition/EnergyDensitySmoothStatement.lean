module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensitySmooth
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

theorem _root_.GlobalTheory.T.energy_density_smooth : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → Sm (dens u) ∧ ∀ (X : Mat n) (v : ℝ → Mat n → W), Sm v → Sm fun s y => ⟪Rt X u s y, v s y⟫_ℝ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | exact GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner <;> assumption)
