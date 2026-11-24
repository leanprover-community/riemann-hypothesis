module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianTubeTransformContinuous
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

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.gaussian_tube_transform_continuous : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] [FirstCountableTopology T] (G : T → ℂ × ℂ → X) (x : ℝ × ℝ), Continuous (fun p : (ℝ × ℝ) × T => G p.2 (pt x p.1)) → (∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ, ‖G g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → Continuous (fun p : (ℝ × ℝ) × T => phi (G p.2) x p.1) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous | exact GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous <;> assumption)
