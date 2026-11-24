module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformIndependentOfBase
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

theorem _root_.GlobalTheory.T.tube_transform_independent_of_base : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω → ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | exact GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex <;> assumption)
