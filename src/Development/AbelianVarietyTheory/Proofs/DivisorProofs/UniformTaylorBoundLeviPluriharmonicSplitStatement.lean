module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformTaylorBoundLeviPluriharmonicSplit
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

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split : ∀ (n : ℕ) (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∃ h : V n → ℂ, Differentiable ℂ h ∧ h 0 = 0 ∧ ∀ w ∈ closedBall (0 : V n) δ, φ (z + w) ≤ φ z + 2 * (h w).re + (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re + η * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.PluriTaylor.taylor_levi_unif | exact GlobalTheory.PluriTaylor.taylor_levi_unif | (intros; apply GlobalTheory.PluriTaylor.taylor_levi_unif <;> assumption)
