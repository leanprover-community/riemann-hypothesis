module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLowerBoundNearInjective
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

open MeasureTheory
open scoped ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.uniform_lower_bound_near_injective : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm → ∀ (c : P) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → Function.Injective (A c) → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by
  first | exact @GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | exact GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | (intros; apply GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective <;> assumption)
