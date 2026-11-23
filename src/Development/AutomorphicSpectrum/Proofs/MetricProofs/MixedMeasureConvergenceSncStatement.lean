module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedMeasureConvergenceSnc
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

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.mixed_measure_convergence_snc : GroundTheory.Heights₂.Heights.AnalyticLimit.UniformIntegrability.Statement → TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas (e + 1) X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X), IsPotential A L' → IsSection A L' v → IsSNC A L' v ![1] ![Dg] → IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg) → ∀ (th : Fin (e + 1) → LocPot X) (ph : Fin (e + 1) → X → ℝ) (phT : Fin (e + 1) → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∀ η : ℝ, 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → Integrable (GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp L' v ε) (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) ∧ ∫ y, GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp L' v ε y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform | exact GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform <;> assumption)
