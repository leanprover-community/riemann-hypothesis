module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBound
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.mixed_energy_regularization_bound : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) → IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧ ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  exact @GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail
