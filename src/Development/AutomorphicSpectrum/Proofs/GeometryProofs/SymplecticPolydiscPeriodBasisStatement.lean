module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis
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

open Filter Topology Matrix

theorem _root_.GlobalTheory.T.symplectic_polydisc_period_basis : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : GlobalTheory.CompanionTheory.Ar.Flat.LogPeriods n a g Λ), ∃ (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (Q : GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc n a g) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧ L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0) ∧ (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (Metric.ball 0 1)) ∧ (A 0).det ≠ 0 ∧ Q.IsTau0Ext T0 ∧ (∀ i, ((Q.B i).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ i k, L.P w (bas (.inl i)) k = A (GroundTheory.Heights₂.Heights.Regular.expCover a w) i k) ∧ ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ j, L.P w (bas (.inr j)) = ∑ k, Q.τ w j k • L.P w (bas (.inl k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame <;> assumption)
