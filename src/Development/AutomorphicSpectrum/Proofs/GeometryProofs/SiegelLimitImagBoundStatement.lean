module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SiegelLimitImagBound
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

theorem _root_.GlobalTheory.T.siegel_limit_imag_bound : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ) (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (c : ℝ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ), 0 < c → Tendsto σs atTop (𝓝 σ) → Tendsto (fun m => (t m).im) atTop atTop → (∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ))) → (∀ m, ((τs m).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v)) → Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y) → ∃ u v : Fin g → ℤ, Bs *ᵥ v = 0 ∧ y = (fun k => (u k : ℂ)) + σ *ᵥ (fun k => (v k : ℂ)) ∧ ∀ᶠ m in atTop, us m = u ∧ vs m = v := by
  first | exact @GlobalTheory.CompanionTheory.PeriodLimitSeq.limit_seq | exact GlobalTheory.CompanionTheory.PeriodLimitSeq.limit_seq | (intros; apply GlobalTheory.CompanionTheory.PeriodLimitSeq.limit_seq <;> assumption)
