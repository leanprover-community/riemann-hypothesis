module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurent
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

open GlobalTheory.NL

theorem _root_.GlobalTheory.T.powerSeriesTwistedScaling_triangular_laurent : ∀ {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M] (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M), Monotone Sub → ∀ (y : ℕ) (f : ℤ → M), (∃ m : ℤ, ∀ j < m, f j = 0) → (∀ j, f j ∈ Sub j) → ∀ k : ℤ, (∀ j < k, f j ∈ Sub (j - y)) → (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧ (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧ (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧ conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  first | exact @GlobalTheory.NL.Twist.tri | exact GlobalTheory.NL.Twist.tri | (intros; apply GlobalTheory.NL.Twist.tri <;> assumption)
