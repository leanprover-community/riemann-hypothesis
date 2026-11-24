module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffTsumOfLocallySummableBounds
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

open scoped ContDiff


theorem _root_.GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds : ∀ {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ), (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) → (∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧ ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  first | exact @GlobalTheory.contDiff_tsum_of_locally_summable_bounds | exact GlobalTheory.contDiff_tsum_of_locally_summable_bounds | (intros; apply GlobalTheory.contDiff_tsum_of_locally_summable_bounds <;> assumption)
