module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEstimateGaloisEigenvectorCLTate
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tate_estimate_galois_eigenvector_cLTate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  first | exact @GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate | exact GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate | (intros; apply GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate <;> assumption)
