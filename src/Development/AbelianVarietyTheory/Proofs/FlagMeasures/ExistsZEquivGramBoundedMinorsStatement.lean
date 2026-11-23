module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsZEquivGramBoundedMinors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField Module Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

theorem _root_.GlobalTheory.T.exists_zEquiv_gram_bounded_minors : ∀ (K : Type) [Field K] [NumberField K], (∀ w : InfinitePlace K, w.IsComplex) → ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (p : Point K (r + 1)), IsInCell (ZhatOM Z) p → ∃ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ZEquiv Z Z₂ ∧ ∀ (τ : K →+* ℂ) (t : ℕ) (I J : Fin t → Fin (r + 1)), ‖τ (Z₂.submatrix I J).det‖ ≤ 4 ^ (r + 1) * (((r + 1).factorial : ℕ) : ℝ) ^ 2 * (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) ^ (2 * (r + 1)) * ∏ l ∈ Finset.Icc 1 (r + 1), (max 1 ‖τ (leadMinorE Z l)‖ * max 1 ‖τ (leadMinorE Z l)‖⁻¹) := by
  first | exact @GlobalTheory.ReducedGram.exists_reduced | exact GlobalTheory.ReducedGram.exists_reduced | (intros; apply GlobalTheory.ReducedGram.exists_reduced <;> assumption)
