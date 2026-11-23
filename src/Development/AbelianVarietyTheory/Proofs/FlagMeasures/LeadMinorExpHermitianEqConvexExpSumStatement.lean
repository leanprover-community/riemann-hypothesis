module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Analysis.Matrix.Spectrum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorExpHermitianEqConvexExpSum
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

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n), ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧ ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl = ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | exact GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | (intros; apply GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum <;> assumption)
