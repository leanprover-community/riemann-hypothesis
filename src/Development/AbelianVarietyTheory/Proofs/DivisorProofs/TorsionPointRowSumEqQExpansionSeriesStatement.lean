module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointRowSumEqQExpansionSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (b : ZMod N) (d : ℕ+), 1 ≤ e → (∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * ch N (((j : ℕ) : ZMod N) * b) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) ∧ ∑' m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ((-1) ^ (e + 1) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * ch N (-(((j : ℕ) : ZMod N) * b)) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) := by
  first | exact @GlobalTheory.WpFam.torsion_row_series | exact GlobalTheory.WpFam.torsion_row_series | (intros; apply GlobalTheory.WpFam.torsion_row_series <;> assumption)
