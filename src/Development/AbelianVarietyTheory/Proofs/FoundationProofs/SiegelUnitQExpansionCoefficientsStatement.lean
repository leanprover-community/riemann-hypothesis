module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficients
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

theorem _root_.GlobalTheory.T.siegel_unit_q_expansion_coefficients : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b : ℕ), 0 < M → a < M → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → Ω), GlobalTheory.QFam.HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => ε (A n)) ∧ (∀ n : ℕ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff (((k : ℚ) + n) / M) = A n) ∧ ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r = 0 := by
  first | exact @GlobalTheory.KExp.siegel_exp | exact GlobalTheory.KExp.siegel_exp | (intros; apply GlobalTheory.KExp.siegel_exp <;> assumption)
