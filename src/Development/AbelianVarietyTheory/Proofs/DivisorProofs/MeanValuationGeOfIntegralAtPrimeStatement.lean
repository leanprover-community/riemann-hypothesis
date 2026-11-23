module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationGeOfIntegralAtPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.meanValuation_ge_of_integral_at_prime : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}, GlobalTheory.FunObj.SqNum.IsMinPol σ β p → β ≠ 0 → ∀ {c : K}, c ≠ 0 → ∀ {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl K}, (l : 𝓞 K) ∈ w.asIdeal → ∀ {m : ℕ}, GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ m * (σ c * β)) → -((m : ℝ) * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w c : ℝ) + GlobalTheory.FunObj.SqNum.meanVal_vw w p := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | exact GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt <;> assumption)
