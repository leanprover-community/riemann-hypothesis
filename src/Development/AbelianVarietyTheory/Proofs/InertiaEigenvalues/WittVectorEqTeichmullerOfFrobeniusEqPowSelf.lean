module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTeichmullerOfFrobenius
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Teichmuller
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.InitTail
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open scoped NNReal

namespace GlobalTheory


open WittVector in
theorem wittVector_iterate_frobenius_of_eq_pow {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    (y : WittVector l O) (h : (WittVector.frobenius (p := l) (R := O)) y = y ^ l) (k : ℕ) :
    (WittVector.frobenius (p := l) (R := O))^[k] y = y ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]


open WittVector in
theorem wittVector_coeff_iterate_frobenius {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [CharP O l] (y : WittVector l O) (k n : ℕ) :
    ((WittVector.frobenius (p := l) (R := O))^[k] y).coeff n = y.coeff n ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ih, ← pow_mul, ← pow_succ]


open WittVector in
theorem wittVector_eq_teichmuller_of_frobenius_eq_pow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] [PerfectRing O l]
      (y : WittVector l O), WittVector.frobenius y = y ^ l →
      y = WittVector.teichmuller l (y.coeff 0) := by
  apply GlobalTheory.HWL.IoLayer.eq_teichmuller_of_frobenius <;> assumption

end GlobalTheory
