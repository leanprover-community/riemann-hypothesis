module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

namespace GlobalTheory.RootNormBound

open Polynomial

theorem pow_card_le_norm_prod {ε : ℝ} (hε : 0 ≤ ε) (s : Multiset ℂ)
    (hs : ∀ t ∈ s, ε ≤ ‖t‖) :
    ε ^ Multiset.card s ≤ ‖(s.map (fun a => (0 : ℂ) - a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, norm_mul, mul_comm]
    have ha : ε ≤ ‖(0 : ℂ) - a‖ := by
      rw [zero_sub, norm_neg]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hε _)
      (norm_nonneg _)

theorem exists_root_norm_lt {h : Polynomial ℂ} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t : ℂ, h.IsRoot t ∧ ‖t‖ < ε := by
  by_contra hne
  push Not at hne
  have hsp : h.Splits := IsAlgClosed.splits h
  have hne0 : h ≠ 0 := hm.ne_zero
  have key := pow_card_le_norm_prod hε h.roots fun t ht => hne t ((mem_roots hne0).1 ht)
  rw [← hsp.eval_eq_prod_roots_of_monic hm 0, ← coeff_zero_eq_eval_zero,
    ← hsp.natDegree_eq_card_roots] at key
  exact absurd hc (not_lt.2 key)

end GlobalTheory.RootNormBound
