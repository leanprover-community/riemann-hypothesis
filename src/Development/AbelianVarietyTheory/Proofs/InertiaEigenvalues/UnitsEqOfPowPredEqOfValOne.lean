module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory

theorem eq_of_pow_pred_eq_of_sub_one_mem {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R)
    (hI : I ≠ ⊤) (l : ℕ) (hl : 0 < l) (hlI : (l : R) ∈ I) (a b : R)
    (hab : a ^ (l - 1) = b ^ (l - 1)) (ha : a - 1 ∈ I) (hb : b - 1 ∈ I) : a = b := by
  by_contra hne
  have h := geom_sum₂_mul a b (l - 1)
  rw [hab, sub_self] at h
  have hs := (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have ha' : Ideal.Quotient.mk I a = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact ha
  have hb' : Ideal.Quotient.mk I b = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hb
  have hl' : (l : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hlI
  have h2 := congrArg (Ideal.Quotient.mk I) hs

  simp only [map_sum, map_mul, map_pow, ha', hb', one_pow, mul_one, Finset.sum_const,
  Finset.card_range, nsmul_eq_mul, map_zero] at h2
  rw [Nat.cast_sub hl, hl', Nat.cast_one, zero_sub, neg_eq_zero] at h2
  apply hI
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem, map_one]
  exact h2

def posValIdeal {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) : Ideal ↥(OL LL) where
  carrier := {x | 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, (algebraMap ↥(OL LL) ↥LL.1).map_add] at ha hb ⊢
    exact (P.v LL).map_lt_add ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, (algebraMap ↥(OL LL) ↥LL.1).map_mul,
      AddValuation.map_mul] at hx ⊢
    have hc : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 c) := (P.v_O LL _).2 c.2
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)

theorem oneUnit_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (a b : ↥(OL LL)) (hab : a ^ (l - 1) = b ^ (l - 1))
    (ha : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 a - 1))
    (hb : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 b - 1)) : a = b := by
  refine eq_of_pow_pred_eq_of_sub_one_mem (posValIdeal P LL) ?_ l (Fact.out : l.Prime).pos ?_ a b
    hab ?_ ?_
  · rw [Ne, Ideal.eq_top_iff_one]
    change ¬ 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 1)
    simp
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)))
    rw [map_natCast, P.v_l]
    exact zero_lt_one
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (a - 1))
    rwa [map_sub, map_one]
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (b - 1))
    rwa [map_sub, map_one]

theorem units_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (u w : (↥(OL LL))ˣ) (h : u ^ (l - 1) = w ^ (l - 1))
    (hu : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (u : ↥(OL LL)) - 1))
    (hw : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1)) : u = w := by
  apply Units.ext
  refine oneUnit_eq_of_pow_pred_eq_of_pos P LL _ _ ?_ hu hw
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h]

theorem units_eq_of_pow_pred_eq_of_val_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (LL : FinExt l) (u w : (↥(OL LL))ˣ), u ^ (l - 1) = w ^ (l - 1) →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((u : ↥(OL LL)) - 1)) = 1 →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1) = 1 → u = w := by
  intro l _ P LL u w h hu hw
  rw [map_sub, map_one] at hu
  refine units_eq_of_pow_pred_eq_of_pos P LL u w h ?_ ?_
  · rw [hu]; exact zero_lt_one
  · rw [hw]; exact zero_lt_one

end GlobalTheory
