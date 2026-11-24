module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace LateralTheory.Q.SZcT

open UpperTheory.V.ZK

def wd {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) : Fin (2 * e + 1 + 1) → Cq q :=
  fun i => if (i : ℕ) % 2 = 0 then Multiplicative.ofAdd (j ⟨i / 2, by omega⟩) else Multiplicative.ofAdd 1

theorem zc_eq (q : ℕ) [NeZero q] (e : ℕ) :
    zc q e = ∑ j : Fin (e + 1) → ZMod q, Finsupp.single (wd e j) 1 := rfl

theorem alt_range {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (T : ℕ → M) (n : ℕ)
    (h : ∀ a, a < n → T (2 * a) = T (2 * a + 1)) :
    ∑ p ∈ Finset.range (2 * n), ((-1 : A) ^ (p + 1)) • T p = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih fun a ha => h a (by omega), ← h n (by omega), pow_succ (-1 : A) (2 * n + 1)]
    simp

theorem alt_fin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (e : ℕ) (S : Fin (2 * e + 1 + 1) → M)
    (h : ∀ (a : ℕ) (ha : a < e + 1), S ⟨2 * a, by omega⟩ = S ⟨2 * a + 1, by omega⟩) :
    ∑ p : Fin (2 * e + 1 + 1), ((-1 : A) ^ ((p : ℕ) + 1)) • S p = 0 := by
  have key := alt_range (A := A) (fun p => if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0) (e + 1) (by
    intro a ha
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    exact h a ha)
  rw [show 2 * (e + 1) = 2 * e + 1 + 1 by ring, ← Fin.sum_univ_eq_sum_range
    (fun p => ((-1 : A) ^ (p + 1)) • (if hp : p < 2 * e + 1 + 1 then S ⟨p, hp⟩ else 0))] at key
  rw [← key]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [dite_eq_left p.2]

theorem wd_even {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1)) (k : Fin (e + 1))
    (h : (i : ℕ) = 2 * k) : wd e j i = Multiplicative.ofAdd (j k) := by
  unfold wd
  rw [if_pos (by omega)]
  congr 2
  ext
  show (i : ℕ) / 2 = k
  omega

theorem wd_odd {q : ℕ} (e : ℕ) (j : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1))
    (h : (i : ℕ) % 2 = 1) : wd e j i = Multiplicative.ofAdd 1 := by
  unfold wd
  rw [if_neg (by omega)]

theorem wd_congr {q : ℕ} (e : ℕ) (j j' : Fin (e + 1) → ZMod q) (i : Fin (2 * e + 1 + 1))
    (h : ∀ k : Fin (e + 1), (i : ℕ) = 2 * k → j k = j' k) : wd e j i = wd e j' i := by
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have hk : (i : ℕ) = 2 * ((⟨i / 2, by omega⟩ : Fin (e + 1)) : ℕ) := by
      show (i : ℕ) = 2 * (i / 2)
      omega
    rw [wd_even e j i _ hk, wd_even e j' i _ hk, h _ hk]
  · rw [wd_odd e j i hi, wd_odd e j' i hi]

theorem tail_sum (q : ℕ) [NeZero q] (e : ℕ) :
    (∑ j : Fin (e + 1) → ZMod q, Finsupp.single (fun i : Fin (2 * e + 1) => wd e j i.succ) 1 :
      Ch (ZMod q) (Cq q) (2 * e + 1)) = 0 := by
  rw [← (Fin.consEquiv fun _ : Fin (e + 1) => ZMod q).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h : ∀ x : ZMod q, (fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (x, j)) i.succ) =
      fun i : Fin (2 * e + 1) => wd e (Fin.consEquiv (fun _ => ZMod q) (0, j)) i.succ := by
    intro x
    funext i
    refine wd_congr e _ _ _ fun k hk => ?_
    induction k using Fin.cases with
    | zero => simp at hk
    | succ k => simp [Fin.consEquiv]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, Finsupp.smul_single]
  simp

def sh (q e a : ℕ) : Fin (e + 1) → ZMod q := fun k => if (k : ℕ) = a then 1 else if (k : ℕ) = a + 1 then -1 else 0

theorem contract_eq {q : ℕ} (e a : ℕ) (ha : a < e + 1) (j : Fin (e + 1) → ZMod q) :
    Fin.contractNth (⟨2 * a, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (wd e j) =
      Fin.contractNth (⟨2 * a + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (wd e (j + sh q e a)) := by
  funext i
  have hi := i.2
  rcases lt_trichotomy (i : ℕ) (2 * a) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega)]
    refine wd_congr e _ _ _ fun k hk => ?_
    rw [Fin.val_castSucc] at hk
    rw [Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by show (i : ℕ) < 2 * a + 1; omega),
      wd_even e j i.castSucc ⟨a, ha⟩ h, wd_even e _ i.castSucc ⟨a, ha⟩ h,
      wd_odd e j i.succ (by rw [Fin.val_succ]; omega), Pi.add_apply, sh, if_pos rfl, ofAdd_add]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    rcases (show (i : ℕ) = 2 * a + 1 ∨ 2 * a + 1 < i by omega) with h' | h'
    · have hk : ((i.succ : Fin (2 * e + 1 + 1)) : ℕ) = 2 * ((⟨a + 1, by omega⟩ : Fin (e + 1)) : ℕ) := by
        rw [Fin.val_succ]
        show (i : ℕ) + 1 = 2 * (a + 1)
        omega
      rw [Fin.contractNth_apply_of_eq _ _ _ _ h', wd_even e j _ _ hk, wd_even e _ _ _ hk,
        wd_odd e _ i.castSucc (by rw [Fin.val_castSucc]; omega), Pi.add_apply, sh, if_neg (by simp), if_pos rfl,
        ← ofAdd_add]
      congr 1
      ring
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ h']
      refine wd_congr e _ _ _ fun k hk => ?_
      rw [Fin.val_succ] at hk
      rw [Pi.add_apply, sh, if_neg (by omega), if_neg (by omega), add_zero]

theorem SZc_of : SZc := by
  intro q _ e
  unfold Cyc

  rw [zc_eq, map_sum]
  simp only [bd, Finsupp.linearCombination_single, one_smul]
  rw [Finset.sum_add_distrib, tail_sum, zero_add, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  refine alt_fin (A := ZMod q) e (fun p => ∑ j : Fin (e + 1) → ZMod q,
    (Finsupp.single (Fin.contractNth p (· * ·) (wd e j)) 1 : Ch (ZMod q) (Cq q) (2 * e + 1))) fun a ha => ?_
  refine Fintype.sum_equiv (Equiv.addRight (sh q e a)) _ _ fun j => ?_
  rw [contract_eq e a ha j]
  rfl

end LateralTheory.Q.SZcT

end
