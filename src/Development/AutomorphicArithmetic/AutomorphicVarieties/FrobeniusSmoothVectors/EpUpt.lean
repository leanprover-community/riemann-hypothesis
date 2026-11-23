module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_upt :
    ∀ {C : Type} [CommRing C] {n : ℕ} (h T T' : Matrix (Fin n) (Fin n) C), UpT T → UpT T' → (∀ i j, j < i → IsUnit (T j j - T' i i)) → h * T = T' * h → UpT h := by
  intro C _ n h T T' hT hT' hu hc
  suffices key : ∀ m, ∀ i j : Fin n, j.val + (n - i.val) = m → j < i → h i j = 0 by
    intro i j hji
    exact key _ i j rfl hji
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i j hm hji
    have e := congrFun (congrFun hc i) j
    simp only [Matrix.mul_apply] at e
    have hji' := Fin.lt_iff_val_lt_val.mp hji
    have L : ∑ k, h i k * T k j = h i j * T j j := by
      rw [Finset.sum_eq_single j]
      · intro k _ hkj
        rcases lt_or_gt_of_ne hkj with hk | hk
        · have hk' := Fin.lt_iff_val_lt_val.mp hk
          rw [ih (k.val + (n - i.val)) (by omega) i k rfl (hk.trans hji), zero_mul]
        · rw [hT k j hk, mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ j) hn
    have R : ∑ k, T' i k * h k j = T' i i * h i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with hk | hk
        · rw [hT' i k hk, zero_mul]
        · have hk' := Fin.lt_iff_val_lt_val.mp hk
          have hkn := k.isLt
          rw [ih (j.val + (n - k.val)) (by omega) k j rfl (hji.trans hk), mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ i) hn
    rw [L, R] at e
    have e2 : h i j * (T j j - T' i i) = 0 := by
      rw [mul_sub, e, mul_comm]
      exact sub_self _
    exact (hu i j hji).mul_left_eq_zero.mp e2
