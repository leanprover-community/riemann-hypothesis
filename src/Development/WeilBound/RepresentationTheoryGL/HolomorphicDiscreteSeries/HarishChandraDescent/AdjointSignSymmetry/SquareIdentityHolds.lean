module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3.SquareIdentity

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M}

theorem adjSign_real (a b : Fin n) : adjSign ε a b = ((if ε a = ε b then (1 : ℝ) else -1 : ℝ) : ℂ) := by
  unfold adjSign; split_ifs <;> simp

theorem adjSign_sq (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign; split_ifs <;> norm_num

theorem adjSign_symm (a b : Fin n) : adjSign ε b a = adjSign ε a b := by
  by_cases h : ε a = ε b
  · simp [adjSign, h]
  · simp [adjSign, h, Ne.symm h]

private theorem re_inner_self_eq_norm_sq' (x : M) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl

theorem term (hU : IsInfUnitary ε E) (a b : Fin n) (x : M) :
    (⟪(E a b * E b a) x, x⟫_ℂ).re = (if ε a = ε b then (1 : ℝ) else -1) * ‖E b a x‖ ^ 2 := by
  rw [Module.End.mul_apply, hU a b, adjSign_real, Complex.re_ofReal_mul, re_inner_self_eq_norm_sq']

theorem inner_sum_re (T : Fin n → Fin n → Module.End ℂ M) (s : Fin n → Finset (Fin n)) (x : M) :
    (⟪(∑ a, ∑ b ∈ s a, T a b) x, x⟫_ℂ).re = ∑ a, ∑ b ∈ s a, (⟪T a b x, x⟫_ℂ).re := by
  simp only [LinearMap.sum_apply, sum_inner, Complex.re_sum]

theorem swap_eq (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f b a = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f a b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε a = ε b
  · simp [h]
  · simp [h, Ne.symm h]

theorem swap_ne (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), f b a = ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), f a b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε a = ε b
  · simp [h]
  · simp [h, Ne.symm h]

theorem casK_re (hU : IsInfUnitary ε E) (x : M) :
    (⟪casimirK ε E x, x⟫_ℂ).re = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b x‖ ^ 2 := by
  calc (⟪casimirK ε E x, x⟫_ℂ).re
      = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E b a x‖ ^ 2 := by
        unfold casimirK
        have h := inner_sum_re (fun a b => E a b * E b a) (fun a => univ.filter (fun b => ε b = ε a)) x
        rw [h]
        refine sum_congr rfl fun a _ => sum_congr rfl fun b hb => ?_
        rw [term hU, if_pos (mem_filter.mp hb).2.symm, one_mul]
    _ = _ := swap_eq (fun a b => ‖E a b x‖ ^ 2)

theorem cas_re (hU : IsInfUnitary ε E) (x : M) :
    (⟪casimir E x, x⟫_ℂ).re = ∑ a, ∑ b, (if ε a = ε b then (1 : ℝ) else -1) * ‖E b a x‖ ^ 2 := by
  unfold casimir
  have h := inner_sum_re (M := M) (fun a b => E a b * E b a) (fun _ => univ) x
  rw [h]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => term hU a b x

theorem diff_re (hU : IsInfUnitary ε E) (x : M) :
    (⟪casimirK ε E x, x⟫_ℂ).re - (⟪casimir E x, x⟫_ℂ).re =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), ‖E a b x‖ ^ 2 := by
  rw [cas_re hU, casK_re hU]
  have hsplit : ∀ a, ∑ b, (if ε a = ε b then (1 : ℝ) else -1) * ‖E b a x‖ ^ 2 =
      ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E b a x‖ ^ 2 -
        ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), ‖E b a x‖ ^ 2 := by
    intro a
    rw [← sum_filter_add_sum_filter_not univ (fun b => ε b = ε a), sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    · exact sum_congr rfl fun b hb => by rw [if_pos (mem_filter.mp hb).2.symm, one_mul]
    · exact sum_congr rfl fun b hb => by
        rw [if_neg (fun h => (mem_filter.mp hb).2 h.symm)]
        ring
  rw [sum_congr rfl fun a _ => hsplit a, sum_sub_distrib]
  have e1 := swap_eq (ε := ε) (fun a b => ‖E a b x‖ ^ 2)
  have e2 := swap_ne (ε := ε) (fun a b => ‖E a b x‖ ^ 2)
  rw [e1, e2]
  ring

theorem cas_symm (hU : IsInfUnitary ε E) (x y : M) : ⟪casimir E x, y⟫_ℂ = ⟪x, casimir E y⟫_ℂ := by
  unfold casimir
  simp only [LinearMap.sum_apply, sum_inner, inner_sum, Module.End.mul_apply]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [hU a b, hU b a, adjSign_symm a b, ← mul_assoc, adjSign_sq, one_mul]

end PositivityTheory.RgHe3.SquareIdentity

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

theorem square_identity_holds : SqId := by
  intro n ε M _ _ E _ hU x
  exact ⟨SquareIdentity.casK_re hU x, SquareIdentity.diff_re hU x, fun y => SquareIdentity.cas_symm hU x y⟩

end PositivityTheory.RgHe3
