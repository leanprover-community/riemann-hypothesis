module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceWeight

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] : ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

theorem norm_le_norm_elim_left {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖x‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inl j)

theorem iteratedFDeriv_sliceR_norm_le {κ κ' : Type} [Fintype κ] [Fintype κ']
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (n : ℕ) (y : κ' → V) :
    ‖iteratedFDeriv ℝ n (sliceR f x) y‖ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
  have hfun : (sliceR f x : (κ' → V) → ℂ) = (fun z => f (Sum.elim x 0 + z)) ∘ (inrL (V := V) κ κ') := by
    funext y'
    simp only [sliceR_apply, Function.comp_apply]
    exact congrArg f (congrFun (elim_eq_add (V := V) (κ' := κ') x) y')
  have hg : ContDiff ℝ ∞ (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast le_top)]
  have h2 : iteratedFDeriv ℝ n (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) (inrL κ κ' y)
      = iteratedFDeriv ℝ n f (Sum.elim x y) := by
    rw [iteratedFDeriv_comp_add_left]
    congr 1
    exact (congrFun (elim_eq_add (V := V) (κ' := κ') x) y).symm
  rw [h2]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖(inrL (V := V) κ κ')‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
  calc _ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem pow_norm_mul_seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (a k n : ℕ) (x : κ → V) :
    ‖x‖ ^ a * SchwartzMap.seminorm ℂ k n (sliceR f x) ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
  have hpt : ∀ y : κ' → V, ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
      ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
    intro y
    have h1 := iteratedFDeriv_sliceR_norm_le f x n y
    have hx := norm_le_norm_elim_left x y
    have hy := norm_le_norm_elim x y
    calc ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
        ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ a * (‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ k
            * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖) := by gcongr
      _ = ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ (a + k) * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
          rw [pow_add, mul_assoc]
      _ ≤ _ := SchwartzMap.le_seminorm ℂ (a + k) n f _
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x) a) with h0 | hpos
  · rw [← h0, zero_mul]; exact apply_nonneg _ _
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ k n _ (div_nonneg (apply_nonneg _ _) hpos.le) fun y => ?_
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt y

end GlobalTheory.SliceWeight
