module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem omA_diag_boxFn_succ :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (C : Matrix A D k), (∀ j, C i₀ j = 0) → ∀ m n : ℕ, GlobalTheory.SplitFlip.omA ν β (GlobalTheory.SplitFlip.diagGL (Function.update 1 i₀ ϖ)) 1 (GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ n)) = ((((ν ϖ)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow ϖ (-(Fintype.card D : ℂ) / 2)) • GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ C hC m n
  have hdet : GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ)) = ϖ := by
    rw [GlobalTheory.SplitFlip.gdet, GlobalTheory.SplitFlip.det_diagGL, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hinv : ((GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ))⁻¹).val =
      diagonal fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k) := rfl
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have key : ∀ X : Matrix A D k,
      (diagonal (fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k)) * X) ∈
        box ϖ C (Function.update (fun _ => m) i₀ n) ↔ X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
    intro X
    simp only [box, Set.mem_setOf_eq, diagonal_mul]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases hi : i = i₀
    · subst hi
      simp only [Function.update_self, hC, sub_zero, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        pow_succ, Units.val_mul, map_mul, map_inv₀, map_pow]
      rw [inv_mul_le_iff₀ h0, mul_comm (valuation k (ϖ : k))]
    · simp [Function.update_of_ne hi]
  funext X
  rw [GlobalTheory.RankCoinv.omA_one_apply, hdet, Pi.smul_apply, smul_eq_mul, hinv]
  congr 1
  unfold boxFn
  by_cases hX : X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1))
  · rw [Set.indicator_of_mem ((key X).2 hX), Set.indicator_of_mem hX]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hX ((key X).1 h)), Set.indicator_of_notMem hX]

end GlobalTheory.RankCoinv
