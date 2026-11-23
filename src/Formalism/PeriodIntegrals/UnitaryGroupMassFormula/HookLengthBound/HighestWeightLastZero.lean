module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

theorem highest_weight_det_mul : HwDetMul := by
  intro N ν _
  cases N with
  | zero => simp [hw, detX]
  | succ n =>
    simp only [hw]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have hlast : ∀ μ : Fin (n + 1) → ℕ, nuNext μ (Fin.last n) = 0 := by
      intro μ; simp [nuNext]
    have hcs : ∀ s : Fin n, (ν s.castSucc + 1) - nuNext (fun i => ν i + 1) s.castSucc =
        ν s.castSucc - nuNext ν s.castSucc := by
      intro s
      have hs := s.isLt
      simp only [nuNext, Fin.val_castSucc]
      rw [dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega), dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega)]
      omega
    simp only [hlast, hcs, Nat.sub_zero]
    have hL : lpMinor ℚ ((Fin.last n : ℕ) + 1) (r := n + 1) (n := n + 1) (by simp) (by simp) =
        detX (n + 1) := rfl
    rw [hL, pow_succ]
    ring

theorem lpMinor_rename (n s : ℕ) (h1 h2 : s ≤ n) (h3 h4 : s ≤ n + 1) :
    rename (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) (lpMinor ℚ s h1 h2) =
      lpMinor ℚ s h3 h4 := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  rfl

theorem highest_weight_last_zero : HwLastZero := by
  intro n ν _ hl
  simp only [hw]
  rw [Fin.prod_univ_castSucc, map_prod]
  have hlast : nuNext ν (Fin.last n) = 0 := by simp [nuNext]
  rw [hlast, hl, Nat.sub_zero, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hs := s.isLt
  rw [map_pow, lpMinor_rename n ((s : ℕ) + 1) _ _ (by omega) (by omega)]
  congr 1
  simp only [nuNext, Fin.val_castSucc]
  rw [dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega)]
  by_cases h : (s : ℕ) + 1 < n
  · rw [dite_eq_left h]; rfl
  · rw [dite_eq_right h]
    have : (⟨s.val + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
    rw [this, hl]

theorem rename_isomorphism : RenameIso := by
  intro σ τ φ hφ f g
  classical
  unfold fockQ
  rw [support_rename_of_injective hφ, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hφ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain φ hφ, coeff_rename_mapDomain φ hφ]
  congr 2
  rw [Finsupp.mapDomain_support_of_injective hφ, Finset.prod_image (fun a _ b _ h => hφ h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hφ]

end PI.HookSteps
