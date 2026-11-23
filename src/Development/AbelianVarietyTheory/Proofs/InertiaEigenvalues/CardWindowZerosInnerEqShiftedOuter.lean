module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.PMonE

open Finset

section WinInner

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def frobPerm : Equiv.Perm F := (frobeniusEquiv F p).toEquiv

theorem frobPerm_pow_apply (n : ℕ) (x : F) : (frobPerm (F := F) p ^ n) x = x ^ p ^ n := by
  rw [Equiv.Perm.coe_pow]
  have : (⇑(frobPerm (F := F) p)) = frobenius F p := by
    funext y; simp [frobPerm]
  rw [this, iterate_frobenius]

theorem pw_eq_zpow (k : ℤ) (x : F) : pw p k x = (frobPerm (F := F) p ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frobPerm_pow_apply]
    simp
  · push_neg at hk
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow]
    simp only [neg_neg, Int.toNat_natCast]
    rfl

theorem pw_pow (k : ℤ) (h : ℕ) (y : F) : pw p k (y ^ p ^ h) = pw p (k + h) y := by
  rw [pw_eq_zpow, pw_eq_zpow, ← frobPerm_pow_apply, ← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add]

theorem term_pow {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (r j : Fin h) (n : ℤ) :
    term p ϖ lam (fun i => x' i ^ p ^ h) r j n = ϖ * term p ϖ lam x' r j (n + 1) := by
  unfold term
  rw [pw_pow]
  have h1 : ((r : ℤ) + n * h + h) = (r : ℤ) + (n + 1) * h := by ring
  have h2 : ϖ ^ (-n) = ϖ * ϖ ^ (-(n + 1)) := by
    rw [show -n = -(n + 1) + 1 by ring, zpow_add_one₀ hϖ]; ring
  rw [h1, h2]; ring

theorem rowT_pow {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (K : ℕ) (hK : 1 ≤ K) (r : Fin h) :
    rowT p ϖ lam K (fun i => x' i ^ p ^ h) r = ϖ * rowS p ϖ lam (K - 1) (K + 1) x' r := by
  unfold rowT rowS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [term_pow p ϖ hϖ]
  rw [← Finset.mul_sum]
  congr 1
  have hI : Finset.Icc (-((K - 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ)
      = (Finset.Icc (-(K : ℤ)) (K : ℤ)).map (addRightEmbedding 1) := by
    rw [Finset.map_add_right_Icc]
    congr 1 <;> push_cast [hK] <;> ring
  rw [hI, Finset.sum_map]
  rfl

end WinInner

theorem win_inner : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F),
    ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F,
      Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} =
        Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  intro F _ p _ _ _ h K ϖ hϖ hK lam π
  let e : (Fin h → F) ≃ (Fin h → F) := Equiv.piCongrRight fun _ => frobPerm (F := F) p ^ h
  have he : ∀ x' : Fin h → F, e x' = fun i => x' i ^ p ^ h := by
    intro x'; funext i; simp [e, frobPerm_pow_apply]
  symm
  refine Nat.card_congr (e.subtypeEquiv fun x' => ?_)
  rw [he]
  have hq : p ^ h ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (h1 j) _
    · rw [rowT_pow p ϖ hϖ lam x' K hK, h2 r, mul_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · have := h1 j
      rw [norm_pow] at this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hq).1 this
    · have := h2 r
      rw [rowT_pow p ϖ hϖ lam x' K hK] at this
      exact (mul_eq_zero.1 this).resolve_left hϖ

end GlobalTheory.PMonE

end
