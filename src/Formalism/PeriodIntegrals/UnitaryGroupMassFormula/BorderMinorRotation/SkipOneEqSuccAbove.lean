import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.Development

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmBorderFull

open PI

theorem val_succAbove {t : ℕ} (p : Fin (t + 1)) (i : Fin t) :
    ((p.succAbove i : Fin (t + 1)) : ℕ) = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos h]
    first
    | exact congrArg Fin.val (Fin.succAbove_of_castSucc_lt p i h)
    | (rw [Fin.succAbove_of_castSucc_lt p i (by simpa [Fin.lt_iff_val_lt_val] using h)]; simp)
  · rw [if_neg h]
    first
    | exact congrArg Fin.val (Fin.succAbove_of_le_castSucc p i (Nat.not_lt.mp h))
    | (rw [Fin.succAbove_of_le_castSucc p i (by simp [Fin.le_iff_val_le_val]; omega)]; simp)

theorem skip_one_eq_succAbove {t : ℕ} (p : Fin (t + 1)) (i : Fin t) : skip1 p i = p.succAbove i := by
  apply Fin.ext
  rw [val_succAbove]
  unfold skip1
  split_ifs with h1 h2 <;> first | rfl | (exact absurd h1 h2) | (exact absurd h2 h1) | omega


theorem bS_castSucc {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es ∘ Fin.castSucc = v := by
  funext i
  first | simp [bS] | (simp only [Function.comp_apply, bS, Fin.snoc_castSucc])

theorem bS_last {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es (Fin.last m) = es := by
  first | simp [bS] | (simp only [bS, Fin.snoc_last])

theorem rot_cons {n k : ℕ} (e : Fin n) (W : Fin k → Fin n) :
    bE e W = Fin.snoc (α := fun _ => Fin n) W e ∘ (finRotate (k + 1)).symm := by
  first
  | (rw [Fin.snoc_eq_cons_rotate]; funext i; simp [bE])
  | (funext i; obtain ⟨j, rfl⟩ := (finRotate (k + 1)).surjective i; simp only [Function.comp_apply, Equiv.symm_apply_apply, bE]; induction j using Fin.lastCases <;> simp [finRotate_last, finRotate_succ_apply])

theorem rowE (hLR : ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n k : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (e : Fin n) (W : Fin k → Fin n) (v : Fin (k + 1) → Fin n) (he : ∀ x, v x ≠ e) (u : ℂ) :
    qminor E (bE e W) v u =
      ∑ x : Fin (k + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) * (qminor E W (v ∘ x.succAbove) (u - 1) * E e (v x)) := by
  have hperm : ∀ (a : Fin (k + 1) → Fin n) (τ : Equiv.Perm (Fin (k + 1))),
      qminor E (a ∘ τ) v u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a v u := by
    intro a τ
    unfold qminor
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
    have hτ : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.Perm.sign_mul,
      Units.val_mul, Int.cast_mul]
    rw [← mul_assoc, ← mul_assoc, hτ, one_mul]
  have hs : ∀ x : Fin (k + 1), ((Equiv.Perm.sign (finRotate (k + 1)).symm : ℤ) : A) *
      (((-1 : ℤ) ^ (k + (x : ℕ)) : ℤ) : A) = (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) := by
    intro x
    rw [Equiv.Perm.sign_symm, sign_finRotate, ← Int.cast_mul, Units.val_pow_eq_pow_val, Units.val_neg,
      Units.val_one, ← pow_add]
    congr 1
    have hx : ∀ a : ℕ, a = 2 * k + (x : ℕ) → (-1 : ℤ) ^ a = (-1) ^ (x : ℕ) := by
      rintro a rfl
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    exact hx _ (by omega)
  rw [rot_cons e W, hperm, hLR A n k E hE (Fin.snoc (α := fun _ => Fin n) W e) v u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 : (Fin.snoc (α := fun _ => Fin n) W e ∘ Fin.castSucc) = W := by
    funext i
    simp
  have h2 : Tm E u e (v x) = E e (v x) := by
    unfold Tm
    rw [if_neg (fun h => he x h.symm), zero_add]
  rw [← mul_assoc, hs x, h1, Fin.snoc_last, h2]



theorem rows_succ {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1))
    (h : k + 1 = k + 1 - 1 + 1) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ Fin.succ =
      Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast h := by
  funext j
  simp only [Function.comp_apply]
  have hw := w.isLt
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have h1 : (w.castSucc.succ).succAbove (Fin.last k).succ = (Fin.last (k + 1)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
    rw [h1]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_last, Fin.cast_last]
  · have hj := j.isLt
    have h2 : (w.castSucc.succ).succAbove (Fin.castSucc j).succ = (Fin.castSucc (w.succAbove j)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc]; split_ifs <;> omega)
    have h3 : Fin.cast h (Fin.castSucc j) = Fin.castSucc (Fin.cast (by omega) j : Fin (k + 1 - 1)) :=
      Fin.ext (by simp only [Fin.coe_cast, Fin.coe_castSucc])
    rw [h2, h3]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_castSucc, Function.comp_apply]
    rw [skip_one_eq_succAbove]
    rfl


theorem cmul {A : Type*} [Ring A] (s : ℤ) (x y : A) : x * ((s : A) * y) = (s : A) * (x * y) := by
  rw [← mul_assoc, ← mul_assoc, Int.cast_comm]


end PI.UnitaryGroupMassFormula.QmBorderFull
