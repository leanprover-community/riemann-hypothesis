import Mathlib
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

noncomputable section

namespace PI.QnZeroLevelWork

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  rcases Nat.lt_or_ge k.val p.val with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h), if_pos h]
    simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using h), if_neg (by omega)]
    simp

theorem skip_one_eq_succAbove {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : skip1 i j = i.succAbove j := by
  apply Fin.ext
  rw [val_succAbove]
  unfold skip1
  split_ifs <;> simp_all

theorem skip_two_succAbove_comp_alt {t : ℕ} (i : Fin (t + 2)) (i' : Fin (t + 1)) (j : Fin t) (hii : i.val ≤ i'.val) :
    skip2 i (i.succAbove i') j = i.succAbove (i'.succAbove j) := by
  have hv : (i.succAbove i').val = i'.val + 1 := by
    rw [val_succAbove]; split_ifs <;> omega
  apply Fin.ext
  rw [val_succAbove, val_succAbove]
  unfold skip2
  split_ifs <;> simp_all <;> omega

theorem skipSucc : SkipSucc := fun _ i j => skip_one_eq_succAbove i j

theorem skipSucc2 : SkipSucc2 := fun _ i i' j h => skip_two_succAbove_comp_alt i i' j h


theorem pair_sum {M : Type*} [AddCommMonoid M] {n : ℕ} (i : Fin (n + 2)) (G : Fin (n + 2) → M) :
    (∑ i' : Fin (n + 2), if i < i' then G i' else 0) =
      ∑ i'' : Fin (n + 1), if (i : ℕ) ≤ (i'' : ℕ) then G (i.succAbove i'') else 0 := by
  rw [Fin.sum_univ_succAbove _ i, if_neg (lt_irrefl i), zero_add]
  refine sum_congr rfl fun i'' _ => ?_
  have h : i < i.succAbove i'' ↔ (i : ℕ) ≤ (i'' : ℕ) := by
    rw [Fin.lt_def, val_succAbove]; split_ifs <;> omega
  simp only [h]

theorem quad_sum {M : Type*} [AddCommMonoid M] {n : ℕ}
    (T : Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → M) :
    (∑ i : Fin (n + 2), ∑ i' : Fin (n + 2), ∑ j : Fin (n + 2), ∑ j' : Fin (n + 2),
      if i < i' ∧ j < j' then T i i' j j' else 0) =
    ∑ i : Fin (n + 2), ∑ i'' : Fin (n + 1), ∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
      if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0 := by
  refine sum_congr rfl fun i _ => ?_
  have h1 : ∀ i' : Fin (n + 2), (∑ j : Fin (n + 2), ∑ j' : Fin (n + 2),
      if i < i' ∧ j < j' then T i i' j j' else 0) =
      if i < i' then ∑ j : Fin (n + 2), ∑ j' : Fin (n + 2), (if j < j' then T i i' j j' else 0) else 0 := by
    intro i'; by_cases h : i < i' <;> simp [h]
  have h2 : ∀ i'' : Fin (n + 1), (∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
      if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0) =
      if (i : ℕ) ≤ (i'' : ℕ) then ∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
        (if (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0) else 0 := by
    intro i''; by_cases h : (i : ℕ) ≤ (i'' : ℕ) <;> simp [h]
  simp only [h1, h2]
  rw [pair_sum i]
  refine sum_congr rfl fun i'' _ => ?_
  split_ifs
  · exact sum_congr rfl fun j _ => pair_sum j (fun j' => T i (i.succAbove i'') j j')
  · rfl

section Ops

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}


theorem comp1 (i : Fin (2 * r + k + 2)) :
    (posL (k + 1) r 0 ∘ skip1 i : Fin (2 * r + k + 2 - 1) → Fin (2 * r + (k + 1) + 1)) = i.succAbove := by
  funext j
  exact skip_one_eq_succAbove i j

theorem comp2 (i : Fin (2 * r + k + 2)) (i'' : Fin (2 * r + k + 1)) (h : (i : ℕ) ≤ (i'' : ℕ)) :
    (posL (k + 1) r 0 ∘ skip2 i (i.succAbove i'') : Fin (2 * r + k + 2 - 2) → Fin (2 * r + (k + 1) + 1)) =
      drop2 i i'' := by
  funext j
  exact skip_two_succAbove_comp_alt i i'' j h

def T1 (u : ℂ) (a β : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E) (g : Mx (k + 1) r)
    (i j : Fin (2 * r + k + 2)) : E :=
  ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * β g i * a g j) •
    qminorOp (EH (k + 1) r) (posL (k + 1) r 0 ∘ skip1 i) (posL (k + 1) r 0 ∘ skip1 j) u f g

def T2 (u : ℂ) (a a' β β' : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E)
    (g : Mx (k + 1) r) (i i' j j' : Fin (2 * r + k + 2)) : E :=
  ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β g i * β' g i' - β g i' * β' g i) *
    (a g j * a' g j' - a g j' * a' g j)) •
    qminorOp (EH (k + 1) r) (posL (k + 1) r 0 ∘ skip2 i i') (posL (k + 1) r 0 ∘ skip2 j j') u f g






end Ops



end PI.QnZeroLevelWork
