import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralStmt

noncomputable section

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

section aux

variable {F : Type} [CommRing F] {k : ℕ}

def StrictUp (d : ℕ) (A : Matrix (Fin k) (Fin k) F) : Prop :=
  ∀ i j : Fin k, j.val < i.val + d → A i j = 0

theorem strictUp_mul {d : ℕ} {A B : Matrix (Fin k) (Fin k) F} (hA : StrictUp d A)
    (hB : StrictUp 1 B) : StrictUp (d + 1) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < i.val + d
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (by omega), mul_zero]

theorem strictUp_pow {A : Matrix (Fin k) (Fin k) F} (hA : StrictUp 1 A) (d : ℕ) :
    StrictUp d (A ^ d) := by
  induction d with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    intro h
    subst h
    omega
  | succ d ih =>
    rw [pow_succ]
    exact strictUp_mul ih hA

theorem strictUp_pow_eq_zero {A : Matrix (Fin k) (Fin k) F} (hA : StrictUp 1 A) {d : ℕ}
    (hd : k ≤ d) : A ^ d = 0 := by
  ext i j
  exact strictUp_pow hA d i j (by have := j.isLt; omega)

theorem isUnitri_one : IsUnitri (1 : Matrix (Fin k) (Fin k) F) :=
  ⟨fun _ _ hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem isUnitri_mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) (hB : IsUnitri B) :
    IsUnitri (A * B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l < i
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hij (not_lt.mp hl)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.1 i l h, zero_mul]
      · rw [hB.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem isUnitri_pow {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) (d : ℕ) :
    IsUnitri (A ^ d) := by
  induction d with
  | zero => rw [pow_zero]; exact isUnitri_one
  | succ d ih => rw [pow_succ]; exact isUnitri_mul ih hA

theorem strictUp_sub_one {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) :
    StrictUp 1 (A - 1) := by
  intro i j hij
  rw [Matrix.sub_apply]
  rcases Nat.lt_or_ge j.val i.val with h | h
  · have h' : j < i := h
    rw [hA.1 i j h', Matrix.one_apply_ne (ne_of_gt h'), sub_zero]
  · have h' : i = j := Fin.ext (by omega)
    subst h'
    rw [hA.2 i, Matrix.one_apply_eq, sub_self]

theorem isUnitri_pow_char (g : ℕ) [Fact g.Prime] [CharP F g] [Nontrivial F]
    {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) : A ^ (g ^ k) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Subsingleton.elim _ _
  · have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have h1 : (A - 1) ^ (g ^ k) = A ^ (g ^ k) - 1 ^ (g ^ k) :=
      sub_pow_char_pow_of_commute (h := Commute.one_right A) ..
    have h2 : (A - 1) ^ (g ^ k) = 0 :=
      strictUp_pow_eq_zero (strictUp_sub_one hA)
        (le_of_lt (Nat.lt_pow_self (Fact.out : g.Prime).one_lt))
    rw [h2, one_pow] at h1
    exact (sub_eq_zero.mp h1.symm)

end aux


end Formalism.MainNotions.Gaps.MI
