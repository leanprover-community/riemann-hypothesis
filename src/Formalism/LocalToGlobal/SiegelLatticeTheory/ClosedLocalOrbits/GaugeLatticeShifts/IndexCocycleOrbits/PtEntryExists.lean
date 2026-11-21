import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ

noncomputable section

namespace Formalism.L2.SG.Pf.IndexCocycleOrbits.CU

open Formalism.MainNotions.S Matrix

theorem ptEntry_symm {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (i j : ℕ), ptEntry bs i j = ptEntry bs j i
  | [], _, _ => rfl
  | (t, s) :: bs, i, j => by
    simp only [ptEntry]
    rw [ptEntry_symm bs (i - s) (j - s)]
    split_ifs <;> first | rfl | (exfalso; omega)




structure Mono {N : ℕ} {K : Type*} [Zero K] (P : Matrix (Fin N) (Fin N) K) : Prop where
  ex : ∀ i, ∃ j, P i j ≠ 0
  row : ∀ i j j', P i j ≠ 0 → P i j' ≠ 0 → j = j'
  col : ∀ i i' j, P i j ≠ 0 → P i' j ≠ 0 → i = i'


theorem mono_eq {K : Type*} [Field K] {N : ℕ} {P Q M V : Matrix (Fin N) (Fin N) K}
    (hP : Mono P) (hQ : Mono Q) (hM : IsLoUni M) (hV : IsUpUni V) (h : M * P = Q * V) : P = Q := by
  classical
  choose σ hσ using hP.ex
  choose τ hτ using hQ.ex
  have hPz : ∀ i j, j ≠ σ i → P i j = 0 := fun i j hj => by
    by_contra hne; exact hj (hP.row i j (σ i) hne (hσ i))
  have hQz : ∀ i j, j ≠ τ i → Q i j = 0 := fun i j hj => by
    by_contra hne; exact hj (hQ.row i j (τ i) hne (hτ i))
  have key : ∀ i, P i (σ i) = Q i (τ i) * V (τ i) (σ i) := by
    intro i
    have e := congrFun (congrFun h i) (σ i)
    simp only [Matrix.mul_apply] at e
    rw [Finset.sum_eq_single i, Finset.sum_eq_single (τ i)] at e
    · rw [(hM i i).2 rfl, one_mul] at e; exact e
    · intro k _ hk; rw [hQz i k hk, zero_mul]
    · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro k _ hk
      have : P k (σ i) = 0 := by
        by_contra hne; exact hk (hP.col k i (σ i) hne (hσ i))
      rw [this, mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  have hle : ∀ i, τ i ≤ σ i := by
    intro i
    by_contra hlt
    push Not at hlt
    have := key i
    rw [(hV (τ i) (σ i)).1 hlt, mul_zero] at this
    exact hσ i this
  have hσi : Function.Injective σ := fun a b hab => hP.col a b (σ a) (hσ a) (by rw [hab]; exact hσ b)
  have hτi : Function.Injective τ := fun a b hab => hQ.col a b (τ a) (hτ a) (by rw [hab]; exact hτ b)
  have h1 := Equiv.sum_comp (Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτi)) (fun j : Fin N => (j : ℕ))
  have h2 := Equiv.sum_comp (Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσi)) (fun j : Fin N => (j : ℕ))
  simp only [Equiv.ofBijective_apply] at h1 h2
  have hsum : ∑ i, ((τ i : Fin N) : ℕ) = ∑ i, ((σ i : Fin N) : ℕ) := by rw [h1, h2]
  have heq : ∀ i, τ i = σ i := by
    intro i
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => Fin.le_iff_val_le_val.mp (hle i))).1 hsum i
      (Finset.mem_univ _)
    exact Fin.ext this
  ext i j
  by_cases hj : j = σ i
  · subst hj
    rw [key i, heq i, (hV (σ i) (σ i)).2 rfl, mul_one]
  · rw [hPz i j hj, hQz i j (by rw [heq i]; exact hj)]

end Formalism.L2.SG.Pf.IndexCocycleOrbits.CU
