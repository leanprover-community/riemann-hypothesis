import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPtrueHom

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Pos

variable {n' : ℕ} [NeZero n']

theorem posOf_val (x : ℤ) : ((posOf n' x).val : ℤ) = x % n' := by
  have h0 : (0:ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have h1 := Int.emod_nonneg x h0.ne'
  have h2 := Int.emod_lt_of_pos x h0
  simp only [posOf]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega



end Pos

theorem sum_ite_le {α : Type} (s : Finset α) (c : α → Prop) [DecidablePred c] (f : α → ℕ) (M n : ℕ)
    (hf : ∀ x ∈ s, c x → f x ≤ M) (hc : (s.filter c).card ≤ n) : ∑ x ∈ s, (if c x then f x else 0) ≤ n * M := by
  rw [← Finset.sum_filter]
  calc ∑ x ∈ s.filter c, f x ≤ ∑ _x ∈ s.filter c, M :=
        Finset.sum_le_sum (fun x hx => by
          rw [Finset.mem_filter] at hx
          exact hf x hx.1 hx.2)
    _ = (s.filter c).card * M := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * M := Nat.mul_le_mul_right _ hc

section Fr

variable {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ}

private theorem fr_lt_fr_of_lt (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l < l') (hl' : l' < r) :
    F.fr j l < F.fr j l' := by
  obtain ⟨-, -, hinc, -⟩ := hV
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hll
  induction m with
  | zero => exact hinc j l (by omega)
  | succ m ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hinc j (l + m + 1) (by omega)
    show F.fr j l < F.fr j (l + m + 1 + 1)
    exact lt_trans h1 h2

private theorem fr_le_fr_of_le (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l ≤ l') (hl' : l' < r) :
    F.fr j l ≤ F.fr j l' := by
  rcases Nat.lt_or_eq_of_le hll with h | rfl
  · exact le_of_lt (fr_lt_fr_of_lt hV j h hl')
  · exact le_rfl


theorem fr_le_last (hV : F.Valid L₁ N₁) (j : ℤ) {l : ℕ} (hl : l < r) : F.fr j l ≤ F.fr j (r - 1) := by
  exact fr_le_fr_of_le hV j (by omega) (by omega)




end Fr

end Formalism.MainNotions.Pf14
