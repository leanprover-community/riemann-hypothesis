module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions MeasureTheory
open scoped InnerProductSpace ComplexOrder nonZeroDivisors NumberField

section S1bNum

variable (D : D7)

def plEmb (v : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb (D.eTau v).1

def rhoReal (i s : ℕ) : ℝ := D.host.rdE ^ (-((((2 * D.R.rS + 3 : ℕ) : ℤ) - 2 * (i : ℤ) - (s : ℤ))))

def locBlocksFrom (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) : ℕ → List (D.host.E × ℕ) → List (ℂ × ℕ)
  | _, [] => []
  | a, (t, s) :: bs => (((ρ (a + 1) s : ℝ) : ℂ) * plEmb D v t, s) :: locBlocksFrom ρ v (a + s) bs

def locBlocks (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) (bs : List (D.host.E × ℕ)) : List (ℂ × ℕ) :=
  locBlocksFrom D ρ v 0 bs

theorem locBlocksFrom_snd (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) (bs : List (D.host.E × ℕ)) :
    ∀ a, (locBlocksFrom D ρ v a bs).map Prod.snd = bs.map Prod.snd := by
  induction bs with
  | nil => intro a; rfl
  | cons b bs ih => intro a; obtain ⟨t, s⟩ := b; simp [locBlocksFrom, ih]

theorem locBlocksFrom_ok (ρ : ℕ → ℕ → ℝ) (hρ : ∀ i s, ρ i s ≠ 0) (v : D.what₂.Tau) (bs : List (D.host.E × ℕ)) :
    ∀ a, (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ p ∈ locBlocksFrom D ρ v a bs, p.1 ≠ 0 ∧ 1 ≤ p.2 := by
  induction bs with
  | nil => intro a _ p hp; simp [locBlocksFrom] at hp
  | cons b bs ih =>
    intro a h p hp
    obtain ⟨t, s⟩ := b
    simp only [locBlocksFrom, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have hb := h (t, s) (by simp)
      exact ⟨mul_ne_zero (by exact_mod_cast hρ (a + 1) s) ((map_ne_zero (plEmb D v)).2 hb.1), hb.2⟩
    · exact ih (a + s) (fun b hb => h b (by simp [hb])) p hp

def ptLocS (ρ : ℕ → ℕ → ℝ) (hρ : ∀ i s, ρ i s ≠ 0) (v : D.what₂.Tau) {i : ℕ} (γ : Point D.host.E i) : Point ℂ i :=
  ⟨locBlocks D ρ v γ.1, locBlocksFrom_ok D ρ hρ v γ.1 0 γ.2.1, by
    rw [locBlocks, locBlocksFrom_snd]; exact γ.2.2⟩

theorem rdE_pos : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)

theorem rhoReal_ne (i s : ℕ) : rhoReal D i s ≠ 0 := zpow_ne_zero _ (rdE_pos D).ne'

theorem rhoReal_pos (i s : ℕ) : 0 < rhoReal D i s := zpow_pos (rdE_pos D) _

def ptWeightG (ρ : ℕ → ℕ → ℝ) (T T' : ℝ) (bs : List (D.host.E × ℕ)) : ℝ :=
  ∏ v, ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D ρ v bs)

end S1bNum

section Kernels

end Kernels

section S1bData

variable (D : D7)

end S1bData

section Sizes

variable (D : D7)

end Sizes

section Rows

end Rows

end Formalism.MainNotions.S
