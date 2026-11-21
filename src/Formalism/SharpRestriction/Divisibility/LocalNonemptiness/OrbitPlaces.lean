import Formalism.SharpRestriction.Divisibility.OrbitPlaces

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.OrbitPlaces

def ydOf (f : ℕ → ℕ) (hf : Antitone f) (N : ℕ) : YoungDiagram where
  cells := (Finset.range N).biUnion fun r => (Finset.range (f r)).image fun c => (r, c)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_biUnion, Finset.coe_range, Finset.coe_image, Set.mem_iUnion, Set.mem_image, Set.mem_Iio,
      exists_prop] at ha ⊢
    obtain ⟨r, hr, c, hc, rfl⟩ := ha
    have h1 : b.1 ≤ r := (Prod.le_def.1 hba).1
    have h2 : b.2 ≤ c := (Prod.le_def.1 hba).2
    exact ⟨b.1, lt_of_le_of_lt h1 hr, b.2, lt_of_le_of_lt h2 (lt_of_lt_of_le hc (hf h1)), rfl⟩




def NuIsPart (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ τ : D.what₂.Tau, ∃ f : ℕ → ℕ, Antitone f ∧
    ∀ r, ((f r : ℕ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) τ r else 0


section NuPart

variable (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau)

def nuE (a : ℕ) : ℚ := if h : a < D.R.m then (D.hc τ).e ⟨a, h⟩ else 0



def nuQ (i r : ℕ) : ℚ :=
  DV.srcPar D u τ r + nuE D τ i - (((D.R.N i : ℕ) : ℚ) + ((D.R.N (i + 1) : ℕ) : ℚ) - 1 - 2 * (r : ℚ)) / 2






theorem nu_last (hk : 0 < D.R.k) :
    ((D.R.t : ℚ) + 3) / 2 < (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ + nuE D τ 0 := by
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have h1 := (D.hcW u τ).u_last_gt hk hm
  have h2 := (D.hcW u τ).gap_be ⟨0, hm⟩
  have he : nuE D τ 0 = (D.hcW u τ).e ⟨0, hm⟩ := by
    unfold nuE
    rw [dif_pos hm, D.hcW_e u τ]
  rw [he]
  linarith






end NuPart




end Formalism.MainNotions.DIV.Inh

end
