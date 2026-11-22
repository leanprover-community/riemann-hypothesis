module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

@[expose] public section

noncomputable section
namespace GlobalTheory.LvT.LevModel
open Formalism.BasicNotions Classical

section Pairs

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

lemma mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

end Pairs

variable {D : D7} {u : D.what₂.Word}

end GlobalTheory.LvT.LevModel
