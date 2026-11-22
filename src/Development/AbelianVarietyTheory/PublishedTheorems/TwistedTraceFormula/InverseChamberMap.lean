module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.Chamber

variable {k : ℕ}

abbrev SV (k : ℕ) : Type := Fin k → SignType

def Below (u u' : SV k) : Prop := ∀ i, u i ≠ 0 → u' i = u i

def IsPar (P : Finset (SV k)) : Prop := 0 ∉ P ∧ ∀ u ∈ P, ∀ u' ∈ P, Below u u' ∨ Below u' u

def stdVec (j : Fin k) : SV k := fun i => if i ≤ j then 1 else 0

def stdPar (J : Finset (Fin k)) : Finset (SV k) := J.image stdVec

theorem isPar_stdPar (J : Finset (Fin k)) : IsPar (stdPar J) := by
  refine ⟨fun h => ?_, fun u hu u' hu' => ?_⟩
  · obtain ⟨j, -, e⟩ := mem_image.1 h
    simpa [stdVec] using congrFun e j
  · obtain ⟨j, -, rfl⟩ := mem_image.1 hu
    obtain ⟨j', -, rfl⟩ := mem_image.1 hu'
    have key : ∀ a b : Fin k, a ≤ b → Below (stdVec a) (stdVec b) := fun a b h i hi => by
      have : i ≤ a := by by_contra e; exact hi (if_neg e)
      simp [stdVec, this, this.trans h]
    exact (le_total j j').imp (key _ _) (key _ _)

end GlobalTheory.Chamber

end
