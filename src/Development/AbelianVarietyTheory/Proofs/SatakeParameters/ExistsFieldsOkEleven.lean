import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfCore

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.GO.EighthRoots

section Quartic

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (σ : E ≃ₐ[ℚ] E)

@[reducible] def quarticFields : Fields where
  F := maximalRealSubfield E
  E := E
  K := E
  starE := IsCMField.starRing E
  starK := IsCMField.starRing E
  Tau := Bool
  emb := fun b => if b then (σ : E →+* E) else RingHom.id E

def conj : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ

theorem conj_conj (x : E) : conj E (conj E x) = x := IsCMField.complexConj_apply_apply E x

theorem conj_ne_one : conj E ≠ 1 := fun h =>
  IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)

theorem mem_Kq (x : E) : x ∈ (quarticFields E σ).Kq ↔ σ x = x := by
  constructor
  · intro h
    exact h true false
  · intro h a b
    cases a <;> cases b
    · rfl
    · exact h.symm
    · exact h
    · rfl


end Quartic







end GlobalTheory.GO.EighthRoots
