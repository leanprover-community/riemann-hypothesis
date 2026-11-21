import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section gram

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem blockPSD_congr {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) (a a' : α → α → ℂ) (w w' : α → β → ℂ)
    (b b' : β → β → ℂ) (ha : ∀ p ∈ Y₁, ∀ q ∈ Y₁, a p q = a' p q) (hw : ∀ p ∈ Y₁, ∀ q ∈ Y₂, w p q = w' p q)
    (hb : ∀ p ∈ Y₂, ∀ q ∈ Y₂, b p q = b' p q) (h : KB.BlockPSD Y₁ Y₂ a w b) : KB.BlockPSD Y₁ Y₂ a' w' b' := by
  unfold KB.BlockPSD TB.PSDOn at *
  convert h using 1
  ext ⟨x, hx⟩ ⟨y, hy⟩
  rcases x with p | p <;> rcases y with q | q <;>
    simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at hx hy <;> simp [*]


end gram

end

end Formalism.FourierDecayAlt.P.PBK
