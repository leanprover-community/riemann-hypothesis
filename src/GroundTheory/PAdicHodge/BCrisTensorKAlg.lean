import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial TensorProduct

section Lifts

variable {R E : Type*} [Field R] [Field E]


end Lifts

section Disjoint

variable {K₀ C E : Type*} [Field K₀] [Field C] [Field E] [Algebra K₀ C] [Algebra K₀ E]
  (j : C →ₐ[K₀] E) (F : IntermediateField K₀ E) (M N : IntermediateField K₀ C)
  (L : Type*) [Field L] [Algebra K₀ L] [Algebra L C] [IsScalarTower K₀ L C]




end Disjoint

end GroundTheory.PAdicHodge
