import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzRapidDecayColumn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothKernelRepresentation

section
open Classical MeasureTheory NumberField

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

theorem mspan_le_rspan : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  intro E _ _ _ a π
  refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF f hf => ?_,
    fun F hF r f => ?_⟩
  · obtain ⟨hk, he⟩ := GlobalTheory.T.archimedean_smooth_kernel_representation f hf
    rw [he F]
    exact kerInf_mem_rspan hF _ hk
  · have e : colConv r f F = kerInf (volume : Measure (Fin a → Cinf E)) (fun x => f x) (colU r) F := rfl
    rw [e]
    exact kerInf_mem_rspan hF _ (GlobalTheory.T.schwartz_rapid_decay_column r f)

end GlobalTheory.JSW
end

open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_span_le_rapid_span : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  atlas_forward_decl GlobalTheory.JSW.mspan_le_rspan
