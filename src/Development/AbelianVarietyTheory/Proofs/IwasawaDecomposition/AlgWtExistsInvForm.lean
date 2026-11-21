import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightFormStatement
import BuildAid.ForwardExisting

section
open NumberField

namespace GlobalTheory

theorem algWt_exists_invForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  intro L _ _ _ n a
  exact GlobalTheory.T.exists_invariant_hermitian_weight_form L n a

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algWt_exists_invForm' : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  atlas_forward_decl GlobalTheory.algWt_exists_invForm
