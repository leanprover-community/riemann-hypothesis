import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import BuildAid.ForwardExisting

section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.UnipInv

theorem Eop_unip_left :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) →
      ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a),
        (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  intro E _ _ _ a r f hf τ i j x g
  have hc : chart f.1 (unip x * g) = chart f.1 g := by
    funext y
    unfold chart
    split_ifs
    · rw [mul_assoc, hf]
    · rfl
  have hD : ∀ X, lieD X f.1 (unip x * g) = lieD X f.1 g := fun X => by
    simp only [lieD, hc]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
    Pi.smul_apply, Pi.sub_apply, lieS_apply, lie_apply, hD]

end GlobalTheory.CuspRep.UnipInv
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eop_preserves_left_unipotent_invariance : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a), (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  atlas_forward_decl GlobalTheory.CuspRep.UnipInv.Eop_unip_left
