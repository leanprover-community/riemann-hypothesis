import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
import BuildAid.ForwardExisting

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem isLimit_leftFunc_arrCone (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (hc : IsColimit (ringCocone K Ω)) :
    Nonempty (IsLimit (Arrow.leftFunc.mapCone (arrCone K Ω))) :=
  ⟨isLimitOfPreserves (Scheme.Spec ⋙ yoneda) hc.op⟩

end GlobalTheory.SepCech
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω], IsColimit (GlobalTheory.SepCech.ringCocone K Ω) → Nonempty (IsLimit (Arrow.leftFunc.mapCone (GlobalTheory.SepCech.arrCone K Ω))) := by
  atlas_forward_decl GlobalTheory.SepCech.isLimit_leftFunc_arrCone
