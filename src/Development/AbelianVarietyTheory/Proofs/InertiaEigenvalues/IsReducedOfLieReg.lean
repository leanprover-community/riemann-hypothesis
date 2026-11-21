import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable
import BuildAid.ForwardExisting

section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem InvAlg.isReduced_of_lieReg : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A :=
  fun _ B h => GlobalTheory.SepGen.isReduced B.g h.2

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_of_lieReg' : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A := by
  atlas_forward_decl GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg
