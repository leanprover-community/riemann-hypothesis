import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFoldRev
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom

section
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem coefficient_vector_commutation : CVComm := by
  intro k r Wp Wq _ _ _ _ _ _ s Y Y' F hF g hg
  have hs : ∀ (Z α : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)),
      Q.CV k r Z (α • f) = α • Q.CV k r Z f := fun Z => P5.tL_smulC 0 0 0 Z 0 0
  have hsm : Q.SmoothLev k r 0 Set.univ F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hF g₀ ((CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
    exact ⟨U, f', hU, hgU, hc, fun x hx hxl => he x hx ((CapelliUnderIntegral.glev0 x).1 hxl)⟩
  have hc := capelli_commutation _ k r 0 Set.univ F isOpen_univ hsm g
    ⟨(CapelliUnderIntegral.glev0 g).2 hg, trivial⟩ (Q.uC k r 0 Y) (Q.uC k r 0 Y')
  simp only [Pi.smul_apply, hs]
  exact congrArg (fun t => s • s • t) hc

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem energyReal_of_capAdj (hA : CapAdj) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_leaves hA capacity_theta_facts coefficient_vector_smoothness coefficient_vector_in_class coefficient_vector_support coefficient_vector_congr coefficient_vector_commutation
    beta_form_congr_holds

theorem energyReal_of_capAdjInt (hI : CapAdjInt) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_capAdj (capAdj_of_int hI)

end Formalism.FourierDecayAlt.P.CutMP.ER
end
