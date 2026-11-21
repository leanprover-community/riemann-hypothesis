import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantForms
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTarget
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTieEntire
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberFormsStableOfReferenceTuple

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical

namespace GlobalTheory.KFiClose

theorem kFi_of_tie : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  intro D L hT Gi Gl K Y cX ex t hC hF
  have second : ∀ u μ, DV.Used D μ → ∀ i < D.R.m, ∀ φ ∈ (ex.tw.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (ex.tw.fm u μ).Fi (i + 1) := by
    intro u μ hμ
    obtain ⟨G, hFA, hSP⟩ := hF u μ hμ
    exact GlobalTheory.T.kernelOperator_maps_stabiliserEquivariant_forms D u (D.chTw u μ) _ _ (ex.tw.fm u μ) (t.O u μ) G hFA (t.unf u μ)
      (fun i hi c c' => GlobalTheory.KerTieEntire.kerTie_entire D L hT Gi Gl K Y cX ex t u μ i hi c c')
      (GlobalTheory.T.classSum_term_law_stabiliser_target D L hT Gi Gl K Y cX ex t hC u μ G hSP)
  have h0 : DV.Used D D.what₂.mu0 := by
    unfold DV.Used
    exact Or.inl rfl
  exact ⟨fun u i hi => GlobalTheory.KFiMu0.memberForms_stable_of_reference_tuple D ex.tw u i hi (second u _ h0 i hi), second⟩

end GlobalTheory.KFiClose
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelClassSums_carry_chainComplexForms : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  atlas_forward_decl GlobalTheory.KFiClose.kFi_of_tie
