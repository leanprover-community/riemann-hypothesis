import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsRowPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsTiedS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
import Formalism.LocalToGlobal.ClassSLinks
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure RowPinMinAlt (T : _root_.Formalism.L2.TiedDataSKAlt ex) : Prop where
  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)
  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), _root_.Formalism.L2.Rows.LowerMapTieTwAlt T u μ hμ h1
  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂
end Formalism.L2.Rows
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
theorem gTiedF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : G.GroupCompatibilityFamily Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i hx1 => ?_⟩
  obtain ⟨T⟩ := hx0 x hx1 ((le_max_left _ _).trans hx) i
  exact ⟨T.g⟩
end Formalism.L2
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure RecTAlt (ex : Extra D L hT Gi Gl K Y cX) where
  T : _root_.Formalism.L2.TiedDataSKAlt ex
  pin : _root_.Formalism.L2.Rows.RowPinMinAlt T
  joints : _root_.Formalism.L2.JointsSAlt T.toTiedDataS
  host : _root_.Formalism.L2.HostDatumSelfDual T.toTiedDataS
  weq : Theta.WeilCompatibleEquivariance T.toTiedDataS.theta.W
def ExtraDataRecursive (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (_root_.Formalism.L2.RecTAlt ex)
theorem ExtraDataRecursive.tiedSK {ex : Extra D L hT Gi Gl K Y cX} (h : _root_.Formalism.L2.ExtraDataRecursive ex) : _root_.Formalism.L2.ExtraDataSelfDualKernel ex :=
  let ⟨R⟩ := h; ⟨R.T⟩
end
def SecondLayerFamilyClass : FamClass := fun {_} Fm =>
  (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataRecursive (Fm.ex x hx i)) ∧ _root_.Formalism.L2.LinkedFamiliesAligned' Fm
theorem SecondLayerFamilyClass.c2sk {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : _root_.Formalism.L2.LinkedFamiliesKernelFrame' Fm := by
  obtain ⟨⟨x0, h⟩, _⟩ := h
  exact ⟨x0, fun x hx hx0 i => (h x hx hx0 i).tiedSK⟩
theorem SecondLayerFamilyClass.c2s {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : _root_.Formalism.L2.SecondChernLinkedClass Fm := h.c2sk.c2s
theorem group_compatibility_of_second_layer_family {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondLayerFamilyClass Fm) : G.GroupCompatibilityFamily Fm := _root_.Formalism.L2.gTiedF_of_C2S_alt Fm h.c2s
end Formalism.L2
end
end
end
