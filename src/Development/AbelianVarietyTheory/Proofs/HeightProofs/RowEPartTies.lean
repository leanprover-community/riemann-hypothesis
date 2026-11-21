import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RowETiesB
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreTiesOfTied
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfSizeFreeConditions

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_constructedPoint_hostSize_numerical : EvP fun _ K => ∀ β : BPt K, GlobalTheory.FieldSize.HostSz β.D.host β.O.L.sc.L ∧ ∀ C, FieldTies β.D C → NumAtL β.O.L K.s.x := by
  first | exact @GlobalTheory.Plug.eventually_hostSize_and_numAt | exact GlobalTheory.Plug.eventually_hostSize_and_numAt | (intros; apply GlobalTheory.Plug.eventually_hostSize_and_numAt <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem more_of_tiesB : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c),
    TiesB D O c b → FieldSmall D O.L → SingleIndexPlacesAreTwisted b → More b := by
  intro D O c b hT hS hW
  obtain ⟨hs, hr⟩ := hT
  refine ⟨hW, ?_, ?_⟩
  · exact GlobalTheory.Plug.coreTies_of_tied D _ _ _ _ O.L O.ex.errX b.T (R2 b) b.P.A3.A.μ0 hs.tied b.charW.base.lev hS
  · exact ⟨hs.series, hs.level, hs.data, hs.psi, hs.psiVal, hs.small, hs.types, hr⟩

end GlobalTheory.PlugPt
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem rowE_part_ties : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (Bd := Ind.Part) (sAnd Q RayPosition) (linkOf fun K p c b => pinPt ν K p c b.pt)
      fun _ D O c b => TiesB D O c b.pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ More b.pt := by
  intro hR hL 𝒮 ν Q hC
  refine (EvP.and (rowE_tiesB hR hL 𝒮 ν Q hC) GlobalTheory.T.eventually_constructedPoint_hostSize_numerical).mono ?_
  intro κ K _ H β hq c b hl
  obtain ⟨p, b', hpin, heq⟩ := hl
  have hl' : linkOf (pinPt ν) K β c b.pt :=
    ⟨p, b'.pt, hpin, congrArg (fun y : (Σ (D : D7) (O : Obj D), Ind.Part D O c) =>
      (⟨y.1, y.2.1, y.2.2.pt⟩ : Σ (D : D7) (O : Obj D), BdPt D O c)) heq⟩
  have ht : TiesB β.D β.O c b.pt := H.1 β hq c b.pt hl'
  have hs : FieldSmall β.D β.O.L := ((H.2 β).2 _ ht.1.tied.field).2.2
  have hw : SingleIndexPlacesAreTwisted b.pt := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
  exact ⟨ht, ⟨hs, (GlobalTheory.T.pathCoreConditions_of_intrinsicConditions β.D β.O c b.pt ht hs).2.2.1⟩, GlobalTheory.PlugPt.more_of_tiesB β.D β.O c b.pt ht hs hw⟩

end GlobalTheory.PlugPt
end
