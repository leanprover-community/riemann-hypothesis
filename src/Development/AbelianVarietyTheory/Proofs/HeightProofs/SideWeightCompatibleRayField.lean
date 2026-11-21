import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WPtFrame
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumns
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightPsiChoiceTameStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightExportLevelStatement

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug

theorem tied_cfOf : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), Tied p.O.ex.errX (cfOf p).J (cfOf p).C := by
  intro hR 𝒮 hcs K p
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p.x.what₂.r.z.geo.fw.laws
  · exact hcs K p.B p.f p.T p.w p.Z p.x.Wt p.O.p0 p.x.what₂ p.x.rx
  · exact GlobalTheory.T.fieldTies_of_rayField_of_ksExact hR (p.w.st p.Z) p.f p.w.δ p.w.exact
  · show HalfAt (ofObj p.O).errX (Fr.at (p.w.st p.Z) p.f)
    rw [p.x.errX]
    exact GlobalTheory.T.conjGenerators_mem_framePrimes_trueColumns p.B p.f p.T p.w p.Z p.x.col.toColT

end GlobalTheory.Plug
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreFrameCompatible_constructed_point : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), Tied p.O.ex.errX (cfOf p).J (cfOf p).C := by
  atlas_forward_decl GlobalTheory.Plug.tied_cfOf
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PlugPt.sideW_ties : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), (sideW ν p).Ties p.O.ex.errX p.O.ex.xd := by
  intro hR hL 𝒮 ν hC K p
  obtain ⟨hRC, hTC, -⟩ := GlobalTheory.Plug.wPt_frame 𝒮 K p
  have ht := GlobalTheory.T.coreFrameCompatible_constructed_point hR 𝒮 hC K p
  obtain ⟨hpsi, hval, htame⟩ := GlobalTheory.T.side_weight_psi_choice_tame hL 𝒮 ν K p
  obtain ⟨hser, hlev, hdat, hsmall⟩ := GlobalTheory.T.side_weight_export_level hR hL 𝒮 ν K p
  refine ⟨?_, ?_, hser, hlev, hdat, hpsi, hval, hsmall, htame⟩
  · show p.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z
    rw [hRC, hTC]
  · show Tied p.O.ex.errX p.x.what₂.r.z.core (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z)
    rw [hTC]
    exact ht
end
