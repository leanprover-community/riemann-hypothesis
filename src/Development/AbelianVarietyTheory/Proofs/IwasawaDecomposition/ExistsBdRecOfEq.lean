import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelDataRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins

section
open Formalism.BasicNotions GlobalTheory.Mem.HD

theorem GlobalTheory.Mem.HD.levelTied_of_levEx : ∀ D : D7, LevEx D → Formalism.L2.Host.LevelTied D :=
  fun D h => ⟨fun p => by
    have hq : Formalism.MainNotions.q0Av D = Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D := rfl
    simpa [hq] using h p⟩
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem exists_bdRec_of_eq {D D' : D7} {O : Obj D} {O' : Obj D'} (h : (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨D', O'⟩)
    (R : Formalism.L2.RecT O'.ex) (c : ℝ) :
    ∃ b : BdRec D O c, (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), BdRec D O c) = ⟨D', O', R⟩ := by
  cases h
  exact ⟨R, rfl⟩

end GlobalTheory.Mem.Top.Bl
end
