import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstantOneNotCuspidalOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRecordOfLocStage

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil GlobalTheory.Cusp.Model GlobalTheory.CuspDecay.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspSpectrum.Model

theorem exists_measure (D : D7) (V : HSp D) :
    ∃ μ : Measure (GA D V), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  ⟨Measure.haar, inferInstance, AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ inferInstance⟩

theorem exists_ne_zero : ∃ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (_ : μ.IsHaarMeasure)
    (_ : μ.IsMulRightInvariant), V.rank = 1 ∧ ∃ f ∈ CcGA V, RcuspOp V μ f ≠ 0 := by
  obtain ⟨D⟩ := Mem.nonempty_record_of_locStage
  obtain ⟨μ, _, _⟩ := exists_measure D (line D)
  obtain ⟨v, hv, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (L2cusp_ne_bot μ (wittIndex_line D))
  obtain ⟨f, hf, h⟩ := exists_RcuspOp_ne_zero (v := ⟨v, hv⟩) fun e => h0 (congrArg Subtype.val e)
  exact ⟨D, line D, μ, ‹_›, ‹_›, rfl, f, hf, fun e => h (by rw [e]; rfl)⟩

theorem exists_isotropic : ∃ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (_ : μ.IsHaarMeasure)
    (_ : μ.IsMulRightInvariant), wittIndex V = 1 ∧ L2cusp V μ ≠ ⊤ ∧ ∃ f ∈ CcGA V, f 1 = 1 := by
  obtain ⟨D⟩ := Mem.nonempty_record_of_locStage
  obtain ⟨μ, _, _⟩ := exists_measure D (plane D)
  obtain ⟨φ, hφ, -, h1, -⟩ := exists_bump_ccAd (J := (plane D).gram) (isCMExt_host D) univ_mem
  exact ⟨D, plane D, μ, ‹_›, ‹_›, wittIndex_plane D, L2cusp_plane_ne_top μ, _, hφ, by simp [h1]⟩

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]



end GlobalTheory.CuspSpectrum.Model

end
