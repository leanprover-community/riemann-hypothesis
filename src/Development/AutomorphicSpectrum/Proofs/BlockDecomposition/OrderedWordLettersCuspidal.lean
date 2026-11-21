import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import BuildAid.ForwardExisting

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcWords

theorem wtW_isCusp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k) :
    ∀ c ∈ wtW Δ, c.IsCusp := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hl
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hcl
  exact Segment.isCusp_term _ _

end GlobalTheory.CompanionTheory.ZcWords
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_word_letters_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k), ∀ c ∈ wtW Δ, c.IsCusp := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp
