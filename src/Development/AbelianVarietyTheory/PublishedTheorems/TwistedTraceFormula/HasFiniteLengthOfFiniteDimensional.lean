import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.FinitenessModel

theorem padic (h : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (p : ℕ) [Fact p.Prime] :
    IrreducibleAdmissible ℚ_[p] :=
  haveI := GlobalTheory.SplitWeil.Model.padic_localField p
  (h ℚ_[p]).1


theorem hasFiniteLength_of_finiteDimensional {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ G V) : HasFiniteLength π := by
  let φ : Subrepresentation π ↪o Submodule ℂ V :=
    ⟨⟨Subrepresentation.toSubmodule, Subrepresentation.toSubmodule_injective⟩, Iff.rfl⟩
  exact (hasFiniteLength_iff_wellFounded π).2 ⟨φ.wellFoundedGT, φ.wellFoundedLT⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]



end GlobalTheory.SmGL.FinitenessModel
