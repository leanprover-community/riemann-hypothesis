import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import BuildAid.ForwardExisting

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SubQuotNe

theorem exists_mem_not_mem_of_subQuot_equiv :
    ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ),
      Nonempty ((subQuot S T).Equiv σ) → Nontrivial X →
        ∃ s ∈ S.toSubmodule, s ∉ T.toSubmodule := by
  intro M W X _ _ _ _ _ ρ σ S T hE hX
  obtain ⟨e⟩ := hE
  by_contra h
  push_neg at h
  have hle : S.toSubmodule ≤ T.toSubmodule := fun s hs => h s hs
  haveI : Subsingleton (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
    Submodule.Quotient.subsingleton_iff.mpr (Submodule.comap_subtype_eq_top.mpr hle)
  exact not_subsingleton X e.toLinearEquiv.symm.injective.subsingleton

end GlobalTheory.CompanionTheory.SubQuotNe
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_nontrivial_exists_mem : ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ), Nonempty ((subQuot S T).Equiv σ) → Nontrivial X → ∃ s ∈ S.toSubmodule, s ∉ T.toSubmodule := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv
