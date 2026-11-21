import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMovesResidue

theorem exists_sub_star_notMem : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q →
    ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  intro D Q _
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host Q.asIdeal Q.isMaximal
  refine ⟨θ, t, ?_, h2⟩
  change algebraMap (𝓞 D.host.E) D.host.E t = _
  rw [h1, Formalism.BasicNotions.Examples₂.star_eq_conj]

end GlobalTheory.ConjMovesResidue
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_sub_conj_notMem_self_conjugate_place : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q → ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  atlas_forward_decl GlobalTheory.ConjMovesResidue.exists_sub_star_notMem
