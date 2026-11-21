import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.BrExistsSqInv
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs

section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (jL)

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

def jI (d : ℕ) (𝔞 : Ideal (𝓞 (KQ d))) : ℂ := jL (latI (algebraMap (KQ d) ℂ) 𝔞 1)

def JSet (d : ℕ) : Set ℂ := {y | ∃ 𝔟 : Ideal (𝓞 (KQ d)), 𝔟 ≠ ⊥ ∧ y = jI d 𝔟}

def ConjKQ (d : ℕ) : Prop :=
  ∀ cc : Ideal (𝓞 (KQ d)), cc ≠ ⊥ → ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (h : jI d cc ∈ M),
    (∀ ρ : M →ₐ[ℚ] ℂ, ∃ 𝔟 : Ideal (𝓞 (KQ d)), 𝔟 ≠ ⊥ ∧ ρ ⟨jI d cc, h⟩ = jI d 𝔟) ∧
    ∀ 𝔟 : Ideal (𝓞 (KQ d)), 𝔟 ≠ ⊥ →
      ((Finset.univ.filter fun ρ : M →ₐ[ℚ] ℂ => ρ ⟨jI d cc, h⟩ = jI d 𝔟).card : ℝ) *
        (Fintype.card (ClassGroup (𝓞 (KQ d))) : ℝ) = (Module.finrank ℚ M : ℝ)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

end
end

section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (jL)

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

open Formalism.BasicNotions (D7)

theorem conjSet_of_F (hF : CMConjSetF) (D : D7) : CMConjSet D :=
  hF D.host.K D.host.d (discriminant_mod_four D) _ (br_sqrt_sq D) (br_finrank_K D) (brPhi D)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

end
end

section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (jL)

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

open Formalism.BasicNotions (D7)

theorem cmConjSetF_proved [h : Fact CMConjSetF] : CMConjSetF := h.out

theorem cmConjSet_holds [h : Fact CMConjSetF] (D : D7) : CMConjSet D := conjSet_of_F h.out D

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ComplexMultiplicationLFunction

end
end
