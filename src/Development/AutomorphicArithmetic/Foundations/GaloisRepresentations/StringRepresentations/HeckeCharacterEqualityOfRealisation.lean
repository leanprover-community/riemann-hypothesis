module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified

@[expose] public section

noncomputable section

namespace UpperTheory.GalN

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem unr_part {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {w : PlE H} :
    ∀ L : List (Part A.CG), A.unr (isoLoc N A L w) → ∀ p ∈ L, 1 ≤ p.d → A.unr (A.locG p.π w) := by
  intro L
  induction L with
  | nil =>
    intro _ _ hp _
    exact absurd hp List.not_mem_nil
  | cons q L ih =>
    intro hun p hp hd
    have h12 := (A.unr_sum (spehLoc N A q w) (isoLoc N A L w)).1 hun
    rcases List.mem_cons.1 hp with rfl | hp
    · have h := h12.1
      obtain ⟨d, hd'⟩ : ∃ d, p.d = d + 1 := ⟨p.d - 1, by omega⟩
      rw [GlobalTheory.StringDecomp.spehLoc_eq, hd', List.range_succ_eq_map, List.foldr_cons,
        A.unr_sum] at h
      exact (A.unr_tw (A.locG p.π w) _).1 h.1
    · exact ih h12.2 p hp hd

end UpperTheory.GalN
