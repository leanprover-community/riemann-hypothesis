import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem multipliable_ofReal_re_of_complex (ι : Type) (c : ι → ℂ) (hc : Multipliable c)
    (hcr : ∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) :
    Multipliable (fun i => ENNReal.ofReal (c i).re) ∧
      ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  obtain ⟨a, ha⟩ := hc
  have hc' : ∀ i, c i = ((c i).re : ℂ) := fun i => Complex.ext (by simp) (by simp [(hcr i).1])
  have hre : HasProd (fun i => (c i).re) a.re := by
    have h := (Complex.continuous_re.tendsto a).comp ha
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [Finset.prod_congr rfl (fun i _ => hc' i), ← Complex.ofReal_prod, Complex.ofReal_re]
  have h2 : HasProd (fun i => ENNReal.ofReal (c i).re) (ENNReal.ofReal a.re) := by
    have h := (ENNReal.continuous_ofReal.tendsto a.re).comp hre
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hcr i).2)]
  exact ⟨h2.multipliable, by rw [h2.tprod_eq, ha.tprod_eq]⟩

theorem multipliable_ofReal_re_of_complex' : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re :=
  multipliable_ofReal_re_of_complex

end GlobalTheory
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multipliable_ofReal_re_of_nonneg_real : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  atlas_forward_decl GlobalTheory.multipliable_ofReal_re_of_complex'
