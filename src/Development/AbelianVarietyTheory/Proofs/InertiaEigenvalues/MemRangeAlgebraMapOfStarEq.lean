import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import BuildAid.ForwardExisting

section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.JR

theorem Unram.mem_range_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  intro F E _ _ _ _ h y hy
  haveI := h.charZero
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨b, d, hb0, hs, -, -⟩ := Unram.exists_basis_antifixed F E
  have hsum := b.sum_repr y
  rw [Fin.sum_univ_two, hb0] at hsum
  set a := b.repr y 0
  set c := b.repr y 1
  have hst : star y = a • (1 : E) - c • b 1 := by
    rw [← hsum]
    simp only [Algebra.smul_def, star_add, star_mul', h.star_fix, hs, star_one]
    ring
  have h2 : (2 : E) * (c • b 1) = 0 := by linear_combination hsum + hst - hy
  have hc : c • b 1 = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  refine ⟨a, ?_⟩
  rw [← hsum, hc, add_zero, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.JR
end

open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_algebraMap_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  atlas_forward_decl GlobalTheory.JR.Unram.mem_range_of_star_eq
