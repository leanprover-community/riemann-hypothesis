import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.ClaimOf

section
open Polynomial

noncomputable section

namespace PI.SqfRootsInj.W

open PI.SqfLab




end PI.SqfRootsInj.W
end
end

section
open Polynomial

noncomputable section

namespace PI.SqfRootsInj.W

open PI.SqfLab

section
variable {g : ℕ} [Fact g.Prime]

theorem root_facts {r : ℕ} {f : (ZMod g)[X]} (hf : IsLab g r f) {x : Fbar g}
    (hx : x ∈ rootsBar f) :
    x ≠ 0 ∧ minpoly (ZMod g) x ∣ f ∧ (minpoly (ZMod g) x).natDegree ≤ r ∧
      1 ≤ (minpoly (ZMod g) x).natDegree := by
  obtain ⟨hmon, hdeg, hc0⟩ := hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hroot : aeval x f = 0 := by
    unfold rootsBar at hx
    rw [mem_roots'] at hx
    rw [← eval_map_algebraMap]
    exact hx.2
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hdvd := minpoly.dvd (ZMod g) x hroot
  refine ⟨?_, hdvd, ?_, minpoly.natDegree_pos hint⟩
  · rintro rfl
    apply hc0
    have h0 := coeff_zero_eq_aeval_zero' (A := Fbar g) f
    rw [hroot] at h0
    exact (algebraMap (ZMod g) (Fbar g)).injective (by rw [h0, map_zero])
  · rw [← hdeg]
    exact natDegree_le_of_dvd hdvd hf0


theorem two_mul_le_of_dvd_ne {J E : ℕ} (hd : J ∣ E) (hne : J ≠ E) (hE : 1 ≤ E) : 2 * J ≤ E := by
  obtain ⟨c, hc⟩ := hd
  subst hc
  rcases Nat.lt_or_ge c 2 with h | h
  · interval_cases c
    · omega
    · exact absurd (mul_one J).symm hne
  · nlinarith




end


end PI.SqfRootsInj.W
end
end
