import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory

theorem coeff_coeff_pow_eq_of_box :
    ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧),
      (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  intro R _ m i n G H h
  induction m generalizing i n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨p, q⟩ hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl ?_
    rintro ⟨s, t⟩ hst
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hst
    dsimp only at hpq hst ⊢
    rw [ih p s (fun i' hi' n' hn' => h i' (by omega) n' (by omega)), h q (by omega) t (by omega)]

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coeff_pow_eq_of_coeff_coeff_eq_le : ∀ (R : Type) [CommRing R] (m i n : ℕ) (G H : R⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ m)) = coeff n (coeff i (H ^ m)) := by
  atlas_forward_decl GlobalTheory.coeff_coeff_pow_eq_of_box
