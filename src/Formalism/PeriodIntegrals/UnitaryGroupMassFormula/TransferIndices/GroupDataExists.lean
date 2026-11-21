import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.PerS

noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section Bound

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem norm_chiT_le (P : Pair K G) (x : G) (σ : K →+* ℂ) : ‖σ (chiT P x)‖ ≤ 1 := by
  by_cases hx : x ∈ P.H
  · rw [chiT_of_mem P x hx]
    have h := chi_inv_pow P ⟨x, hx⟩
    have h2 : (σ (((P.chi ⟨x, hx⟩)⁻¹ : Kˣ) : K)) ^ (Nat.card P.H) = 1 := by rw [← map_pow, h, map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h2 (card_H_pos P).ne').le
  · rw [chiT_of_not_mem P x hx, map_zero, norm_zero]; exact zero_le_one

theorem prod_expand (c c' : G → K) (g' g : G) :
    (∑ x : G, c x • MonoidAlgebra.of K G x) * MonoidAlgebra.of K G g' *
        ((∑ y : G, c' y • MonoidAlgebra.of K G y) * MonoidAlgebra.of K G g) =
      ∑ x : G, ∑ y : G, (c x * c' y) • MonoidAlgebra.of K G (x * g' * (y * g)) := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hof : MonoidAlgebra.of K G x * MonoidAlgebra.of K G g' * (MonoidAlgebra.of K G y * MonoidAlgebra.of K G g) =
      MonoidAlgebra.of K G (x * g' * (y * g)) := by simp only [map_mul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hof, mul_comm (c' y) (c x)]

theorem entry_bound (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (g' g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G g' * (epsS P * MonoidAlgebra.of K G g))))‖ ≤
      ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
  have hd : (Module.finrank K (T.W s) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast finrank_le_card (T.tau s) (T.irr s)
  rw [epsS, epsS, prod_expand, map_sum, map_sum, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x y : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      ((chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖ ≤ (Fintype.card G : ℝ) := by
    intro x y
    rw [map_smul, map_smul, Representation.asAlgebraHom_of, smul_eq_mul, map_mul, map_mul, norm_mul, norm_mul]
    have h1 := norm_chiT_le P0 x σ
    have h2 := norm_chiT_le P y σ
    have h3 := norm_trace_tau_le (T.tau s) (x * g' * (y * g)) σ
    calc ‖σ (chiT P0 x)‖ * ‖σ (chiT P y)‖ * ‖σ (LinearMap.trace K (T.W s) ((T.tau s) (x * g' * (y * g))))‖
        ≤ 1 * 1 * (Module.finrank K (T.W s) : ℝ) := by
          gcongr
      _ ≤ _ := by rw [one_mul, one_mul]; exact hd
  calc ∑ x : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (∑ y : G, (chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖
      ≤ ∑ x : G, ∑ y : G, (Fintype.card G : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [map_sum, map_sum, map_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hterm x y)
    _ = ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Bound


end PI.Dv.TIW
