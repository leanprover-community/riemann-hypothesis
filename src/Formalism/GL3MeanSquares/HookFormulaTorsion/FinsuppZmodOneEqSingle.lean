import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
import Formalism.LogVandermondeBounds.LogVandermondeProofs.TaylorLogMetric
import Formalism.FormalGroupWitt.WeightInvariance
import Formalism.TorsionNormIteration.LubinTateExample

section
namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem norm_for_all_alpha : NormAllAlpha := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm tr hinj hnm htr hadd hlin hadj h2 α α' u hu2 hα hα'
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have add2 : ∀ a b b', cob φ a (b + b') = cob φ a b + cob φ a b' := by
    intro a b b'; rw [symm, hadd, symm b, symm b']
  have e1 : φ ((α + α') • u) = φ (α • u) + φ (α' • u) + cob φ (α • u) (α' • u) := by
    unfold cob; rw [add_smul]; abel
  have e2 : cob φ (α • u) (α' • u) = cob φ u ((star α * α') • u) := by rw [hadj, smul_smul]
  have e3 : cob φ u ((star α * α') • u) + cob φ u ((star α * α') • u)
      = (tr (star α * α')) • cob φ u u := by
    have h : cob φ u ((star α * α') • u) = cob φ u (star (star α * α') • u) := by
      rw [symm, hadj]
    nth_rewrite 1 [h]; rw [← add2, ← add_smul, ← htr, hlin]
  have e4 : cob φ u u = φ u + φ u := by
    unfold cob; rw [← two_smul O u, hu2]
    have : (4 : Z) • φ u = φ u + φ u + φ u + φ u := by
      rw [show (4 : Z) = 1 + 1 + 1 + 1 by norm_num]; simp [add_smul]
    rw [this]; abel
  have e5 : cob φ u ((star α * α') • u) = tr (star α * α') • φ u := by
    apply sub_eq_zero.1; apply h2
    have : ∀ x y : Q, (x - y) + (x - y) = (x + x) - (y + y) := by intro x y; abel
    rw [this, e3, e4, smul_add, sub_self]
  have e6 : nm (α + α') = nm α + nm α' + tr (star α * α') := by
    apply hinj; simp only [map_add, hnm, htr, star_add, star_mul, star_star]; ring
  rw [e1, e2, e5, hα, hα', e6, add_smul, add_smul]

end Formalism.HermitianLattices.IntegralLatticeDensity
end

section
namespace Formalism.HermitianLattices.IntegralLatticeDensity

namespace LemE

open MvPowerSeries Finset Formalism.G Formalism.FG

noncomputable abbrev s1 (n : ℕ) : ZMod 1 →₀ ℕ := Finsupp.single 0 n

noncomputable abbrev mon (k m : ℕ) : Fin 2 × ZMod 1 →₀ ℕ :=
  Finsupp.single ((0 : Fin 2), (0 : ZMod 1)) k + Finsupp.single ((1 : Fin 2), (0 : ZMod 1)) m

section Generic

variable {K : Type} [Field K] {τ : Type}

lemma coeff_add_pow (k m : ℕ) :
    coeff (mon k m) ((X ((0 : Fin 2), (0 : ZMod 1)) + X ((1 : Fin 2), (0 : ZMod 1)) :
      MvPowerSeries (Fin 2 × ZMod 1) K) ^ (k + m)) = ((k + m).choose k : K) := by
  classical
  rw [add_pow, map_sum, Finset.sum_eq_single k]
  · rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, Nat.add_sub_cancel_left, ← nsmul_eq_mul',
      map_nsmul, coeff_monomial_same]
    simp
  · intro j _ hj
    rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, ← nsmul_eq_mul', map_nsmul, coeff_monomial,
      if_neg, smul_zero]
    intro h
    have := congrArg (fun d => d ((0 : Fin 2), (0 : ZMod 1))) h
    simp at this
    exact hj this.symm
  · intro h
    exact absurd (mem_range.2 (by omega)) h

end Generic

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

end Padic

section Main

variable {p : ℕ} [hp : Fact p.Prime]

def Good (f : MvPowerSeries (ZMod 1) ℚ_[p]) (N : ℕ) (z : ℚ_[p] × ℚ_[p]) : Prop :=
  ‖z.1‖ ≤ 1 ∧ ‖z.2 - coeff (s1 1) f‖ ≤ 1 ∧
    ∀ d ≤ N, ‖coeff (s1 d) f - z.1 * coeff (s1 d) (g0 p) -
      z.2 * coeff (s1 d) (shiftLog ℚ_[p] p 1 0)‖ ≤ 1

end Main

end LemE

end Formalism.HermitianLattices.IntegralLatticeDensity
end
