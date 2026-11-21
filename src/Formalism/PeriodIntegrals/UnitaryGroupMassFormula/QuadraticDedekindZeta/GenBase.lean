import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.Development

section
open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂



variable {K : Type} [Field K] [NumberField K]


theorem cnt_one : cnt K 1 = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun y => Subtype.ext (Ideal.absNorm_eq_one_iff.mp y.2)⟩




end PI.ClassNumImQ.ZetaNonvanishing₂
end

section
open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_span_two (h2 : Module.finrank ℚ K = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have hn : Algebra.norm ℤ ((p : 𝓞 K)) = (p : ℤ) ^ 2 := by
    rw [show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, h2]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast]



theorem ne_bot_of_absNorm {P : Ideal (𝓞 K)} {n : ℕ} (hP : Ideal.absNorm P = n) (hn : n ≠ 0) :
    P ≠ ⊥ := by
  rintro rfl
  rw [Ideal.absNorm_bot] at hP
  exact hn hP.symm




end PI.ClassNumImQ.ZetaNonvanishing₂
end
