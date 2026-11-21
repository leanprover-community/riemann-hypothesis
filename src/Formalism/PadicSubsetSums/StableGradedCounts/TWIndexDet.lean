import Formalism.PadicSubsetSums.StableGradedCounts.TWIndexAdditive

open Module

namespace Formalism.IrreducibleCountingLemmas.TW

namespace Idx

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem valuation_unique {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a : ℤ) (m : ℕ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a
      = algebraMap O K v * algebraMap O K ϖ ^ (a + (m : ℤ))) : m = 0 := by
  have hπ : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  rw [zpow_add₀ hπ, zpow_natCast, mul_comm (_ ^ a), ← mul_assoc] at h
  have h2 := mul_right_cancel₀ (zpow_ne_zero a hπ) h
  rw [← map_pow, ← map_mul] at h2
  have h3 := IsFractionRing.injective O K h2
  by_contra hm
  have : IsUnit (ϖ ^ m) := isUnit_of_mul_isUnit_right (h3 ▸ u.isUnit)
  exact hϖ.not_isUnit ((isUnit_pow_iff hm).1 this)

theorem val_unique {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a b : ℤ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a = algebraMap O K v * algebraMap O K ϖ ^ b) :
    a = b := by
  rcases le_total a b with hab | hab
  · obtain ⟨m, rfl⟩ := Int.le.dest hab
    have := valuation_unique hϖ u v a m h
    simp [this]
  · obtain ⟨m, rfl⟩ := Int.le.dest hab
    have := valuation_unique hϖ v u b m h.symm
    simp [this]

end Idx


end Formalism.IrreducibleCountingLemmas.TW
