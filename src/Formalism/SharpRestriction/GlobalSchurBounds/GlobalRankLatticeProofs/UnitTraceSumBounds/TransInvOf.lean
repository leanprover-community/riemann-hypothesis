module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ := by
  have hdeg := Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw)
  refine (HI D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) hdeg ⟨fun f => ?_⟩ cc δ hc hδ).1
  suffices hd : D.host.d = 0 by
    suffices Module.finrank ℚ D.host.K = 1 by omega
    apply IntermediateField.finrank_eq_one_iff.mpr
    change IntermediateField.adjoin ℚ {D.host.sqd} = ⊥
    rw [show D.host.sqd = 0 by simpa [hd] using D.host.sqd_sq]
    exact IntermediateField.adjoin_simple_eq_bot_iff.mpr (zero_mem _)
  let s : D.host.K := ⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩
  suffices (f s) ^ 2 = -(D.host.d : ℝ) by
    apply Nat.eq_zero_of_le_zero
    exact_mod_cast (show (D.host.d : ℝ) ≤ 0 by linarith [sq_nonneg (f s)])
  simpa only [map_pow, map_neg, map_natCast] using
    congrArg f (show s ^ 2 = -((D.host.d : ℕ) : D.host.K) from Subtype.ext (by simpa [s] using D.host.sqd_sq))

theorem delta_ne (HI : IdealLattice) (HD : DiscrNe) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat HI D cc hc 1 one_ne_zero
  rintro rfl
  exact HD w₁ w₂ hw (by simpa [hL] using (show (0 : ℂ) ^ 12 = discr (lamOf D cc 1) from hδ).symm)

end Formalism.MainNotions.Ext
