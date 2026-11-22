module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta
public import Formalism.LocalToGlobal.UnitaryNorms.IotaABijective
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist

@[expose] public section

open NumberField IntermediateField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.L2.Host Formalism.DivisionValues

instance normalQb : Normal ℚ Qb :=
  haveI : IsAlgClosure ℚ Qb := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  IsAlgClosure.normal ℚ Qb

def conjQb (ι : Qb →+* ℂ) : Qb ≃ₐ[ℚ] Qb :=
  AlgEquiv.ofRingEquiv (f := (algC ((starRingEnd ℂ).comp ι)).trans (algC ι).symm) (fun r => by simp)

theorem conjQb_spec (ι : Qb →+* ℂ) (x : Qb) : ι (conjQb ι x) = starRingEnd ℂ (ι x) := by
  have key : conjQb ι x = (algC ι).symm (algC ((starRingEnd ℂ).comp ι) x) := rfl
  rw [key, ← algC_coe ι ((algC ι).symm (algC ((starRingEnd ℂ).comp ι) x)),
    RingEquiv.apply_symm_apply, algC_coe] <;> rfl

@[reducible] def starLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : StarRing LL where
  star := cLL ι LL
  star_involutive := cLL_cLL ι LL
  star_mul a b := by rw [map_mul, mul_comm]
  star_add a b := map_add _ a b

namespace CoF

variable (ι : Qb →+* ℂ) (LL : Fld)

instance : Field (CoF ι LL) := inferInstanceAs (Field LL)

instance [FiniteDimensional ℚ LL] : NumberField (CoF ι LL) where
  to_charZero := inferInstanceAs (CharZero LL)
  to_finiteDimensional := inferInstanceAs (FiniteDimensional ℚ LL)

instance [Normal ℚ LL] : StarRing (CoF ι LL) := starLL ι LL

end CoF

end Formalism.L2.DIV
