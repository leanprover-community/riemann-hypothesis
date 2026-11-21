import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonicShiftEvaluation.EvalXAddCMul

open Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation

open Formalism.QuantumDeterminants

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]


theorem term (r : ℕ) (c : R r E) (Y : ℂ) (j : ℕ) (f : WSm r E) :
    (((c * algebraMap ℂ (R r E) Y ^ j) f : WSm r E) : (Fin r → ℂ) → E) =
      Y ^ j • ((c f : WSm r E) : (Fin r → ℂ) → E) := by
  rw [← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, Submodule.coe_smul]


end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
