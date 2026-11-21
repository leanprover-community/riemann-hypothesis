import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FinalWR

section
open Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation

open Formalism.QuantumDeterminants

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev R (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] := Module.End ℂ (WSm r E)

def PQ (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : ℕ → (R r E)[X] × (R r E)[X]
  | 0 => (1, 0)
  | i + 1 =>
    if h : i < r then
      ((X + C (pEnd ⟨i, h⟩)) * (PQ r E i).1 - C (cEnd ⟨i, h⟩) * (PQ r E i).2,
        C (ciEnd ⟨i, h⟩) * (PQ r E i).1)
    else PQ r E i



end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
end
end

section
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
end
end
