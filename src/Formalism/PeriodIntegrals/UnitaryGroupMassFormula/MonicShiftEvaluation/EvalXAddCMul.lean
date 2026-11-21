import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FinalWR

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
