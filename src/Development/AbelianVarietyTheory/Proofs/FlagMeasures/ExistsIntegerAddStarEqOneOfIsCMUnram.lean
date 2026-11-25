module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceOne
public import Formalism.HermitianLattices.StatementMass
import Mathlib.Tactic.Lemma
import Formalism.LocalRingCardinality.Params

@[expose] public section

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

open NumberField Module Matrix in
open scoped ENNReal in
open NumberField Module Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
      ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  first | exact _root_.GlobalTheory.TraceOnto.exists_trace_one | exact @_root_.GlobalTheory.TraceOnto.exists_trace_one | apply _root_.GlobalTheory.TraceOnto.exists_trace_one <;> assumption

end GlobalTheory
