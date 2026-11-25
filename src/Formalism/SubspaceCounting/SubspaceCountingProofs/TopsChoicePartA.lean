module

public import Formalism.SubspaceCounting.StatementB
public import Mathlib.Basic.Real.Basic

@[expose] public section

noncomputable section

open Finset

namespace Formalism.G0

namespace TopsConditionalProbabilityWindows

open Classical in
def P (U : Finset ℕ) (δ : ℝ) (A : Finset ℕ → Prop) : ℝ :=
  by classical exact ∑ t ∈ U.powerset, if A t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0

end TopsConditionalProbabilityWindows

end Formalism.G0
