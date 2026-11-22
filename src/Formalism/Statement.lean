module

public import Mathlib

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

end Formalism
