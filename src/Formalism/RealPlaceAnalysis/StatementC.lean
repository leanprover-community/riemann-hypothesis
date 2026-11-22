module

public import Formalism.RealPlaceAnalysis.StatementB

@[expose] public section

open Finset

noncomputable section

namespace Formalism.REAL

def cyc {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {W : Submodule ℂ V | v ∈ W ∧ ∀ a b, ∀ x ∈ W, E a b x ∈ W}

end Formalism.REAL
