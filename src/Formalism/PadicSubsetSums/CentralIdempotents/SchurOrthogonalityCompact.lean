module

public import Formalism.PadicSubsetSums.CentralIdempotents.FactorOverLocalSubalgebraMonic

@[expose] public section

noncomputable section

open Polynomial MeasureTheory
open scoped TensorProduct NumberField ComplexConjugate

namespace Formalism.IrreducibleCountingLemmas.Z

def BCCyclicVector : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (g : Module.End K V), g.charpoly.Separable → ∃ e : V, ∀ v : V, ∃ p : K[X], aeval g p e = v

end Formalism.IrreducibleCountingLemmas.Z
