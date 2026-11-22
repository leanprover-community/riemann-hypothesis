module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.TameInertiaTowers.TowerFieldFoundations
public import Formalism.CyclotomicNorms.StatementI
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField
open scoped Pointwise

attribute [instance] Arith.instField Arith.instNF

variable {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1))

end Formalism.MainNotions.Inhab

end
