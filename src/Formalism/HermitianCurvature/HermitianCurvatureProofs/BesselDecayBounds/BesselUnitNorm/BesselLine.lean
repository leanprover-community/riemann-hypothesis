module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.BesselLine

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

def muSof {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map (fun p => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)

end PI.BesselLine

namespace PI

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine

end PI
