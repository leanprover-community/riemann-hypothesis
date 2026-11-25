module

public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace PrimeReciprocalSums

theorem hOf_ord (e l : ℕ) (hl : Nat.Coprime l 2) :
    ordH (hOf e l) = orderOf (hcl e (ZMod.unitOfCoprime l (Nat.Coprime.pow_right (e + 2) hl))) := by
  simp only [hOf, dite_eq_left hl, ordH, ← orderOf_iotaH, iotaH_iotaHInv]

end PrimeReciprocalSums

open PrimeReciprocalSums

end Formalism.MainNotions.UnusedSlot33

end
