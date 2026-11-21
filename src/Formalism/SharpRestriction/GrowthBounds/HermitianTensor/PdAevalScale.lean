import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

variable (A : Type) [CommRing A] (r : ℕ)

def pdW : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) := fun i j => if i = j.rev then 1 else 0

def pdZ : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) := fun i j => (genY A r).adjugate j.rev i







theorem detY_eq : detY A r = (genY A r).det := rfl





end Formalism.MainNotions.flipOneThree.Pf

end
