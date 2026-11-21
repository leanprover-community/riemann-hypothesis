import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt

section
variable (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

def redAs (m : Ideal A) : ↥(As O A) →ₐ[O] ↥(As O (A ⧸ m)) :=
  ((Ideal.Quotient.mkₐ O m).comp (As O A).val).codRestrict (As O (A ⧸ m))
    fun a => (show IsIntegral O (a : A) from a.2).map (Ideal.Quotient.mkₐ O m)


end



end Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
