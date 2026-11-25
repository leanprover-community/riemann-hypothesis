module

public import Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut
import Development.EtaleCohomology.EtaleSheaves.LeafDescendChainPf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf

namespace LateralTheory.E.LeafPropsDescendPf.BaseChange

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

theorem toR_incl {R R' : Subalgebra k Ω} (hR : R ≤ R') : toR R' ≫ incl hR = toR R := by
  rw [← Spec.map_comp]
  rfl

end LateralTheory.E.LeafPropsDescendPf.BaseChange

end
