module

public import Mathlib
public import GroundTheory.LocalFields.FormalGroups.Basics

@[expose] public section

namespace GroundTheory.Arith.Abelian

noncomputable section

section Field

variable {K : Type*} [Field K] (V : WeierstrassCurve K)

open WeierstrassCurve.Affine

variable [V.IsElliptic]

end Field

section Points

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) (τ : Type*)

attribute [local instance] isDomain_mvPowerSeries

variable [Fact (W.Δ ≠ 0)]

end Points

section Lin

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {τ : Type*}

end Lin

section Assoc

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [Fact (W.Δ ≠ 0)]

attribute [local instance] isDomain_mvPowerSeries

end Assoc

section FormalGroupLaw

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

end FormalGroupLaw

end

end GroundTheory.Arith.Abelian
