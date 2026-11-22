module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)

namespace GlobalTheory.ShFam.Pad

namespace FinLB

variable {X Y : Scheme.{0}}

end FinLB

attribute [instance] NModel.normal NModel.flat

namespace NModel

section Local

variable {O : Type} [CommRing O] (Z : NModel O)

variable [IsLocalRing O]

namespace VPair

variable {Z} (P P' P'' : VPair Z)

end VPair

end Local

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : NModel O)

section Over

variable {Z} {B : Model O} {f : B.X ⟶ Z.X} (hf : f ≫ Z.str = B.str)
include hf

end Over

namespace VPair

variable {Z} {P P' P'' : VPair Z}

section Pull

variable {B : Model O} {f : B.X ⟶ Z.X} (hf : f ≫ Z.str = B.str)

end Pull

end VPair

namespace VPair

variable {Z} {P P' P'' : VPair Z}

end VPair

section Lift

variable {Z} {A : Type*} [AddCommGroup A] (φ : VPair Z → A)
  (h : ∀ P P' P'' : VPair Z, P.IsSum P' P'' → φ P'' = φ P + φ P')

end Lift

variable {Z}

end NModel

end GlobalTheory.ShFam.Pad
