module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FirstOrderRigidityLevel
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCoset
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LevelBasisEqOfSameThetaPt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TracePowerSumModEq
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

end GlobalTheory.Published

namespace GlobalTheory.ThetaDetCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section AdjRing

open CechPic MulOpposite

variable {K : Type} [Field K] {P : PolAV (Sp K)}

end AdjRing

section Trace

open ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)} {M : ℕ} {y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A)}
  {O : Type} [Ring O]

variable [IsAlgClosed K]

end Trace

section Positive

variable {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {O : Type} [Ring O] [StarRing O]

end Positive

end GlobalTheory.ThetaDetCompare
