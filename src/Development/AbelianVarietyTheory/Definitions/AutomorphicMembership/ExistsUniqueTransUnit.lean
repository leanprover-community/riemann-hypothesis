module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRangeOfCls
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ScalCompSpecMap
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Bdy

section Transl

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

variable {D}

end Transl

section Gen

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Dg : DegData R (maximalIdeal R))

variable {Dg}

end Gen

section Sec

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I D A G)

end Sec

section Coef

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (maximalIdeal R) D A G) (hR : AdmBase R (maximalIdeal R)) [GeometricallyConnected G.hom]

end Coef

end GlobalTheory.LocM.Bdy
