module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemisimplificationMatrixRepSameCharpoly

@[expose] public section

noncomputable section

namespace GlobalTheory.EigTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.Triple (IsParam IsResidual FbAt)
open GlobalTheory.HeightCounting (RowSide PlSide IotaOk setTy factRes)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

variable {D : D7}

theorem mem_plB (Pl : PlSide D) (w : D.what₂.places.Pl) (z : Zbar (D.what₂.places.resChar w)) :
    Pl.ι w (z : Qbar (D.what₂.places.resChar w)) ∈ Pl.plB w := by
  rw [Pl.plB_eq, RingEquiv.symm_apply_apply]
  exact z.2

def plRed (Pl : PlSide D) (w : D.what₂.places.Pl) : Zbar (D.what₂.places.resChar w) →+* FbAt D w :=
  ((Pl.plκ w).toRingHom.comp (IsLocalRing.residue (Pl.plB w))).comp
    (((Pl.ι w).toRingHom.comp (Zbar (D.what₂.places.resChar w)).subtype).codRestrict (Pl.plB w) (mem_plB Pl w))

theorem plRed_eq (Pl : PlSide D) (w : D.what₂.places.Pl) (z : Zbar (D.what₂.places.resChar w)) :
    plRed Pl w z = Formalism.L2.NT.redThrough (Pl.plB w) (Pl.plκ w) (Pl.ι w z) := by
  rw [Formalism.L2.NT.redThrough, dite_eq_left (mem_plB Pl w z)]
  rfl

theorem teichAt_of_iotaOk {Pl : PlSide D} (h : IotaOk D Pl) (w : D.what₂.places.Pl) : TeichAt (Pl.ι w) w (plRed Pl w) :=
  fun k _ v x _ z hz => by rw [plRed_eq, hz, RingEquiv.apply_symm_apply, h]

end GlobalTheory.EigTie

end
