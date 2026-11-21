import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Torsor
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AutomorphicArithmetic.CommutativeAlgebra.AlgHTDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescendsFg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdemKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero

section
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace ObjMapPts

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S₂ : Scheme.{0}} {s₁ : S ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o : Obj b N s₁} {o₂ : Obj b N s₂} {f : S ⟶ S₂}

def push (m : ObjMap o o₂ f) {k : Type} [CommRing k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ o.A) : Over.mk (x ≫ f) ⟶ o₂.A :=
  Over.homMk (g.left ≫ m.φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [m.cart.1.w, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w g))

@[simp] theorem push_left (m : ObjMap o o₂ f) {k : Type} [CommRing k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ o.A) :
    (push m x g).left = g.left ≫ m.φ := rfl

end ObjMapPts

end GlobalTheory.UPel.HT.ES
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.crystallineComparison

noncomputable section

namespace GlobalTheory.ESOrdM

theorem stalk_normal_of_smooth (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0})
    (f : X ⟶ Sp R) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f (fun y => ?_) x
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  let _ : Algebra R ((Sp R).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have h : IsLocalization.AtPrime ((Sp R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have hle : y.asIdeal.primeCompl ≤ nonZeroDivisors R := y.asIdeal.primeCompl_le_nonZeroDivisors
  have hd : IsDomain ((Sp R).presheaf.stalk y) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  exact ⟨hd, isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.ESOrdM
end
end
