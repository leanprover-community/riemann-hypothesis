import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AeComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.UnipTorsion
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section Fx

open Matrix Ws.Eb

private def sn {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) (DualNumber K)) :
    Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (X i j).snd






end Fx

section Tw

open Matrix Ws.Eb

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)

include K in
private theorem fx_kk {A : Type} [CommRing A] [Algebra O A] (g : G.G₀) :
    ((K.κA A g : Aˣ) : A) * (K.κA A (G.conj g) : Aˣ) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) := by
  have h := congrArg (Units.map (algebraMap O A : O →* A)) (K.κ_conj g)
  rw [map_mul, map_zpow] at h
  exact congrArg Units.val h



variable {Q : Type} [Field Q] [Algebra O Q]

private noncomputable def fxY (ρD : Fr.NRep F n (DualNumber Q)) (g : G.G₀) : Matrix (Fin n) (Fin n) Q :=
  sn (ρD.r (K.π g)) * (ρD.map (dF Q)).r (K.π g)⁻¹





end Tw

section Core

open Matrix Ws.Eb

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
  {Q : Type} [Field Q] [Algebra O Q]




variable [CharZero Q] [IsAlgClosed Q] [TopologicalSpace Q] [IsTopologicalRing Q]


end Core

section Sp

open Matrix Ws.Eb

private noncomputable def fxD {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [Field Q] [Algebra O Q]
    (ξ : A →ₐ[O] Q) (D : A →ₗ[O] Q) (hD : D ∈ PtDer ξ Q) : A →ₐ[O] DualNumber Q :=
  have h1 : D 1 = 0 := by
    have h := hD 1 1
    rw [mul_one, map_one ξ, one_smul] at h
    exact left_eq_add.1 h
  { toFun := fun a => ⟨ξ a, D a⟩
    map_one' := TrivSqZeroExt.ext (map_one ξ) h1
    map_mul' := fun a b => TrivSqZeroExt.ext (map_mul ξ a b) (by
      refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
      change D (a * b) = ξ a * D b + D a * ξ b
      rw [mul_comm (D a)]
      exact hD a b)
    map_zero' := TrivSqZeroExt.ext (map_zero ξ) (map_zero D)
    map_add' := fun a b => TrivSqZeroExt.ext (map_add ξ a b) (map_add D a b)
    commutes' := fun a => TrivSqZeroExt.ext (ξ.commutes a) (by
      change D (algebraMap O A a) = 0
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]) }

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)



end Sp
