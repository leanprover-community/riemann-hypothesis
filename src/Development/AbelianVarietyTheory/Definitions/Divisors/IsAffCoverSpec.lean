module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CechDR GlobalTheory.CxForm GlobalTheory.CxPts
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ContDiff

namespace GlobalTheory.PD

section Smooth

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

variable {ι : Type} [LinearOrder ι]

end Smooth

section Scheme

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ)

variable [IsIntegral X]

@[reducible] def ffAlg : Algebra k X.functionField :=
  ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra

variable [Algebra k X.functionField]

omit σ in
structure IsAffCover {ι : Type} (U : ι → X.Opens) (B : Finset ι → Subalgebra k X.functionField) : Prop where
  alg : algebraMap k X.functionField = @algebraMap k X.functionField _ _ (ffAlg p)
  affine : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (I.inf U)
  cover : iSup U = ⊤
  ne : ∀ I : Finset ι, genericPoint X ∈ I.inf U
  ring : ∀ I : Finset ι, I.Nonempty → ∀ y, y ∈ B I ↔ ∃ f : Γ(X, I.inf U), (X.presheaf.germ (I.inf U) (genericPoint X) (ne I)).hom f = y

end Scheme

section Compare

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

variable {A}

variable (A)

end Compare

section Basic₂

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

end Basic₂

section Inhab

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

end Inhab

end GlobalTheory.PD
