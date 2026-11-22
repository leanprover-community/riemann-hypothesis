module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalFirstChernSurjective
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.RelativeGroupHatForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsLogGrNormSubLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.PublishedTheorems.ThetaCharacteristics.ThetaCharZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDieudonne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.QCoh


open TensorProduct in
theorem nontrivial_fibre_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    Nontrivial (q.ResidueField ⊗[S] N) ↔ Nontrivial (p.ResidueField ⊗[R] M) := by
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R S q.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap _ _ _ hpq r).symm
  have e₁ : q.ResidueField ⊗[S] N ≃ₗ[S] q.ResidueField ⊗[S] (S ⊗[R] M) :=
    LinearEquiv.lTensor q.ResidueField hl.equiv.symm
  have e₂ : q.ResidueField ⊗[S] (S ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S q.ResidueField q.ResidueField M
  have e₃ : q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] M) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField M
  rw [e₁.toEquiv.nontrivial_congr, e₂.toEquiv.nontrivial_congr, ← e₃.toEquiv.nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField q.ResidueField

theorem mem_support_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (q : PrimeSpectrum S) :
    q ∈ Module.support S N ↔ PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M := by
  haveI : Module.Finite S N := Module.Finite.equiv hl.equiv
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact nontrivial_fibre_of_isBaseChange hl _ _ rfl

theorem support_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [IsFiniteQC G] :
    support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G := by
  ext y
  obtain ⟨U, V, hU, hV, hy, -, e⟩ := exists_affine_pair f y (W := ⊤) trivial
  have hfy : f y ∈ V := e hy
  rw [Set.mem_preimage, mem_support_iff_primeIdealOf hU ⟨y, hy⟩,
    mem_support_iff_primeIdealOf hV ⟨f y, hfy⟩]
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  have := finite_sections G hV
  rw [mem_support_of_isBaseChange (isBaseChange_pullbackSections f G hU hV e)]
  have h := IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hy
  convert Iff.rfl using 2
  exact h.symm

end GlobalTheory.QCoh
