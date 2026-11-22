module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.SelfInterPow

theorem isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a → ∀ e : ℕ,
      (L.pow e).IsSelfInter ((e : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX L a ha e
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).1
  have h₁ := (((hC.arIso k X p D hX).2 Unit _ Φ hΦ).1 ()).unique hX ha
  obtain ⟨H, hH, he⟩ := hΦ.1 fun _ => (e : ℤ)
  refine ⟨H, (hC.arIso k X p D hX).1 _ _ H (GlobalTheory.ArInt.isometric_comb_unit_pow k X p L e) hH, he.trans ?_⟩
  rw [← h₁, ← smul_eq_mul, ← map_smul, ArInt.lin, Fintype.sum_unique, mul_pow, ← map_pow, MvPolynomial.smul_eq_C_mul]
  simp

end GlobalTheory.SelfInterPow
