module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilRepresentationExists
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock

variable {V : Type} [AddCommGroup V] [Module ℂ V]

open scoped IsMulCommutative in
def polEval {ι : Type} (m : ι → Module.End ℂ V) (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) :
    MvPolynomial ι ℂ →ₗ[ℂ] V :=
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range m)) :=
    Algebra.isMulCommutative_adjoin ℂ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hm i j)
  (LinearMap.applyₗ f₀ ∘ₗ (Algebra.adjoin ℂ (Set.range m)).val.toLinearMap) ∘ₗ
    (MvPolynomial.aeval (fun i => (⟨m i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range m)))).toLinearMap

def polMap (W Λ : Type) [Fintype W] [DecidableEq W] :
    (⨂[ℂ] _ : W, MvPolynomial Λ ℂ) →ₗ[ℂ] MvPolynomial (W × Λ) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (W × Λ) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Prod.mk w)).toLinearMap)

def unitAt {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    W → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

def fockM {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))

def fockD {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I)))

def coefM (z ε : ℂ) : ℂ := (z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

def coefD (z ε : ℂ) : ℂ := -(z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

end GlobalTheory.CCRFock
