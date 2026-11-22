module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
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
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
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
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePair
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum

@[expose] public section

open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)

noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
