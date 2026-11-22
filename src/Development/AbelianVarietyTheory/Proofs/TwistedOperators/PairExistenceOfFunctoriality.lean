module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
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
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFockIntertwinerAdjointExchangedPairStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeriesStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PairIt

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_locIt_pair {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X : ProvA} (hX : ChosenSeries X)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X) (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D)
    (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {aS aT : ℚ}
    (hP : GlobalTheory.PairLift.PairPar (S τ) (S' τ) aS aT) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨t, P, P', hS, hS', hc⟩ := hP
  rcases hc with ⟨⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩, -⟩ | ⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩
  · exact exists_locIt hX h1 h2 hB M M' τ hd (hS.trans (congrArg dualPar e1)) (hS'.trans (congrArg dualPar e2))
  · obtain ⟨hr, A, hA⟩ := GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e2)) (hS.trans (congrArg dualPar e1))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · obtain ⟨hr, A, hA⟩ := exists_locIt hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e1)) (hS.trans (congrArg dualPar e2))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ hd
      (hS.trans (congrArg dualPar e2)) (hS'.trans (congrArg dualPar e1))

end GlobalTheory.PairIt

end
