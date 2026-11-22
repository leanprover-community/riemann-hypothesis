module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
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
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

noncomputable section

open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape

variable {D : D7}

def latPi (S : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.FinPl.Lat S :=
  Submodule.pi Set.univ fun _ => (I : Submodule (𝓞 D.host.E) D.host.E)


variable (D) in
def tiltSc (j : ℕ) (p : Fin (D.R.m - 1 - j)) : D.host.E :=
  if Odd j then
    (if 2 * p.1 < D.R.m - 1 - j then (D.host.xi0 ^ p.1)⁻¹ else star (D.host.xi0 ^ (D.R.m - 1 - j - 1 - p.1)))
  else 1


variable (D) in
def rowId (j : ℕ) (p : Fin (D.R.m - 1 - j)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  FractionalIdeal.spanSingleton _ (tiltSc D j p) * stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p

variable {T : Type} {L : LevCh D T} {sc : Consts}

def rowN (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (G.V (.grid D.R.m j)) :=
  if h : j < D.R.m then (G.rowDec j h).lat (G.Λ (.top j)) (rowId D j) else G.Λ (.grid D.R.m j)


variable (D) in
def lineId (j : ℕ) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  D.host.AA ^ ((D.R.m - 2 - j) / 2 + 1) * (D.host.AAbar ^ ((D.R.m - 2 - j) / 2 + 1))⁻¹


variable (D) in
def lineL (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.SeeSaw.Model.nLine D) := latPi _ (lineId D j)


variable (D) in
def topL : GlobalTheory.FinPl.Lat (GlobalTheory.RowChain.pLine D) := latPi _ 1

def coreL (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) :=
  (G.Λ (.top j)).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iA).restrictScalars
        (𝓞 D.host.E)) ⊔
    (lineL D j).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iB).restrictScalars
        (𝓞 D.host.E))

end GlobalTheory.RowShape

end
