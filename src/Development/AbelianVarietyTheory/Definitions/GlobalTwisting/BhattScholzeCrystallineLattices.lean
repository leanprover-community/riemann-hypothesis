module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Lean.Meta.Injective

@[expose] public section

namespace GlobalTheory.Fc.S0


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure HypothesesU : Prop where
  clozelCohomological : GlobalTheory.Published.ClozelCohomological
  greenCuspidal : GlobalTheory.Published.GreenCuspidal
  cohomologicalCsdTempered : GlobalTheory.Published.CohomologicalCsdTempered
  heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter
  chebotarevDegreeOne : GlobalTheory.Published.ChebotarevDegreeOne
  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL
  galoisRepOfPolarizedCuspidal : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  baseChangeDefiniteUnitary : GlobalTheory.Published.BaseChangeDefiniteUnitary
  bhattScholzeCrystallineLattices : GlobalTheory.Published.BhattScholzeCrystallineLattices
  heckeLAdicCharacterAbove : GlobalTheory.Published.HeckeLAdicCharacterAbove
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  siegelWeilUnitaryConvergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  doublingMethod : GlobalTheory.Published.DoublingMethod
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration
  unlinkedProductIrreducible : GlobalTheory.Published.UnlinkedProductIrreducible
  depthZeroJacquetInjective : GlobalTheory.Published.DepthZeroJacquetInjective
  howeDualityGL : GlobalTheory.Published.HoweDualityGL
  jacquetShalika : GlobalTheory.Published.JacquetShalika
  automorphicFormsFiniteGL : GlobalTheory.Published.AutomorphicFormsFiniteGL
  localGlobalAboveL : GlobalTheory.Published.LocalGlobalAboveL
  regularAlgebraicPurity : GlobalTheory.Published.RegularAlgebraicPurity
  globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity
  heckeLAdicParameterAbove : GlobalTheory.Published.HeckeLAdicParameterAbove
  deRhamPotSemistable : GlobalTheory.Published.DeRhamPotSemistable
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  greenRegularCharacters : GlobalTheory.Published.GreenRegularCharacters
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  depthZeroInertia : GlobalTheory.Published.DepthZeroInertia
  rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt
  rayCharacterArtin : GlobalTheory.Published.RayCharacterArtin
  genericUnitaryDualGL : GlobalTheory.Published.GenericUnitaryDualGL
  standardCosocleGL : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  siegelWeilUnitaryConvergent2 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  harishChandraAnalyticity : GlobalTheory.Published.HarishChandraAnalyticity
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  pseudoCoefficientUpq : GlobalTheory.Published.PseudoCoefficientUpq
  harishChandraCharacters : GlobalTheory.Published.HarishChandraCharacters
  langlandsClassification : GlobalTheory.Published.LanglandsClassification
  labesseWaldspurger : GlobalTheory.Published.LabesseWaldspurger
  cMCurveGoodOutsidePrimeSt : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  weberRayFieldSt : GlobalTheory.Published.WeberRayFieldSt
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  besselUniquenessReal : GlobalTheory.Published.BesselUniquenessReal
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation
  siegelEisensteinSimplePole : GlobalTheory.Published.SiegelEisensteinSimplePole
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  regularisedSiegelWeilFirstTerm : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport
  localFiniteness : ReciprocityTheory.Gal.LocalFiniteness
  localTateDuality : ReciprocityTheory.Gal.LocalTateDuality
  localEulerChar : ReciprocityTheory.Gal.LocalEulerChar

end GlobalTheory.Fc.S0
