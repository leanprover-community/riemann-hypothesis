module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff

@[expose] public section

section
namespace GlobalTheory.NRows
structure GeometricGaloisRepCompatibility : Prop where
  weil : GlobalTheory.Published.WeilRepresentationUnitaryPair
  ds : GlobalTheory.Published.DiscreteSeriesExists
  ana : GlobalTheory.Published.HarishChandraAnalyticity
  dsc : GlobalTheory.Published.DiscreteSeriesClassification
  trc : GlobalTheory.Published.CuspTraceClass
  dm : GlobalTheory.Published.DixmierMalliavinFactorisation
  flath : GlobalTheory.Published.FlathFactorisation
  sw : GlobalTheory.Published.WeilSiegelFormulaUnitary
  dbl : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  udbl : GlobalTheory.Published.UnramifiedDoublingGL
  hl : GlobalTheory.Published.HeckeLPartialContinuation
  ht : GlobalTheory.HeightCounting.HtCard
end GlobalTheory.NRows
end
