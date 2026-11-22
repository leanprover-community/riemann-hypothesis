module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBiject
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp

