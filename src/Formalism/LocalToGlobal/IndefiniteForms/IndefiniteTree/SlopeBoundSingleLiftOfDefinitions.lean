module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.ExistsIsRegularOfListEqMaximalIdeal
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Formalism.ThetaSupremumBounds.LiftOperatorBoundOfFockJet

@[expose] public section

open Finset Module NumberField Formalism.HN

noncomputable section

namespace Formalism.L2.Indef.Tree

attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero

namespace SlopeBoundParameters

variable (P : SlopeBoundParameters)

end SlopeBoundParameters

attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι

namespace SlopeBoundLiftData

variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P)

end SlopeBoundLiftData

section Leaves

variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}

end Leaves

end Formalism.L2.Indef.Tree
