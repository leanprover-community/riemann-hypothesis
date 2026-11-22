module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Mathlib
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingL2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFormalDegree.VUnitInvVal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPfKFin
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.CoefBoundUniform
public import CompanionTheory.AutomorphicTheory.RankOneEstimates.RankOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem inputs_holds : Inputs := by
  have hDecay := CompanionTheory.FamilyDerivativeExpansion.DecS.decay_infinite_range
  exact ⟨Formalism.L2.SG.BesselDiscreteSeries.decLow, hDecay,
    CompanionTheory.D.gk.admitted.k_finite_smooth, trivial⟩

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end
