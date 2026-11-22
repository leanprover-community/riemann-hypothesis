module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueSat
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem BlowUpChart.full : BlowUpChart.Statement := BlowUpChart.proof

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement := FiniteIntegralClosure.proof

theorem MertensUpper.full : MertensUpper.Statement := MertensUpper.proof

theorem TorsionFreeQuotientLength.full : TorsionFreeQuotientLength.Statement := TorsionFreeQuotientLength.proof

theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

end GroundTheory.Heights₂.Heights.Model

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
