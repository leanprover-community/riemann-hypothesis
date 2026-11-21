import Mathlib
import GroundTheory.AutomorphicForms.QuotientKernel

open MeasureTheory

namespace GroundTheory.Automorphic

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isCompactOperator_integrated (f : CompactlySupportedContinuousMap G ℂ) :
    IsCompactOperator ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) :=
  isCompactOperator_integrated_rightRegularRep Γ μ f


theorem finiteDimensional_intertwiners {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : UnitaryRep G K} (hσ : σ.IsIrreducible) :
    FiniteDimensional ℂ (σ.intertwiners (rightRegularRep Γ μ)) :=
  UnitaryRep.finiteDimensional_intertwiners (isCompactOperator_integrated Γ μ) hσ

end RightCosetSpace

end GroundTheory.Automorphic
