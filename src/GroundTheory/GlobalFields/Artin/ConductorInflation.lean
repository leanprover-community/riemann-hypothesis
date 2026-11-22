module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
public import GroundTheory.LocalFields.DifferentGalois
public import GroundTheory.LocalFields.ConductorMatch
public import GroundTheory.GlobalFields.Artin.InflationTower
public import GroundTheory.LocalFields.LowerIndexQuotient
public import GroundTheory.LocalFields.IntermediateField

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section LocalInflation

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

variable {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M] [IsGalois K M] [Algebra M L]
  [IsScalarTower K M L]

end LocalInflation

section GlobalInflation

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]

section Tower

variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] isScalarTower_adicCompletion

variable [IsGalois K F] [IsGalois K L]

end Tower

variable [IsGalois K F] [IsGalois K L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end GlobalInflation

end GroundTheory.Global
