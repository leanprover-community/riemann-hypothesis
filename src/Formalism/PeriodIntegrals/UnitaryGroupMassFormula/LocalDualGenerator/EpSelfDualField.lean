module

public import Mathlib

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section
open ValuativeRel IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace PI.LocDualGen.EpF

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]

theorem tf : Module.IsTorsionFree 𝒪[K] L := by
  first
    | exact Module.IsTorsionFree.trans_faithfulSMul 𝒪[K] K L
    | (rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
        IsScalarTower.algebraMap_eq 𝒪[K] K L]
       exact (algebraMap K L).injective.comp Subtype.val_injective)

attribute [local instance] dd fr mf tfC

attribute [local instance] sepFR

end PI.LocDualGen.EpF
