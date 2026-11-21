import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitShear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

def shearU (ι : Type) :
    ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) ≃ₜ+ ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' x y := Prod.ext rfl (by
    show x.1 + y.1 - (x.2 + y.2) = (x.1 - x.2) + (y.1 - y.2)
    abel)
  continuous_toFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)


end PI.UnitaryGroupMassFormula.LocJacTyp
