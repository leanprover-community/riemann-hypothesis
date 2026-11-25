module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

noncomputable section

namespace PI.VolStabS.TopoAF

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology TopologicalSpace Filter
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F]

export PI.VolStabSW.TopoAF (countable_ideal)

export PI.VolStabSW.TopoAF (isOpen_integers)

section HA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F} {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]

export PI.VolStabSW.TopoAF (secondCountable_HA_of)

end HA

end PI.VolStabS.TopoAF
