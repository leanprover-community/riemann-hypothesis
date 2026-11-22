module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCOB

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ExpU (D : D7) : Prop := ∀ (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D χ τ a → HasInfExp D χ τ b → a = b

variable {ψ : AddChar (AF D.host.F) ℂ}

end Formalism.L2.Fam.ThC

end
