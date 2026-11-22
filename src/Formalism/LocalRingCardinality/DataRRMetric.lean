module

public import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataParams₂

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions

open NumberField

namespace DV

variable {D : D7}

end DV

structure EigIdx (D : D7) (X : DivX D) where
  Pi : Type
  [fin : Fintype Pi]
  [dec : DecidableEq Pi]
  cOf : D.what₂.FT → Pi
  lam_const : ∀ j ∈ SizeData₂.lifts D, ∀ π π' e, D.what₂.isot j π ≠ ⊥ → D.what₂.isot j π' ≠ ⊥ → cOf π = cOf π' →
    X.logLam j π e = X.logLam j π' e

attribute [instance] EigIdx.fin EigIdx.dec

end Formalism.BasicNotions

end
