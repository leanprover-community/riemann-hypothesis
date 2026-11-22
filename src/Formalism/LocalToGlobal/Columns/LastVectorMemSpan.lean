module

public import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
public import Formalism.LocalToGlobal.HermitianForms.BothLemmas

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

end Mat

section Form

variable {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]

end Form

variable {D : ColRec}

variable {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} {K : CF.ClsPTied u}

variable (T : CF.TilTied u A K (P D.R.m le_rfl))

end Formalism.L2.Col
