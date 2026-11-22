module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum Formalism.IndefR.Lev
open scoped TensorProduct ComplexOrder
open Classical

namespace Formalism.IndefR.NX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

namespace ExpSet

variable (S : ExpSet D)

end ExpSet

attribute [instance] CoefLat.acg CoefLat.md

section SuppHalf

variable {m n : ℕ}

end SuppHalf

variable {S : ExpSet D} {O : Type} [CommRing O] {C : CoefLat S O}

namespace RawDat

end RawDat

end Formalism.IndefR.NX
