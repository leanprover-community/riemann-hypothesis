module

public import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
public import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticePropsOfModel
public import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem
public import Formalism.LocalToGlobal.GlobalTheory.GL6.CoordMapInjective
public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesRationalFormZero
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionFamilyOf
public import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Forms NumberField Classical Formalism.UG IsDedekindDomain

section Gen

variable {ι : Type} [Fintype ι] {n : ℕ}

variable {K : Type} [Field K]

end Gen

section Transport

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Transport

section Reps

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Reps

section Norms

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Norms

section Iso

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Iso

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
