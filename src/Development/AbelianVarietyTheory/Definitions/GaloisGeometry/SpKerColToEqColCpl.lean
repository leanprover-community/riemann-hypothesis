module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumFibreEqSumOrbits
public import Formalism.LocalToGlobal.KernelLattices.ThDistC

@[expose] public section

noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

variable {K : Type} [Field K] [NumberField K] [StarRing K]

attribute [instance] MemOn.grpG MemOn.actD

namespace SpIdx

variable {β : ℕ → Type} {n m i : ℕ}

end SpIdx

section Splice

variable (F : ℕ → GFam K) (n m : ℕ) (C : MemOn (F (n + 1))) (T : MemOn (F m))

variable {F n m C T}

variable (kk : KerFam F) (k1 : ∀ al : (F n).β, ClsKer ((F n).mem al) C.gsd) (k2 : ClsKer C.gsd T.gsd)

variable {hS : ∀ i, (spFam F n m C T i).Ok}

end Splice

end GlobalTheory.GO
