module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipReal
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat

@[expose] public section

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section RatEl

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem cT_eq {m p : Type} (M : Matrix m p X.B.I.E) : Formalism.UG.cT (starRingEnd X.B.I.E) M = Mᴴ := by
  ext i j
  simp only [Formalism.UG.cT, conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  rfl

end RatEl
