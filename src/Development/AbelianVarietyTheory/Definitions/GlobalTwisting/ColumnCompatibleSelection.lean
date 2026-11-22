module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SquareIntegrableColumnsCompatible
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top

namespace GlobalTheory.Cp

end GlobalTheory.Cp

namespace GlobalTheory.Fc

open GlobalTheory.Cp

def zsc {D : D7} {O : Obj D} (P : Formalism.L2.Rows.RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) :
    Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D O.L Del h0) (Equiv.refl _) O.L.Nc Zs
    { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }

variable {𝒜 : FamClass} (σ : RawSel Bundle 𝒜)

end GlobalTheory.Fc

end
