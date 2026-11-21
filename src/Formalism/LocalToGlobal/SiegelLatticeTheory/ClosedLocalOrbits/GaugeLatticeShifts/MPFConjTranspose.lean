import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.VolumeZeroFintype
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

section PFm

variable {ι : Type*}






def MPF {α β : Type*} (M : (ι → ℝ) → Matrix α β ℂ) : Prop := ∀ i j, (fun y => M y i j) ∈ PF ι

variable {α β γ : Type*}











end PFm

section Coords

variable {ι : Type*} {n r : ℕ}


theorem hJ_eq_sum (ε : Fin n → Bool) (x v : Fin n → ℂ) :
    hJ ε x v = ∑ i, (star x ᵥ* Formalism.REAL.Jm ε) i * v i := by
  unfold hJ
  rw [Matrix.dotProduct_mulVec]
  rfl




def Fval (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℂ :=
  (∏ l ∈ Finset.Icc 1 r, Dl Z l) * (Gv T T' Z : ℂ)


def Qexpr (T T' : ℝ) (Z0 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (d : ℂ) : ℂ :=
  (∏ l ∈ Finset.Icc 1 r, Dl Z0 l) *
    (Dl Z0 (r + 1) * conj (Dl Z0 (r + 1)) - ((T * T' : ℝ) : ℂ) * (d * conj d) * (Dl Z0 r * conj (Dl Z0 r)))



end Coords

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
