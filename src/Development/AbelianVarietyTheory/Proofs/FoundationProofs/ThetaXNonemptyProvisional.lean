import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory

namespace GlobalTheory

namespace ThetaProv

section Incl

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def coordIncl (a b : ℕ) : (Fin a → E) →ₗ[E] (Fin b → E) where
  toFun x := fun i => if h : (i : ℕ) < a then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp


end Incl

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end ThetaProv

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory

end
