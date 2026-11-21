import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieIdx
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieInt
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieSep

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar


def FramesStep (D : D7) (u : D.what₂.Word) (i : ℕ) : Prop :=
  ∃ e : (D.mem u).C.cls i → Fin (D.R.N i) → (D.sp.X i).V,
    (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub (D.sp.X i) (D.clsLat u i c)) ∧
    ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls (D.sp.X i) (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) (D.clsLat u i c)
      (D.clsLat u i c') (e c) (e c') → c = c'

def ClauseP (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ LP : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V,
    (∀ c, Submodule.IsLattice D.host.E (LP c) ∧ Formalism.MainNotions.flipTwoThree.LatT D.sp.X' 1 (LP c)) ∧
    ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
      (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' (LP c)) ∧
      ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls D.sp.X' (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) (LP c) (LP c') (e c) (e c') →
        c = c'


end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
