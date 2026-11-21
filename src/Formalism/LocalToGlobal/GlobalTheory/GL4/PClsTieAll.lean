import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieP

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FramesP {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) : Prop :=
  ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
    (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' ((X.atT u).lattice₂ c)) ∧
    ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls D.sp.X' (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) ((X.atT u).lattice₂ c)
      ((X.atT u).lattice₂ c') (e c) (e c') → c = c'




end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
