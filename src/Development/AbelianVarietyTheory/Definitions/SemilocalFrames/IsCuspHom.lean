module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

noncomputable section

namespace GlobalTheory.RowLev

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsCuspHom (I : AutInst) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {μf : Measure I.Gf} [SigmaFinite μf] {fund : Set I.GA} (A : Hs →L[ℂ] I.L2 μf fund) : Prop :=
  ∀ u, I.IsCuspFn (I.muA μf) (I.ext (A u))

end GlobalTheory.RowLev
