module

public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

def PsiOpenP : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∃ G : AddSubgroup (Af F), IsOpen (G : Set (Af F)) ∧ (∀ y ∈ G, ∀ z ∈ Ohat F, z * y ∈ G) ∧
      ∀ y ∈ G, ψ (pairA F 0 y) = 1

def PsiSmoothP : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (k : ℕ) (s : (Fin k → ℝ) →+ Ainf D.host.F), Continuous s →
      ContDiff ℝ ∞ fun t => ψ (pairA D.host.F (s t) 0)

end Formalism.IndefR.PHeisTh

end
