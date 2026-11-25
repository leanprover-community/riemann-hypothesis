module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

def SmulSD (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    SD D L → SD D (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)

def NormOneUnitIdeal (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ z : unitary D.host.E, TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)})

end Formalism.L2.PairingIndexBounds.Eq
