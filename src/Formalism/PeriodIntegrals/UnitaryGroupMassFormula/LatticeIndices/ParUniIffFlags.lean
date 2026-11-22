module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.RowFlagIff

@[expose] public section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni isUpUni_inv isUpUni_det)

variable {K : Type} [Field K] {r k : ℕ}

def posW (i : Fin k) : Set (Idx r k) := Set.range Sum.inl ∪ wI '' {j | j < i}

def ColW (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ i : Fin k, m *ᵥ Pi.single (wI i) 1 - Pi.single (wI i) 1 ∈
    Submodule.span K ((fun j => Pi.single j (1 : K)) '' posW (r := r) i)

end MassDataIdxStIm
