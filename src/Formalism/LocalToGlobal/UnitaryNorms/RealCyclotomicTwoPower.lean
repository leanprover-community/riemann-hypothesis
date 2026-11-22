module

public import Mathlib
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.FrobeniusOrbits.HostDiffSupport

@[expose] public section

noncomputable section

open IntermediateField NumberField

namespace Formalism.L2.Host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

abbrev Qb : Type := AlgebraicClosure ℚ

abbrev Fld : Type := IntermediateField ℚ Qb

def sqrts (m : ℤ) : Set Qb := {z | z ^ 2 = (m : Qb)}

def mus (N : ℕ) : Set Qb := {z | z ^ N = 1}

def sqQ (m : ℤ) : Fld := adjoin ℚ (sqrts m)

def cycQ (N : ℕ) : Fld := adjoin ℚ (mus N)

def KQ (d : ℕ) : Fld := sqQ (-(d : ℤ))

abbrev GalOf (L : Fld) : Subgroup (Qb ≃ₐ[ℚ] Qb) := L.fixingSubgroup

def IsCond (L : Fld) (N : ℕ) : Prop := L ≤ cycQ N ∧ ∀ M : ℕ, 0 < M → L ≤ cycQ M → N ∣ M

open Classical in
def sqSign {p : ℕ} (u : (ZMod p)ˣ) : ℤˣ := if IsSquare (u : ZMod p) then 1 else -1

end Formalism.L2.Host
