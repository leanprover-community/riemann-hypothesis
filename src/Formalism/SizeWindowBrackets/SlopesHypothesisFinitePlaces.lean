module

public import Mathlib
public import Formalism.HarderNarasimhan.StatementPl
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

open Module NumberField

noncomputable section

namespace Formalism.LFunctionChainParameters.slopeLatticeData

open Formalism.HN

abbrev FinPl (K : Type) [Field K] [NumberField K] := {p : Ideal (𝓞 K) // p.IsMaximal}

def lenAt {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (w : FinPl K) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  haveI := w.2.isPrime
  Module.length (Localization.AtPrime w.1)
    (LocalizedModule w.1.primeCompl (A ⧸ B.comap A.subtype))

end Formalism.LFunctionChainParameters.slopeLatticeData
