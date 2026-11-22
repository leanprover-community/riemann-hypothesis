module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataParamsT

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField Matrix
open scoped ComplexOrder

variable {R : Ranks}

abbrev Pl (R : Ranks) : Type := ↥(R.Psi)

instance instFintypePl : Fintype (Pl R) := Fintype.ofFinite _

def tau (H : Host R) (τ : Pl R) : H.E →+* ℂ := H.emb τ.1

variable {H : Host R} {n : ℕ}

end GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents

end
