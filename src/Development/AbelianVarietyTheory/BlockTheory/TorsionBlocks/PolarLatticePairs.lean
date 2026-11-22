module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs

open NumberField IsDedekindDomain Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped Pointwise

def coefLat (D : D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ c ∈ cc, ∃ m ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    t = ((c : D.host.K) : D.host.E) * m}

def matIn (D : D7) (a d : ℕ) (A : Submodule (𝓞 D.host.E) D.host.E) :
    AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) where
  carrier := {z | ∀ i j, z i j ∈ A}
  zero_mem' := fun _ _ => A.zero_mem
  add_mem' := fun h₁ h₂ i j => A.add_mem (h₁ i j) (h₂ i j)
  neg_mem' := fun h i j => A.neg_mem (h i j)

abbrev lat0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (a d : ℕ) : AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) :=
  matIn D a d (coefLat D cc)

namespace PairDatum

variable {D : D7} (X : PairDatum D)

end PairDatum

end GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
