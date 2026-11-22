module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
open GroundTheory.Heights₂.Heights

universe u v w

noncomputable section

def BaseChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type w) [Field L] [NumberField L] [Algebra K L]
    (M : HermitianBundle.{v} K), (M.baseChange L).deg = M.deg

section Witnesses

variable (K : Type u) [Field K] [NumberField K]

end Witnesses

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
