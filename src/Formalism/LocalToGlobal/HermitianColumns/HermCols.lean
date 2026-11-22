module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory in
def VolumeCompatible (D : D7) : Prop :=
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) →
    ∀ μ, Formalism.MainNotions.StandardLattice.IsVolMeas D W P Q μ →
    ∀ 𝓕, IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
      μ 𝓕 = ENNReal.ofReal (D.vol W)

end Formalism.L2.Herm

end
