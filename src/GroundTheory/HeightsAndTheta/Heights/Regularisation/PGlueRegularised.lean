module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedGlue

@[expose] public section

namespace GroundTheory.Heights₂.Heights.Regular

noncomputable section

theorem GlueRegularised.proof : GlueRegularised.Statement :=
  fun _ _ _ _ _ _ R ρ η _ K _ _ hcut ht hε hball hcmp =>
    R.glue_smooth_and_levi (R.smoothed ρ K _) η hcut hε
      (fun j x hx => R.smoothed_local ρ K ht j (hball j x (subset_closure hx))) hcmp

end

end GroundTheory.Heights₂.Heights.Regular
