import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.PropLoc

universe u

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

theorem smul_bij {O V : Type u} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (c : O) (hc : c ≠ 0) :
    Function.Bijective fun v : V => c • v := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using hc
  constructor
  · intro v w h
    have h' : algebraMap O (FractionRing O) c • v = algebraMap O (FractionRing O) c • w := by
      simpa only [algebraMap_smul] using h
    exact smul_right_injective V hc' h'
  · intro v
    refine ⟨(algebraMap O (FractionRing O) c)⁻¹ • v, ?_⟩
    show c • _ = v
    rw [← algebraMap_smul (FractionRing O) c, smul_smul, mul_inv_cancel₀ hc', one_smul]



end Formalism.RepresentationBoundsCohomology.LOC
