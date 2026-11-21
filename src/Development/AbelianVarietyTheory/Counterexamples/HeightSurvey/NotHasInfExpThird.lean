import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.VolHeckeCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar











theorem isWittLower_self (D : D7) (V : HSp D) : IsWittLower V V 0 := by
  refine ⟨rfl, LinearMap.id, fun _ _ => rfl, 0, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

theorem isomEmb_inj (D : D7) (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) (h : HSpace.IsIsomEmb V' V ι) :
    Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply V'.nondeg.1
  intro y
  rw [← h x y, hx]
  simp

end GlobalTheory.VolHeckeCheck

end
