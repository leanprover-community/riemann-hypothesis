import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedLem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def PhiM (m n : ℕ) (x : Mx D m n) : Fin m → Fin n → Fin (nE D) → AF D.host.F :=
  fun i j => cE D.host.F D.host.E (x i j)



theorem cont_PhiM (m n : ℕ) (i j k) : Continuous fun x : Mx D m n => PhiM m n x i j k :=
  (continuous_apply k).comp ((cE D.host.F D.host.E).continuous.comp (continuous_id.matrix_elem i j))

def FDM (D : D7) (m n : ℕ) : Set (Mx D m n) := {x | ∀ i j k, PhiM m n x i j k ∈ F0 D.host.F}


open scoped Classical in
theorem meas_FDM (m n : ℕ) : MeasurableSet (FDM D m n) := by
  have h : FDM D m n = ⋂ i, ⋂ j, ⋂ k,
      ((fun x => eM D.host.F (PhiM m n x i j k).1) ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis D.host.F) ∩
        (fun x => (PhiM m n x i j k).2) ⁻¹' Ohat D.host.F) := by
    ext x; simp [FDM, F0, Pinf]
  rw [h]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => ?_
  refine MeasurableSet.inter ?_ ?_
  · exact ((continuous_eM _).comp (continuous_fst.comp (cont_PhiM m n i j k))).measurable (measurableSet_Pinf _)
  · exact ((isOpen_Ohat _).preimage (continuous_snd.comp (cont_PhiM m n i j k))).measurableSet


instance lcMx (m n : ℕ) : LocallyCompactSpace (Mx D m n) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AE D))



end Formalism.IndefR.Eqv

end
