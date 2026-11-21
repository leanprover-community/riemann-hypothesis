import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h0 : symplOH S T w 0 = 0 := by
    simp [symplOH, symplO, hO]
  simp [heisO, h0]

theorem redZero_holds : RedZero D := by
  intro ψ S T r C μ 𝓕 f
  simp only [Red, ellI, heisO_zero]




theorem hO_eq_zero_of (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (a : Mx D r S.rank)
    (y : WO S T) (hy : HMul.hMul (HMul.hMul (y.map (cA D)).transpose (Brg.GG T)) (C.map (incA D)) = 0) :
    hO S T (embI S T C a) y = 0 := by
  have hz : (y.map (cA D)).transpose * Brg.GG T * (C.map (incA D) * a) = 0 := by
    rw [← Matrix.mul_assoc, hy, Matrix.zero_mul]
  unfold hO embI
  refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ => ?_
  have e := congrFun (congrFun hz i2) i1
  generalize C.map (incA D) * a = X at e ⊢
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    Matrix.zero_apply] at e

  have e2 : ∑ i3, ∑ i4, (cA D) (y i3 i2) * (incA D) (HSpace.gram T i3 i4) * X i4 i1 = 0 := by
    rw [Finset.sum_comm]
    exact e
  calc _ = (incA D) ((HSpace.gram S)⁻¹ i1 i2) *
        ∑ i3, ∑ i4, (cA D) (y i3 i2) * (incA D) (HSpace.gram T i3 i4) * X i4 i1 := by
        simp only [Finset.mul_sum, mul_assoc]
    _ = 0 := by rw [e2, mul_zero]







instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

instance tagMx (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin m → Fin n → AE D))

instance measAddMx (m n : ℕ) : MeasurableAdd (Mx D m n) :=
  ⟨fun _ => (continuous_const.add continuous_id).measurable, fun _ => (continuous_id.add continuous_const).measurable⟩

theorem countable_ratMx (m n : ℕ) : Countable (ratMx D m n) := by
  haveI : Countable D.host.E :=
    Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.symm.toEquiv
  haveI : Countable (Matrix (Fin m) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin m → Fin n → D.host.E))
  unfold ratMx
  have hs : Function.Surjective (fun x : Matrix (Fin m) (Fin n) D.host.E =>
      (⟨_, AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ :
        ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hy
    exact ⟨x, rfl⟩
  exact hs.countable







end Formalism.IndefR.Eqv

end
end

section
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
end
