import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExists

section
noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.IdCell

section Basics

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem fvec_castSucc (F : FlagG S r T) (k : Fin r) : F.fvec k.castSucc = F.e k := by
  simp [FlagG.fvec]

theorem fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi h : i.1 < b))

theorem e_mem_Xa (F : FlagG S r T) {k : Fin r} {a : ℕ} (hk : k.val < a) : F.e k ∈ F.Xa a := Submodule.subset_span ⟨k, hk, rfl⟩

theorem Xa_r (F : FlagG S r T) : F.Xa r = F.X := by
  simp [FlagG.Xa, FlagG.X]




theorem hT_e_X (F : FlagG S r T) (j : Fin r) : ∀ y ∈ F.X, S.hT (F.e j) y = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT (F.e j)) :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact F.e_iso j k)
  intro y hy
  exact LinearMap.mem_ker.1 (h1 hy)

theorem hT_X_X (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT.flip y) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hT_e_X F j y hy)
  simpa using h1 hx

theorem hT_X_alt (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT x F.z = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT.flip F.z) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact F.z_orth j)
  simpa using h1 hx


theorem fvec_indep (F : FlagG S r T) (hT0 : T ≠ 0) : LinearIndependent E F.fvec := by
  rw [FlagG.fvec, linearIndependent_fin_snoc]
  refine ⟨F.e_indep, fun hz => hT0 ?_⟩
  have h1 := hT_X_alt F hz
  rw [F.z_norm] at h1
  exact neg_eq_zero.1 h1


end Basics

section TwoFlags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}






end TwoFlags

end PI.FRS
end
end

section
noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.IdCell

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}





end PI.FRS
end
end

section
noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.IdCell


end PI.FRS
end
end
