import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def kgT : Lie E a →ₗ[ℝ] ℂ where
  toFun X := ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)
  map_add' X Y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← coordL_apply, map_smul, coordL_apply]

theorem kgT_apply (X : Lie E a) : kgT X = ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) := rfl

def kgH : Herm E a →ₗ[ℝ] Lie E a where
  toFun X := toL X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kgT_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : kgT (toL (X * Y - Y * X)) = 0 := by
  have h : ∀ τ : E →+* ℂ, ∑ i, coord τ ((X * Y - Y * X) i i) = coord τ (Matrix.trace (X * Y - Y * X)) := by
    intro τ; simp only [Matrix.trace, Matrix.diag, map_sum]
  change ∑ τ : E →+* ℂ, ∑ i, coord τ ((X * Y - Y * X) i i) = 0
  simp only [h, Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, map_zero, Finset.sum_const_zero]

variable [IsTotallyComplex E]

theorem kgT_star (X : Lie E a) : star (kgT X) = kgT X := by
  rw [kgT_apply, star_sum]
  simp_rw [star_sum, ← J.coord_conjugate]
  exact Fintype.sum_equiv (Function.Involutive.toPerm _ fun τ => star_star τ) _ _ fun τ => rfl

omit [NumberField E] [IsTotallyComplex E] in
theorem kg_coord_atEmb_self (τ : E →+* ℂ) (z : ℂ) : coord τ (atEmb τ z) = z := by
  rw [J.coord_eq]
  unfold atEmb
  split_ifs <;> simp_all

omit [NumberField E] [IsTotallyComplex E] in
theorem kg_coord_atEmb_of_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  classical
  rw [J.coord_eq]
  unfold atEmb
  split_ifs <;> simp only [Pi.single_eq_of_ne h, map_zero]

theorem kg_sum_coord_atEmb (τ : E →+* ℂ) (z : ℂ) :
    ∑ τ' : E →+* ℂ, coord τ' (atEmb τ z) = z + starRingEnd ℂ z := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := by
    intro h
    have h1 : (InfinitePlace.mk τ).IsReal :=
      InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1
  rw [Fintype.sum_eq_add τ (ComplexEmbedding.conjugate τ) hne.symm, J.coord_conjugate, kg_coord_atEmb_self]
  · rfl
  · rintro τ' ⟨h1, h2⟩
    refine kg_coord_atEmb_of_ne (fun h => ?_) z
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact h1 h
    · exact h2 (by rw [← h]; exact (star_star τ').symm)

theorem cx_kgT (τ : E →+* ℂ) (i j : Fin a) : cx τ (kgT (E := E) (a := a)) i j = if i = j then 1 else 0 := by
  have h : ∀ z : ℂ, kgT (toL (Matrix.single i j (atEmb τ z))) = if i = j then z + starRingEnd ℂ z else 0 := by
    intro z
    rw [kgT_apply]
    split_ifs with hij
    · subst hij
      rw [← kg_sum_coord_atEmb τ z]
      refine Finset.sum_congr rfl fun τ' _ => ?_
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    · refine Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun k _ => ?_
      simp only [toL]
      rw [Matrix.of_symm_apply, Matrix.single_apply]
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) hij
      · exact map_zero _
  unfold cx
  rw [h, h]
  split_ifs <;> norm_num [Complex.conj_I]

end
end PositivityTheory.Rg.Cz
end
end

section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def kgA (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lieOp π X).rTensor _ + (-(σ / 2 : ℂ) * kgT X) • 1
  map_add' X Y := by rw [map_add, LinearMap.rTensor_add, map_add, mul_add, add_smul]; abel
  map_smul' c X := by
    have e1 : lieOp π (c • X) = (c : ℂ) • lieOp π X := by rw [map_smul, ← algebraMap_smul ℂ c]; rfl
    have e2 : kgT (c • X) = (c : ℂ) * kgT X := by rw [map_smul, Complex.real_smul]
    simp only [RingHom.id_apply]
    rw [e1, e2, LinearMap.rTensor_smul, ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))),
      show algebraMap ℝ ℂ c = (c : ℂ) from rfl]
    module

def kgR (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (Matrix.toLin' (Ξ.dmat X)).lTensor _ + ((σ / 2 : ℂ) * kgT X) • 1
  map_add' X Y := by rw [map_add, map_add, LinearMap.lTensor_add, map_add, mul_add, add_smul]; abel
  map_smul' c X := by
    have e1 : Ξ.dmat (c • X) = (c : ℂ) • Ξ.dmat X := by rw [map_smul, ← algebraMap_smul ℂ c]; rfl
    have e2 : kgT (c • X) = (c : ℂ) * kgT X := by rw [map_smul, Complex.real_smul]
    simp only [RingHom.id_apply]
    rw [e1, e2, map_smul, LinearMap.lTensor_smul, ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))),
      show algebraMap ℝ ℂ c = (c : ℂ) from rfl]
    module

variable (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ)

theorem kgA_apply (X : Lie E a) : kgA π Ξ σ X = (lieOp π X).rTensor _ + (-(σ / 2 : ℂ) * kgT X) • 1 := rfl

theorem kgR_apply (X : Lie E a) :
    kgR π Ξ σ X = (Matrix.toLin' (Ξ.dmat X)).lTensor _ + ((σ / 2 : ℂ) * kgT X) • 1 := rfl

theorem kgA_add_kgR (X : Lie E a) : kgA π Ξ σ X + kgR π Ξ σ X = tensorLie π Ξ X := by
  rw [kgA_apply, kgR_apply]
  show _ = (lieOp π X).rTensor _ + (Matrix.toLin' (Ξ.dmat X)).lTensor _
  rw [add_add_add_comm, ← add_smul, neg_mul, neg_add_cancel, zero_smul, add_zero]

theorem kg_lieOp_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    lieOp π (toL X) * lieOp π (toL Y) - lieOp π (toL Y) * lieOp π (toL X) = lieOp π (toL (X * Y - Y * X)) := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  have h := LinearMap.congr_fun (lie_comm (E := E) (a := a) (toL X) (toL Y)) φ.1
  have e : toL (X * Y - Y * X) =
      toL (Matrix.of (toL X) * Matrix.of (toL Y)) - toL (Matrix.of (toL Y) * Matrix.of (toL X)) := rfl
  rw [e, map_sub]
  exact h

theorem kgA_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    kgA π Ξ σ (toL X) * kgA π Ξ σ (toL Y) - kgA π Ξ σ (toL Y) * kgA π Ξ σ (toL X) = kgA π Ξ σ (toL (X * Y - Y * X)) := by
  have e : kgA π Ξ σ (toL (X * Y - Y * X)) = (lieOp π (toL (X * Y - Y * X))).rTensor _ := by
    rw [kgA_apply, kgT_comm]; simp
  rw [e, ← kg_lieOp_comm, LinearMap.rTensor_sub, LinearMap.rTensor_mul, LinearMap.rTensor_mul, kgA_apply, kgA_apply]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

theorem kgR_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    kgR π Ξ σ (toL X) * kgR π Ξ σ (toL Y) - kgR π Ξ σ (toL Y) * kgR π Ξ σ (toL X) = kgR π Ξ σ (toL (X * Y - Y * X)) := by
  have e : kgR π Ξ σ (toL (X * Y - Y * X)) = (Matrix.toLin' (Ξ.dmat (toL (X * Y - Y * X)))).lTensor _ := by
    rw [kgR_apply, kgT_comm]; simp
  rw [e, ← GlobalTheory.AlgInfChar.dmat_bracket,
    map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.lTensor_sub, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp, LinearMap.lTensor_mul, LinearMap.lTensor_mul, kgR_apply, kgR_apply]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

theorem kgA_kgR_comm (X Y : Lie E a) : Commute (kgA π Ξ σ X) (kgR π Ξ σ Y) := by
  have h : Commute ((lieOp π X).rTensor (Fin Ξ.d → ℂ) : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))
      ((Matrix.toLin' (Ξ.dmat Y)).lTensor π.V) := by
    show _ * _ = _ * _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [kgA_apply, kgR_apply]
  refine Commute.add_left ?_ ?_
  · refine Commute.add_right h ?_
    exact (Commute.one_right _).smul_right _
  · exact (Commute.one_left _).smul_left _

theorem cx_kgA (τ : E →+* ℂ) (i j : Fin a) :
    cx τ (kgA π Ξ σ) i j = (cx τ (lieOp π) i j).rTensor _ + (if i = j then -(σ / 2 : ℂ) else 0) • 1 := by
  have h := cx_kgT (E := E) (a := a) τ i j
  have e : (if i = j then -(σ / 2 : ℂ) else 0) = -(σ / 2 : ℂ) * cx τ (kgT (E := E) (a := a)) i j := by
    rw [h]; split_ifs <;> simp
  rw [e]
  simp only [cx, kgA_apply, LinearMap.rTensor_sub, LinearMap.rTensor_smul, smul_eq_mul]
  module

theorem cx_kgR (τ : E →+* ℂ) (i j : Fin a) :
    cx τ (kgR π Ξ σ) i j = (Matrix.toLin' (cx τ Ξ.dmat i j)).lTensor _ + (if i = j then (σ / 2 : ℂ) else 0) • 1 := by
  have h := cx_kgT (E := E) (a := a) τ i j
  have e : (if i = j then (σ / 2 : ℂ) else 0) = (σ / 2 : ℂ) * cx τ (kgT (E := E) (a := a)) i j := by
    rw [h]; split_ifs <;> simp
  rw [e]
  simp only [cx, kgR_apply, map_sub, map_smul, LinearMap.lTensor_sub, LinearMap.lTensor_smul, smul_eq_mul]
  module

end
end PositivityTheory.Rg.Cz
end
end
