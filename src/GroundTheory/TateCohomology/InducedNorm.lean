import Mathlib

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology groupHomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def TateAcyclic (M : Rep.{u} k G) : Prop := ∀ n : ℤ, IsZero (tateCohomology M n)

theorem TateAcyclic.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : TateAcyclic N) : TateAcyclic M := fun n => by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 ((tateCohomologyFunctor n).obj M) = 0
  rw [← (tateCohomologyFunctor n).map_id, ← h, Functor.map_comp,
    (hN n).eq_of_tgt ((tateCohomologyFunctor n).map i) 0, zero_comp]

theorem TateAcyclic.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : TateAcyclic N) :
    TateAcyclic M :=
  hN.of_retract e.hom e.inv e.hom_inv_id

theorem isZero_tateCohomology_zero_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, (∀ g : G, M.ρ g m = m) → ∃ y : M, M.ρ.norm y = m) :
    IsZero (tateCohomology M 0) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousCochains M).X 0, (inhomogeneousCochains M).d 0 1 x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 0, M.tateNorm x₁ = x₂
  intro x₂ hd
  have hinv : ∀ g : G, M.ρ g ((cochainsIso₀ M).hom x₂) = (cochainsIso₀ M).hom x₂ := by
    intro g
    have key : (d₀₁ M).hom ((cochainsIso₀ M).hom.hom x₂) =
        (cochainsIso₁ M).hom.hom (((inhomogeneousCochains M).d 0 1).hom x₂) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, comp_d₀₁_eq]; rfl
    rw [show ((inhomogeneousCochains M).d 0 1).hom x₂ = 0 from hd, map_zero] at key
    have := congr_fun key g
    exact sub_eq_zero.mp this
  obtain ⟨y, hy⟩ := h _ hinv
  refine ⟨(chainsIso₀ M).inv y, ?_⟩
  simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change (cochainsIso₀ M).inv (M.ρ.norm y) = x₂
  rw [hy, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_neg_one_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, M.ρ.norm m = 0 → ∃ z : G →₀ M, d₁₀ M z = m) :
    IsZero (tateCohomology M (-1)) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousChains M).X 0, M.tateNorm x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 1, (inhomogeneousChains M).d 1 0 x₁ = x₂
  intro x₂ hx
  have hn : M.ρ.norm ((chainsIso₀ M).hom x₂) = 0 := by
    have := congr_arg (fun x => (cochainsIso₀ M).hom x) hx
    simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, map_zero] at this
    exact this
  obtain ⟨z, hz⟩ := h _ hn
  refine ⟨(chainsIso₁ M).inv z, ?_⟩
  rw [eq_d₁₀_comp_inv_apply, hz, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_zero_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M 0) := by
  refine isZero_tateCohomology_zero_of_forall M fun m hm => ⟨φ m, ?_⟩
  rw [Representation.norm, LinearMap.sum_apply]
  conv_rhs => rw [← hφ m]
  simp only [hm]

theorem isZero_tateCohomology_neg_one_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M (-1)) := by
  refine isZero_tateCohomology_neg_one_of_forall M fun m hm =>
    ⟨∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m)), ?_⟩
  have hsum : ∑ g : G, M.ρ g⁻¹ m = M.ρ.norm m := by
    rw [Representation.norm, LinearMap.sum_apply]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
  show (Finsupp.lsum k fun g : G => M.ρ g⁻¹ - LinearMap.id)
    (∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m))) = m
  simp only [map_sum, Finsupp.lsum_single, LinearMap.sub_apply, LinearMap.id_apply, inv_inv]
  rw [Finset.sum_sub_distrib, ← map_sum, hsum, hm, map_zero, sub_zero, hφ]

section Coind

variable (B : Rep.{u} k (⊥ : Subgroup G))

open scoped Classical in

noncomputable def coindBotProj :
    (coind (⊥ : Subgroup G).subtype B).V →ₗ[k] (coind (⊥ : Subgroup G).subtype B).V :=
  LinearMap.codRestrict _ ((LinearMap.single k (fun _ : G => B.V) 1) ∘ₗ LinearMap.proj 1 ∘ₗ
    (Representation.coindV (⊥ : Subgroup G).subtype B.ρ).subtype) fun f => by
      rw [Representation.mem_coindV]
      intro s x
      obtain rfl : s = 1 := Subsingleton.elim _ _
      simp

open scoped Classical in

theorem sum_coindBotProj (f : coind (⊥ : Subgroup G).subtype B) :
    ∑ g : G, (coind (⊥ : Subgroup G).subtype B).ρ g
      (coindBotProj B ((coind (⊥ : Subgroup G).subtype B).ρ g⁻¹ f)) = f := by
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  change ∑ g : G, (Pi.single (M := fun _ : G => B.V) (1 : G) (f.1 (1 * g⁻¹)) (x * g)) = f.1 x
  rw [Fintype.sum_eq_single x⁻¹]
  · simp
  · intro g hg
    rw [Pi.single_apply, if_neg]
    exact fun h => hg (eq_inv_of_mul_eq_one_right h)

theorem isZero_tateCohomology_coind_bot (n : ℤ) :
    IsZero (tateCohomology (coind (⊥ : Subgroup G).subtype B) n) := by
  classical
  rcases n with (_ | n) | (_ | n)
  · exact isZero_tateCohomology_zero_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · exact ((isZero_groupCohomology_succ_of_subsingleton B n).of_iso (coindIso B (n + 1))).of_iso
      ((TateCohomology.isoGroupCohomology (n + 1)).app _)
  · exact isZero_tateCohomology_neg_one_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · have e := (TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
      (by simp [Int.negSucc_eq])).app (coind (⊥ : Subgroup G).subtype B)
    refine (((isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (indIso (⊥ : Subgroup G) B (n + 1))).of_iso ?_).of_iso e
    exact (groupHomology.functor k G (n + 1)).mapIso (indCoindIso B).symm

theorem isZero_tateCohomology_ind_bot (n : ℤ) :
    IsZero (tateCohomology (ind (⊥ : Subgroup G).subtype B) n) := by
  classical
  exact (isZero_tateCohomology_coind_bot B n).of_iso
    ((tateCohomologyFunctor n).mapIso (indCoindIso B))

theorem tateAcyclic_coind_bot : TateAcyclic (coind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_coind_bot B

theorem tateAcyclic_ind_bot : TateAcyclic (ind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_ind_bot B

end Coind

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Criterion

variable (M : Rep.{u} k G)

noncomputable def toCoindRes :
    M ⟶ coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M) :=
  ofHom ⟨LinearMap.codRestrict _ (LinearMap.pi fun x : G => M.ρ x) fun m => by
      rw [Representation.mem_coindV]
      intro s x
      simp [map_mul],
    fun g => LinearMap.ext fun m => by
      apply Subtype.ext
      funext x
      change M.ρ x (M.ρ g m) = M.ρ (x * g) m
      rw [map_mul, Module.End.mul_apply]⟩

noncomputable def fromCoindRes (φ : M.V →ₗ[k] M.V) :
    coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M) ⟶ M :=
  ofHom ⟨∑ x : G, M.ρ x⁻¹ ∘ₗ φ ∘ₗ LinearMap.proj x ∘ₗ
      (Representation.coindV (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M).ρ).subtype,
    fun g => LinearMap.ext fun f => by
      simp only [LinearMap.coe_comp, LinearMap.coe_sum, Function.comp_apply, Finset.sum_apply,
        map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun x => ?_
      change M.ρ x⁻¹ (φ (f.1 (x * g))) = M.ρ g (M.ρ (x * g)⁻¹ (φ (f.1 (x * g))))
      rw [← Module.End.mul_apply (M.ρ g) (M.ρ (x * g)⁻¹), ← map_mul, mul_inv_rev,
        mul_inv_cancel_left]⟩

theorem toCoindRes_fromCoindRes (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    toCoindRes M ≫ fromCoindRes M φ = 𝟙 M := by
  ext m
  change (fromCoindRes M φ).hom.toLinearMap ((toCoindRes M).hom.toLinearMap m) = m
  refine (LinearMap.sum_apply _ _ _).trans ?_
  change ∑ x : G, M.ρ x⁻¹ (φ (M.ρ x m)) = m
  conv_rhs => rw [← hφ m]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun x => by simp

theorem tateAcyclic_of_sum_eq (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : TateAcyclic M :=
  (tateAcyclic_coind_bot _).of_retract _ _ (toCoindRes_fromCoindRes M φ hφ)

end Criterion

section Tensor

omit [Fintype G] in

noncomputable def coeffOneProj : MonoidAlgebra k G →ₗ[k] MonoidAlgebra k G :=
  MonoidAlgebra.lsingle 1 ∘ₗ Finsupp.lapply 1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

omit [Fintype G] in

theorem coeffOneProj_apply (x : MonoidAlgebra k G) :
    coeffOneProj x = MonoidAlgebra.single 1 (x.coeff 1) := rfl

variable (B : Rep.{u} k G)

theorem sum_leftRegular_tensor (t : (leftRegular k G ⊗ B : Rep k G)) :
    ∑ g : G, (leftRegular k G ⊗ B).ρ g
      (TensorProduct.map coeffOneProj LinearMap.id ((leftRegular k G ⊗ B).ρ g⁻¹ t)) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | tmul x b =>
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib, hx, hy]
    | single h c =>
      rw [Fintype.sum_eq_single h]
      · simp [Rep.tensor_ρ, coeffOneProj_apply]
      · intro g hg
        have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
        simp [Rep.tensor_ρ, coeffOneProj_apply, this]

theorem tateAcyclic_leftRegular_tensor : TateAcyclic (leftRegular k G ⊗ B) :=
  tateAcyclic_of_sum_eq _ (TensorProduct.map coeffOneProj LinearMap.id) (sum_leftRegular_tensor B)

theorem tateAcyclic_leftRegular_tensor_trivial (V : Type u) [AddCommGroup V] [Module k V] :
    TateAcyclic (leftRegular k G ⊗ trivial k G V) :=
  tateAcyclic_leftRegular_tensor _

theorem tateAcyclic_leftRegular : TateAcyclic (leftRegular k G) :=
  (tateAcyclic_leftRegular_tensor (𝟙_ (Rep k G))).of_iso (ρ_ (leftRegular k G)).symm

theorem tateAcyclic_free (α : Type u) : TateAcyclic (free k G α) := by
  classical
  exact (tateAcyclic_leftRegular_tensor_trivial _).of_iso (leftRegularTensorTrivialIsoFree k G α).symm

end Tensor

section Free

variable (M : Rep.{u} k G)

end Free

end GroundTheory.GroupCoh
end
