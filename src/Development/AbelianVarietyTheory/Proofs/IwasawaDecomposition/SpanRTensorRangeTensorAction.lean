import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import BuildAid.ForwardExisting

section
section
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory.EigenSplit

theorem baseChangeAction_toModuleEnd_self_apply {O R : Type} [CommRing O] [CommRing R] (a : O)
    (t : R ⊗[ℤ] O) :
    baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O) a t = t * (1 ⊗ₜ a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add s t hs ht => simp only [map_add, hs, ht, add_mul]

theorem eigenSub_eq_range_tensorAction_of_le_span {O R Λ : Type} [CommRing O] [CommRing R]
    [AddCommGroup Λ] [Module O Λ] [Module.Finite O Λ] [Module.Projective O Λ] (χ : O →+* R)
    (e : R ⊗[ℤ] O)
    (he : e ∈ eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ)
    (hspan : eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ
      ≤ Submodule.span R {e}) :
    eigenSub (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) χ
      = LinearMap.range
          (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) := by
  set ρO := (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)
  set ρ := (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)
  have hact : ∀ a, baseChangeAction R ρ a = tensorAction (baseChangeAction R ρ) (1 ⊗ₜ a) := by
    intro a; ext y; simp
  apply le_antisymm
  · intro x hx
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O Λ
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    let F : Fin n → R ⊗[ℤ] Λ →ₗ[R] R ⊗[ℤ] O := fun k =>
      (((LinearMap.proj k : (Fin n → O) →ₗ[O] O) ∘ₗ s).restrictScalars ℤ).baseChange R
    let lam : Fin n → Λ := fun k => π (Pi.single k 1)
    have hsum : ∀ l, ∑ k, s l k • lam k = l := by
      intro l
      have h1 := LinearMap.congr_fun hs l
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
      conv_rhs => rw [← h1]
      rw [← Finset.univ_sum_single (s l), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lam, ← map_smul]
      congr 1
      ext j
      by_cases hj : j = k <;> simp [Pi.single_apply, hj]
    have hid : ∀ y, y = ∑ k, tensorAction (baseChangeAction R ρ) (F k y) (1 ⊗ₜ lam k) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r l =>
        simp only [F, LinearMap.baseChange_tmul, tensorAction_tmul, baseChangeAction_apply,
          LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.proj_apply]
        simp [ρ, ← TensorProduct.tmul_sum, hsum, TensorProduct.smul_tmul']
      | add y z hy hz =>
        conv_lhs => rw [hy, hz]
        simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
    have hF : ∀ k, IsEquivariant (baseChangeAction R ρ) (baseChangeAction R ρO) (F k) := by
      intro k a y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r l => simp [F, ρ, ρO]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hc : ∀ k, ∃ c : R, c • e = F k x := fun k =>
      Submodule.mem_span_singleton.1 (hspan ((hF k).map_mem hx))
    choose c hc using hc
    refine ⟨∑ k, c k • (1 ⊗ₜ lam k), ?_⟩
    rw [map_sum]
    conv_rhs => rw [hid x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hc k, map_smul, map_smul, LinearMap.smul_apply]
  · rintro _ ⟨m, rfl⟩
    refine mem_eigenSub.2 fun a => ?_
    rw [hact a, ← Module.End.mul_apply, ← map_mul, mul_comm,
      ← baseChangeAction_toModuleEnd_self_apply, mem_eigenSub.1 he a, map_smul, LinearMap.smul_apply]

end GlobalTheory.EigenSplit
end

open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_rank_one_span : ∀ {O R Λ : Type} [CommRing O] [CommRing R] [AddCommGroup Λ] [Module O Λ] [Module.Finite O Λ]
    [Module.Projective O Λ] (χ : O →+* R) (e : R ⊗[ℤ] O),
    e ∈ eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ →
    eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ ≤ Submodule.span R {e} →
    eigenSub (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) χ
      = LinearMap.range (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) := by
  atlas_forward_decl GlobalTheory.EigenSplit.eigenSub_eq_range_tensorAction_of_le_span
end

section
section
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory

theorem rTensor_reduction_ne_zero_of_form_eq_one :
    ∀ {O R k : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Field k] [Module.Free ℤ O] [Module.Finite ℤ O]
    (ρ₀ : R →+* k), (∀ x, ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal R) → ∀ (e : R ⊗[ℤ] O)
    (f : R ⊗[ℤ] O →ₗ[R] R), f e = 1 → ρ₀.toIntAlgHom.toLinearMap.rTensor O e ≠ 0 := by
  intro O R k _ _ _ _ _ _ ρ₀ hρ e f hf hε
  classical
  let b := Module.Free.chooseBasis ℤ O
  have key : ∀ (z : R ⊗[ℤ] O) i,
      TensorProduct.equivFinsuppOfBasisRight b (ρ₀.toIntAlgHom.toLinearMap.rTensor O z) i
        = ρ₀ (TensorProduct.equivFinsuppOfBasisRight b z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp
    | add x y hx hy => simp [hx, hy]
  have hmem : ∀ i, TensorProduct.equivFinsuppOfBasisRight b e i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    apply hρ
    rw [← key, hε]
    simp
  have he : e = (TensorProduct.equivFinsuppOfBasisRight b e).sum
      (fun i m => m • ((1 : R) ⊗ₜ[ℤ] b i)) := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply e]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
    congr 1
    ext i m
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hf, he, map_finsuppSum]
    refine Ideal.sum_mem _ fun i _ => ?_
    simp only [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (hmem i)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)

end GlobalTheory
end

open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rTensor_residue_nonzero_of_split : ∀ {O R k : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Field k] [Module.Free ℤ O] [Module.Finite ℤ O]
    (ρ₀ : R →+* k), (∀ x, ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal R) → ∀ (e : R ⊗[ℤ] O)
    (f : R ⊗[ℤ] O →ₗ[R] R), f e = 1 → ρ₀.toIntAlgHom.toLinearMap.rTensor O e ≠ 0 := by
  atlas_forward_decl GlobalTheory.rTensor_reduction_ne_zero_of_form_eq_one
end

section
section
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory
namespace EigenSplit

section RankOne

variable {E : Type} [Field E] [NumberField E] {K : Type} [CommRing K]

theorem baseChangeAction_toModuleEnd_apply (a : 𝓞 E) (x : K ⊗[ℤ] 𝓞 E) :
    baseChangeAction K (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E)) a x
      = (1 ⊗ₜ a) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

theorem tensorAction_baseChangeAction_toModuleEnd (t x : K ⊗[ℤ] 𝓞 E) :
    tensorAction (baseChangeAction K
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) t x = t * x := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [tensorAction_tmul, baseChangeAction_toModuleEnd_apply, ← smul_mul_assoc,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add s t hs ht => simp [add_mul, hs, ht]

variable {ι : Type} [DecidableEq ι] {τ : ι → 𝓞 E →+* K}

theorem idem_ne_zero [Nontrivial K] (h : IsSplitting τ) (i : ι) : idem h i ≠ 0 := by
  intro h0
  have := congrFun (splitMap_idem h i) i
  rw [h0, map_zero] at this
  simp at this

theorem eigenSub_toModuleEnd_eq_span (h : IsSplitting τ) (i : ι) :
    eigenSub (baseChangeAction K (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E)))
      (τ i) = Submodule.span K {idem h i} := by
  apply le_antisymm
  · intro x hx
    have h1 := tensorAction_of_mem (σ := τ) hx (idem h i)
    rw [tensorAction_baseChangeAction_toModuleEnd, splitMap_idem, Pi.single_eq_same, one_smul,
      mul_comm, mul_idem] at h1
    rw [← h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact mem_eigenSub.2 fun a => by rw [baseChangeAction_toModuleEnd_apply, one_tmul_mul_idem]

end RankOne

theorem finrank_eigenSub_toModuleEnd_eq_one_of_isSplitting {E V : Type} [Field E] [NumberField E]
    [CommRing V] [IsDomain V] [ValuationRing V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : ι → 𝓞 E →+* V) (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    (h : IsSplitting fun i => (algebraMap V K).comp (σ i)) (i₀ : ι) :
    Module.finrank V (eigenSub (baseChangeAction V
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) (σ i₀)) = 1 := by
  have : FaithfulSMul V K :=
    (faithfulSMul_iff_algebraMap_injective V K).2 (IsFractionRing.injective V K)
  have : Module.Flat V K := flat_of_valuationRing V K
  rw [← finrank_eigenSub_of_flat (R' := K) (extendTensor_equivariant V K _)
    (isBaseChange_extendTensor ℤ V K (𝓞 E)) (σ i₀)]
  have hs := eigenSub_toModuleEnd_eq_span h i₀
  beta_reduce at hs
  rw [hs]
  exact finrank_span_singleton (idem_ne_zero h i₀)

theorem finrank_eigenSub_toModuleEnd_eq_one {E V : Type} [Field E] [NumberField E] [CommRing V]
    [IsDomain V] [ValuationRing V] [CharZero V]
    {ι : Type} [Fintype ι] (σ : ι → 𝓞 E →+* V) (hσ : Function.Injective σ)
    (hc : Fintype.card ι = Module.finrank ℚ E) (i₀ : ι) :
    Module.finrank V (eigenSub (baseChangeAction V
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) (σ i₀)) = 1 := by
  classical
  exact finrank_eigenSub_toModuleEnd_eq_one_of_isSplitting σ (FractionRing V)
    (isSplitting_fractionRing hσ hc) i₀

end EigenSplit
end GlobalTheory
end

open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eigenspace_embedding_one : ∀ {E V : Type} [Field E] [NumberField E] [CommRing V] [IsDomain V] [ValuationRing V] [CharZero V]
    {ι : Type} [Fintype ι] (σ : ι → 𝓞 E →+* V), Function.Injective σ →
    Fintype.card ι = Module.finrank ℚ E → ∀ i₀ : ι,
    Module.finrank V (eigenSub (baseChangeAction V (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) (σ i₀)) = 1 := by
  atlas_forward_decl GlobalTheory.EigenSplit.finrank_eigenSub_toModuleEnd_eq_one
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open scoped TensorProduct
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame

namespace GlobalTheory.RedEig

theorem rTensor_mul_one_tmul {O R k : Type} [CommRing O] [CommRing R] [CommRing k] (ρ₀ : R →+* k) (χ : O →+* R) (e : R ⊗[ℤ] O)
    (he : ∀ a : O, e * ((1 : R) ⊗ₜ[ℤ] a) = χ a • e) (a : O) :
    ρ₀.toIntAlgHom.toLinearMap.rTensor O e * ((1 : k) ⊗ₜ[ℤ] a) = ρ₀ (χ a) • ρ₀.toIntAlgHom.toLinearMap.rTensor O e := by
  let Φ := Algebra.TensorProduct.map ρ₀.toIntAlgHom (AlgHom.id ℤ O)
  have hΦ : ∀ t, ρ₀.toIntAlgHom.toLinearMap.rTensor O t = Φ t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r b => simp [Φ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsm : ∀ (r : R) t, Φ (r • t) = ρ₀ r • Φ t := fun r t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s b => simp [Φ, TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  rw [hΦ, ← hsm, ← he a, map_mul]
  simp [Φ]

theorem span_rTensor_range_tensorAction {O R k Λ : Type} [CommRing O] [CommRing R] [CommRing k] [AddCommGroup Λ] [Module O Λ]
    (ρ₀ : R →+* k) (e : R ⊗[ℤ] O) :
    Submodule.span k ((ρ₀.toIntAlgHom.toLinearMap.rTensor Λ) ''
      (LinearMap.range (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) : Set (R ⊗[ℤ] Λ)))
    = LinearMap.range (tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
        (ρ₀.toIntAlgHom.toLinearMap.rTensor O e)) := by
  set red := ρ₀.toIntAlgHom.toLinearMap.rTensor Λ
  have key : ∀ (e : R ⊗[ℤ] O) (m : R ⊗[ℤ] Λ),
      red (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e m)
        = tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
            (ρ₀.toIntAlgHom.toLinearMap.rTensor O e) (red m) := by
    intro e m
    induction e using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [LinearMap.rTensor_tmul, tensorAction_tmul, tensorAction_tmul]
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul s l => simp [red, TensorProduct.smul_tmul']
      | add x y hx hy => rw [map_add, smul_add, map_add, hx, hy, map_add, map_add, smul_add]
    | add x y hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, map_add, LinearMap.add_apply]
  have hspan : Submodule.span k (Set.range red) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c l =>
      have : c ⊗ₜ[ℤ] l = c • red (1 ⊗ₜ l) := by simp [red, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have himg : (red '' (LinearMap.range (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) : Set (R ⊗[ℤ] Λ)))
      = (tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
            (ρ₀.toIntAlgHom.toLinearMap.rTensor O e)) '' Set.range red := by
    ext y
    simp only [LinearMap.coe_range, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨red m, ⟨m, rfl⟩, (key e m).symm⟩
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨_, ⟨m, rfl⟩, key e m⟩
  rw [himg, Submodule.span_image, hspan, Submodule.map_top]

theorem baseChangeAction_regular_apply {O R : Type} [CommRing O] [CommRing R] (a : O) (t : R ⊗[ℤ] O) :
    baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O) a t = t * ((1 : R) ⊗ₜ[ℤ] a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add x y hx hy => rw [map_add, hx, hy, add_mul]

theorem exists_generator {V M : Type} [CommRing V] [Nontrivial V] [AddCommGroup M] [Module V M] (P : Submodule V M)
    [Module.Free V P] [Module.Finite V P] (h1 : Module.finrank V P = 1) {Q : Submodule V M} (hQ : IsCompl P Q) :
    ∃ e ∈ P, P ≤ Submodule.span V {e} ∧ ∃ f : M →ₗ[V] V, f e = 1 := by
  let b := Module.finBasisOfFinrankEq V P h1
  refine ⟨b 0, (b 0).2, fun x hx => ?_, (b.coord 0).comp (Submodule.linearProjOfIsCompl P Q hQ), ?_⟩
  · have := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at this
    rw [Submodule.mem_span_singleton]
    exact ⟨b.repr ⟨x, hx⟩ 0, by simpa using congrArg Subtype.val this⟩
  · rw [LinearMap.comp_apply, show P.linearProjOfIsCompl Q hQ (b 0) = b 0 from
      Submodule.linearProjOfIsCompl_apply_left hQ _]
    simp

theorem exists_eigBar_eq_range : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (τ : PsiT D),
  ∃ ε : ct.kbar ⊗[ℤ] 𝓞 D.host.E, ε ≠ 0 ∧
    (∀ a : 𝓞 D.host.E, ε * ((1 : ct.kbar) ⊗ₜ[ℤ] a) = ct.ρ₀ (embV κ.c ct.W (embOf D τ) a) • ε) ∧
    ct.eigBar τ = LinearMap.range (tensorAction (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) ε) := by
  intro D A N j S κ p ct τ
  let σ : (D.host.E →+* ℂ) → 𝓞 D.host.E →+* ct.V₀ := fun i => embV κ.c ct.W i
  have hσ : Function.Injective σ := by
    intro i i' h
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.host.E)) (RingHom.ext fun a => ?_)
    have := congrArg (fun g : 𝓞 D.host.E →+* ct.V₀ => (((g a : ct.V₀) : κ.c.F) : ℂ)) h
    exact this
  have hc : Fintype.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := NumberField.Embeddings.card _ _
  have h1 := GlobalTheory.T.finrank_eigenspace_embedding_one σ hσ hc (embOf D τ)
  set P := eigenSub (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ (𝓞 D.host.E) : 𝓞 D.host.E →+* Module.End ℤ (𝓞 D.host.E))) (σ (embOf D τ)) with hP
  have : Module.Free ct.V₀ P := free_eigenSub_of_valuationRing _ _
  have : Module.Finite ct.V₀ P := finite_eigenSub_of_valuationRing _ _
  obtain ⟨Q, hQ⟩ := exists_isCompl_eigenSub_of_valuationRing
    (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ (𝓞 D.host.E) : 𝓞 D.host.E →+* Module.End ℤ (𝓞 D.host.E))) (σ (embOf D τ))
  obtain ⟨e, he, hle, f, hf⟩ := exists_generator P h1 hQ
  have heig : ∀ a : 𝓞 D.host.E, e * ((1 : ct.V₀) ⊗ₜ[ℤ] a) = σ (embOf D τ) a • e := fun a => by
    rw [← baseChangeAction_regular_apply]; exact mem_eigenSub.1 he a
  have hρ : ∀ x, ct.ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal ct.V₀ := fun x hx => by
    rw [At.ρ₀, RingHom.comp_apply] at hx
    exact (IsLocalRing.residue_eq_zero_iff x).1 ((algebraMap (IsLocalRing.ResidueField ct.V₀) ct.kbar).injective (hx.trans (map_zero _).symm))
  have : Module.Finite (𝓞 D.host.E) S.Dw.La := S.Dw.fin
  have : Module.Projective (𝓞 D.host.E) S.Dw.La := S.Dw.proj
  refine ⟨ct.ρ₀.toIntAlgHom.toLinearMap.rTensor _ e, GlobalTheory.T.rTensor_residue_nonzero_of_split ct.ρ₀ hρ e f hf, rTensor_mul_one_tmul ct.ρ₀ _ e heig, ?_⟩
  rw [At.eigBar, At.eigLat, GlobalTheory.T.eigenspace_rank_one_span (σ (embOf D τ)) e he hle]
  exact span_rTensor_range_tensorAction ct.ρ₀ e

end GlobalTheory.RedEig
end
