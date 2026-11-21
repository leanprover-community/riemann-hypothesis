import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftCoactionIffIsCoactionComm
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv

namespace GlobalTheory

section Comodule

open CartierDual

variable {R C M M' : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

def dualContraction (ρ : M →ₗ[R] M ⊗[R] C) : CartierDual R C →ₗ[R] Module.End R M :=
  (tensorToHom R M C ∘ₗ ρ).flip

theorem dualContraction_apply (ρ : M →ₗ[R] M ⊗[R] C) (w : CartierDual R C) (m : M) :
    dualContraction ρ w m = tensorToHom R M C (ρ m) w := rfl

theorem dualContraction_eq_rid (ρ : M →ₗ[R] M ⊗[R] C) (w : CartierDual R C) (m : M) :
    dualContraction ρ w m = TensorProduct.rid R M (w.ofConv.lTensor M (ρ m)) :=
  tensorToHom_apply _ _

variable (R M C) in

def dualContractionEquiv [Module.Finite R C] [Module.Projective R C] :
    (M →ₗ[R] M ⊗[R] C) ≃ (CartierDual R C →ₗ[R] Module.End R M) where
  toFun := dualContraction
  invFun θ := (tensorEquivHom R M C).symm.toLinearMap ∘ₗ θ.flip
  left_inv ρ := LinearMap.ext fun m => (tensorEquivHom R M C).symm_apply_apply (ρ m)
  right_inv θ := LinearMap.ext fun w => LinearMap.ext fun m =>
    congr($((tensorEquivHom R M C).apply_symm_apply (θ.flip m)) w)

@[simp] theorem dualContractionEquiv_apply [Module.Finite R C] [Module.Projective R C]
    (ρ : M →ₗ[R] M ⊗[R] C) : dualContractionEquiv R C M ρ = dualContraction ρ := rfl






variable [Coalgebra R C]

private theorem tensorToHom_assoc_rTensor (ρ : M →ₗ[R] M ⊗[R] C) (φ ψ : CartierDual R C)
    (x : M ⊗[R] C) :
    tensorToHom R M (C ⊗[R] C) (TensorProduct.assoc R M C C (ρ.rTensor C x))
      (toConv (pair R C C (φ ⊗ₜ ψ))) = dualContraction ρ φ (tensorToHom R M C x ψ) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul m c =>
    rw [LinearMap.rTensor_tmul, tensorToHom_tmul, map_smul, dualContraction_apply]
    generalize ρ m = s
    induction s with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, add_tmul, smul_add, hx, hy]
    | tmul m' c' => simp [smul_smul, mul_comm]

private theorem tensorToHom_lTensor_comul (φ ψ : CartierDual R C) (x : M ⊗[R] C) :
    tensorToHom R M (C ⊗[R] C) ((comul : C →ₗ[R] C ⊗[R] C).lTensor M x)
      (toConv (pair R C C (φ ⊗ₜ ψ))) = tensorToHom R M C x (φ * ψ) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul m c => rw [LinearMap.lTensor_tmul, tensorToHom_tmul, tensorToHom_tmul, mul_apply]

theorem IsCoaction.dualContraction_one {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    dualContraction ρ 1 = 1 :=
  LinearMap.ext fun m => (dualContraction_eq_rid ρ 1 m).trans (h.rid_counit m)

theorem IsCoaction.dualContraction_mul {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ)
    (φ ψ : CartierDual R C) :
    dualContraction ρ (φ * ψ) = dualContraction ρ φ * dualContraction ρ ψ :=
  LinearMap.ext fun m => by
    rw [Module.End.mul_apply, dualContraction_apply, dualContraction_apply ρ ψ,
      ← tensorToHom_lTensor_comul, ← h.coassoc, tensorToHom_assoc_rTensor]

theorem isCoaction_iff_dualContraction [Module.Finite R C] [Module.Projective R C]
    {ρ : M →ₗ[R] M ⊗[R] C} :
    IsCoaction ρ ↔ dualContraction ρ 1 = 1 ∧
      ∀ φ ψ, dualContraction ρ (φ * ψ) = dualContraction ρ φ * dualContraction ρ ψ := by
  refine ⟨fun h => ⟨h.dualContraction_one, h.dualContraction_mul⟩, fun ⟨h1, h2⟩ =>
    ⟨fun m => eq_of_forall_tensorToHom_pair fun φ ψ => ?_, fun m => ?_⟩⟩
  · rw [tensorToHom_lTensor_comul, tensorToHom_assoc_rTensor]
    exact congr($(h2 φ ψ) m).symm
  · refine (TensorProduct.rid R M).injective ?_
    rw [TensorProduct.rid_tmul, one_smul]
    exact (dualContraction_eq_rid ρ 1 m).symm.trans congr($h1 m)

def IsCoaction.dualAction {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    CartierDual R C →ₐ[R] Module.End R M :=
  AlgHom.ofLinearMap (dualContraction ρ) h.dualContraction_one h.dualContraction_mul

@[simp] theorem IsCoaction.dualAction_apply {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ)
    (w : CartierDual R C) : h.dualAction w = dualContraction ρ w := rfl

abbrev IsCoaction.dualModule {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    Module (CartierDual R C) M :=
  Module.compHom M h.dualAction.toRingHom



variable (R C M) in

def coactionEquivDualAction [Module.Finite R C] [Module.Projective R C] :
    {ρ : M →ₗ[R] M ⊗[R] C // IsCoaction ρ} ≃ (CartierDual R C →ₐ[R] Module.End R M) where
  toFun ρ := ρ.2.dualAction
  invFun θ := ⟨(dualContractionEquiv R C M).symm θ.toLinearMap, by
    rw [isCoaction_iff_dualContraction, ← dualContractionEquiv_apply, Equiv.apply_symm_apply]
    exact ⟨map_one θ, map_mul θ⟩⟩
  left_inv ρ := Subtype.ext ((dualContractionEquiv R C M).symm_apply_apply ρ.1)
  right_inv θ := AlgHom.toLinearMap_injective
    ((dualContractionEquiv R C M).apply_symm_apply θ.toLinearMap)

@[simp] theorem coactionEquivDualAction_apply [Module.Finite R C] [Module.Projective R C]
    (ρ : {ρ : M →ₗ[R] M ⊗[R] C // IsCoaction ρ}) :
    coactionEquivDualAction R C M ρ = ρ.2.dualAction := rfl


end Comodule

section Augmented

variable {R : Type*} [CommRing R]

section Noncommutative

variable {D : Type*} [Ring D] [Algebra R D] {M : Type*} [AddCommGroup M] [Module R M] [Module D M]
  [IsScalarTower R D M]

theorem forall_ker_smul_eq_zero_iff (ε : D →ₐ[R] R) (m : M) :
    (∀ w ∈ RingHom.ker ε, w • m = 0) ↔ ∀ w : D, w • m = ε w • m := by
  refine ⟨fun h w => ?_, fun h w hw => by rw [h, RingHom.mem_ker.1 hw, zero_smul]⟩
  have := h (w - algebraMap R D (ε w)) (by simp [RingHom.mem_ker])
  rwa [sub_smul, algebraMap_smul, sub_eq_zero] at this

theorem forall_ker_mul_eq_zero_iff (ε : D →ₐ[R] R) (Λ : D) :
    (∀ w ∈ RingHom.ker ε, w * Λ = 0) ↔ ∀ w : D, w * Λ = ε w • Λ :=
  forall_ker_smul_eq_zero_iff ε Λ


end Noncommutative

variable {D D' : Type*} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']

theorem mem_annihilator_iff_forall_mul {I : Ideal D} {Λ : D} :
    Λ ∈ I.annihilator ↔ ∀ w ∈ I, w * Λ = 0 := by
  simp only [Submodule.mem_annihilator, smul_eq_mul, mul_comm Λ]

theorem mem_annihilator_ker_iff {ε : D →ₐ[R] R} {Λ : D} :
    Λ ∈ (RingHom.ker ε).annihilator ↔ ∀ w : D, w * Λ = ε w • Λ :=
  mem_annihilator_iff_forall_mul.trans (forall_ker_mul_eq_zero_iff ε Λ)


theorem smul_eq_smul_of_mem_annihilator_ker {ε : D →ₐ[R] R} {Λ T : D}
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) (hT : T ∈ (RingHom.ker ε).annihilator) :
    ε Λ • T = ε T • Λ := by
  rw [← mem_annihilator_ker_iff.1 hT, ← mem_annihilator_ker_iff.1 hΛ, mul_comm]





end Augmented

section Invariants

variable {R H M : Type*} [CommRing R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [AddCommGroup M] [Module R M]







end Invariants

section Unramified

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]


theorem eq_smul_of_mem_annihilator_ker {ε : A →ₐ[R] R} {e Λ : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1)
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) : Λ = ε Λ • e := by
  rw [← smul_eq_smul_of_mem_annihilator_ker he hΛ, he1, one_smul]


theorem annihilator_ker_eq_span {ε : A →ₐ[R] R} {e : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1) :
    (RingHom.ker ε).annihilator = Ideal.span {e} := by
  refine le_antisymm (fun Λ hΛ => Ideal.mem_span_singleton'.2 ⟨algebraMap R A (ε Λ), ?_⟩)
    ((Ideal.span_singleton_le_iff_mem _).2 he)
  rw [← Algebra.smul_def, ← eq_smul_of_mem_annihilator_ker he he1 hΛ]


theorem bijective_prod_quotient_of_mem_annihilator_ker {ε : A →ₐ[R] R} {e : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1) :
    Function.Bijective (ε.prod (Ideal.Quotient.mkₐ R (Ideal.span {e}))) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun ⟨r, q⟩ => ?_⟩
  · have h1 : ε a = 0 := congrArg Prod.fst ha
    have h2 : a ∈ Ideal.span {e} := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Prod.snd ha)
    rw [← annihilator_ker_eq_span he he1] at h2
    rw [eq_smul_of_mem_annihilator_ker he he1 h2, h1, zero_smul]
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h0 : Ideal.Quotient.mkₐ R (Ideal.span {e}) e = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)
    refine ⟨a + (r - ε a) • e, Prod.ext ?_ ?_⟩
    · simp [he1]
    · change Ideal.Quotient.mkₐ R (Ideal.span {e}) (a + (r - ε a) • e) = _
      rw [map_add, map_smul, h0, smul_zero, add_zero]; rfl

theorem existsUnique_mem_annihilator_ker [Algebra.FormallyUnramified R A]
    [Algebra.EssFiniteType R A] (ε : A →ₐ[R] R) :
    ∃! e, e ∈ (RingHom.ker ε).annihilator ∧ ε e = 1 := by
  let π : A ⊗[R] A →ₐ[R] A := Algebra.TensorProduct.lift ((Algebra.ofId R A).comp ε) (AlgHom.id R A)
    fun _ _ => Commute.all _ _
  have hπ (t : A ⊗[R] A) : ε (π t) = ε (Algebra.TensorProduct.lmul' R t) := by
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp [π, Algebra.ofId_apply]
  have he : π (Algebra.FormallyUnramified.elem R A) ∈ (RingHom.ker ε).annihilator :=
    mem_annihilator_ker_iff.2 fun w => by
      have := congrArg π (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) w)
      simpa [π, Algebra.ofId_apply, Algebra.smul_def] using this
  have he1 : ε (π (Algebra.FormallyUnramified.elem R A)) = 1 := by
    rw [hπ, Algebra.FormallyUnramified.lmul_elem, map_one]
  refine ⟨_, ⟨he, he1⟩, fun e' he' => ?_⟩
  rw [eq_smul_of_mem_annihilator_ker he he1 he'.1, he'.2, one_smul]


end Unramified

section BaseChange

variable {R D : Type*} (K : Type*) [CommRing R] [CommRing D] [Algebra R D] [CommRing K]
  [Algebra R K]

def augmentationBaseChange (ε : D →ₐ[R] R) : K ⊗[R] D →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp ε) fun _ _ => Commute.all _ _

@[simp] theorem augmentationBaseChange_tmul (ε : D →ₐ[R] R) (k : K) (d : D) :
    augmentationBaseChange K ε (k ⊗ₜ d) = k * algebraMap R K (ε d) := rfl

variable {K}



variable (K) in

theorem one_tmul_mem_annihilator_ker {ε : D →ₐ[R] R} {Λ : D}
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) :
    (1 : K) ⊗ₜ[R] Λ ∈ (RingHom.ker (augmentationBaseChange K ε)).annihilator := by
  refine mem_annihilator_ker_iff.2 fun w => ?_
  induction w with
  | zero => simp
  | add a b ha hb => rw [add_mul, ha, hb, map_add, add_smul]
  | tmul k d =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mem_annihilator_ker_iff.1 hΛ,
      augmentationBaseChange_tmul, smul_tmul', ← smul_tmul]
    simp [Algebra.smul_def, mul_comm]

theorem one_tmul_mem_annihilator_ker_iff (hD : Function.Injective fun d : D => (1 : K) ⊗ₜ[R] d)
    {ε : D →ₐ[R] R} {Λ : D} :
    (1 : K) ⊗ₜ[R] Λ ∈ (RingHom.ker (augmentationBaseChange K ε)).annihilator ↔
      Λ ∈ (RingHom.ker ε).annihilator := by
  refine ⟨fun h => mem_annihilator_iff_forall_mul.2 fun w hw => hD ?_,
    one_tmul_mem_annihilator_ker K⟩
  have := mem_annihilator_iff_forall_mul.1 h (1 ⊗ₜ w)
    (by simp [RingHom.mem_ker, RingHom.mem_ker.1 hw])
  simpa using this



open nonZeroDivisors in

theorem one_tmul_injective_of_isTorsionFree (K : Type*) [Field K] [IsDomain R] [Algebra R K]
    [IsFractionRing R K] (M : Type*) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] :
    Function.Injective fun m : M => (1 : K) ⊗ₜ[R] m :=
  (IsLocalizedModule.injective_iff_isRegular R⁰ (TensorProduct.mk R K M 1)).2 fun c =>
    IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero c.2)

end BaseChange

section GenericFibre

variable {R D : Type*} [CommRing R] [CommRing D] [Algebra R D]
  (K : Type*) [Field K] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  [Module.IsTorsionFree R D] [Algebra.FormallyUnramified K (K ⊗[R] D)]
  [Algebra.EssFiniteType K (K ⊗[R] D)]

include K in

theorem eq_zero_of_mem_annihilator_ker {ε : D →ₐ[R] R} {Λ : D}
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) (h0 : ε Λ = 0) : Λ = 0 := by
  obtain ⟨e, ⟨he, he1⟩, -⟩ := existsUnique_mem_annihilator_ker (augmentationBaseChange K ε)
  refine one_tmul_injective_of_isTorsionFree (R := R) K D ?_
  simpa [h0] using eq_smul_of_mem_annihilator_ker he he1 (one_tmul_mem_annihilator_ker K hΛ)

open nonZeroDivisors in
include K in

theorem exists_mem_annihilator_ker_ne_zero (ε : D →ₐ[R] R) :
    ∃ Λ ∈ (RingHom.ker ε).annihilator, ε Λ ≠ 0 := by
  obtain ⟨e, ⟨he, he1⟩, -⟩ := existsUnique_mem_annihilator_ker (augmentationBaseChange K ε)
  obtain ⟨⟨Λ, s⟩, hs⟩ := IsLocalizedModule.surj R⁰ (TensorProduct.mk R K D 1) e
  have hs' : algebraMap R K s • e = (1 : K) ⊗ₜ[R] Λ := by
    rw [algebraMap_smul]; exact hs
  refine ⟨Λ, (one_tmul_mem_annihilator_ker_iff (one_tmul_injective_of_isTorsionFree K D)).1 ?_,
    fun h => ?_⟩
  · rw [← hs']
    exact Submodule.smul_of_tower_mem _ _ he
  · have := congrArg (augmentationBaseChange K ε) hs'
    rw [map_smul, he1] at this
    simp [h, nonZeroDivisors.ne_zero s.2] at this

end GenericFibre

section ComoduleBaseChange

open CartierDual

variable {R K H M M' : Type*} [CommRing R] [CommRing K] [Algebra R K] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [Module K M'] [IsScalarTower R K M']


variable [Semiring H] [Bialgebra R H] [Module.Finite R H] [Module.Projective R H] [IsCocomm R H]



end ComoduleBaseChange

section Cramer

open Matrix

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem det_mul_eq_zero_of_sum_mul_eq_zero {D : Type*} [CommRing D] {a : Matrix σ σ D} {x : σ → D}
    (h : ∀ i, ∑ j, a i j * x j = 0) (j : σ) : a.det * x j = 0 := by
  have h0 : a *ᵥ x = 0 := funext h
  have h1 : a.adjugate *ᵥ (a *ᵥ x) = a.det • x := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [h0, mulVec_zero] at h1
  exact (congrFun h1 j).symm

theorem det_mem_annihilator_span {D : Type*} [CommRing D] {a : Matrix σ σ D} {x : σ → D}
    (h : ∀ i, ∑ j, a i j * x j = 0) : a.det ∈ (Ideal.span (Set.range x)).annihilator :=
  (Submodule.mem_annihilator_span _ _).2 fun ⟨_, j, hj⟩ =>
    hj ▸ det_mul_eq_zero_of_sum_mul_eq_zero h j

open MvPowerSeries

variable {R : Type*} [CommRing R]

omit [DecidableEq σ] in

theorem exists_matrix_eq_sum_mul_X {τ : Type*} {f : τ → MvPowerSeries σ R}
    (hf : ∀ i, constantCoeff (f i) = 0) :
    ∃ a : Matrix τ σ (MvPowerSeries σ R), ∀ i, f i = ∑ j, a i j * X j := by
  have h (i) : ∃ c : σ → MvPowerSeries σ R, f i = ∑ j, c j * X j := by
    have : f i ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) :=
      germIdeal_eq_span (σ := σ) (R := R) ▸ hf i
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 this
    exact ⟨c, hc.symm⟩
  choose a ha using h
  exact ⟨a, ha⟩

omit [DecidableEq σ] in

theorem coeff_single_sum_mul_X (c : σ → MvPowerSeries σ R) (j : σ) :
    coeff (Finsupp.single j 1) (∑ l, c l * X l) = constantCoeff (c j) := by
  classical
  rw [map_sum, Finset.sum_eq_single j]
  · have := coeff_add_mul_monomial (0 : σ →₀ ℕ) (Finsupp.single j 1) (c j) 1
    rwa [zero_add, mul_one, ← X_def, coeff_zero_eq_constantCoeff_apply] at this
  · intro l _ hl
    exact X_dvd_iff.1 (dvd_mul_left (X l) (c l)) _ (Finsupp.single_eq_of_ne hl)
  · simp

variable {D : Type*} [CommRing D] [Algebra R D]

omit [DecidableEq σ] in

theorem ker_eq_span_range_X {π : MvPowerSeries σ R →ₐ[R] D} (hπ : Function.Surjective π)
    {ε : D →ₐ[R] R} (hε : ∀ g, ε (π g) = constantCoeff g) :
    RingHom.ker ε = Ideal.span (Set.range fun j => π (X j)) := by
  refine le_antisymm (fun d hd => ?_) (Ideal.span_le.2 ?_)
  · obtain ⟨g, rfl⟩ := hπ d
    obtain ⟨a, ha⟩ := exists_matrix_eq_sum_mul_X (f := fun _ : Unit => g) fun _ => (hε g).symm.trans hd
    rw [ha (), map_sum]
    exact Ideal.sum_mem _ fun j _ => by
      rw [map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hε]

theorem map_det_mul_map_X {π : MvPowerSeries σ R →ₐ[R] D} {a : Matrix σ σ (MvPowerSeries σ R)}
    (ha : ∀ i, π (∑ j, a i j * X j) = 0) (j : σ) : π a.det * π (X j) = 0 := by
  rw [AlgHom.map_det]
  exact det_mul_eq_zero_of_sum_mul_eq_zero (x := fun j => π (X j)) (fun i => by simpa using ha i) j

theorem map_det_mem_annihilator_ker {π : MvPowerSeries σ R →ₐ[R] D} (hπ : Function.Surjective π)
    {ε : D →ₐ[R] R} (hε : ∀ g, ε (π g) = constantCoeff g) {a : Matrix σ σ (MvPowerSeries σ R)}
    (ha : ∀ i, π (∑ j, a i j * X j) = 0) : π a.det ∈ (RingHom.ker ε).annihilator := by
  rw [ker_eq_span_range_X hπ hε, AlgHom.map_det]
  exact det_mem_annihilator_span fun i => by simpa using ha i

theorem constantCoeff_det {a : Matrix σ σ (MvPowerSeries σ R)} {f : σ → MvPowerSeries σ R}
    (hf : ∀ i, f i = ∑ j, a i j * X j) :
    constantCoeff a.det = (Matrix.of fun i j => coeff (Finsupp.single j 1) (f i)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [hf, coeff_single_sum_mul_X, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]

omit [Fintype σ] [DecidableEq σ] in

def quotientConstantCoeff {τ : Type*} (f : τ → MvPowerSeries σ R)
    (hf : ∀ i, constantCoeff (f i) = 0) :
    (MvPowerSeries σ R ⧸ Ideal.span (Set.range f)) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ { constantCoeff with commutes' := fun r => constantCoeff_C r }
    fun _ hg => (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hf i) :
      Ideal.span (Set.range f) ≤ germIdeal σ R) hg

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem quotientConstantCoeff_mk {τ : Type*} (f : τ → MvPowerSeries σ R)
    (hf : ∀ i, constantCoeff (f i) = 0) (g : MvPowerSeries σ R) :
    quotientConstantCoeff f hf (Ideal.Quotient.mk _ g) = constantCoeff g := rfl

omit [DecidableEq σ] in

theorem constantCoeff_eq_zero_of_eq_sum_mul_X {τ : Type*} {a : Matrix τ σ (MvPowerSeries σ R)}
    {f : τ → MvPowerSeries σ R} (hf : ∀ i, f i = ∑ j, a i j * X j) (i : τ) :
    constantCoeff (f i) = 0 := by
  simp [hf]

theorem cramer_quotient {a : Matrix σ σ (MvPowerSeries σ R)} {f : σ → MvPowerSeries σ R}
    (hf : ∀ i, f i = ∑ j, a i j * X j) :
    let ε := quotientConstantCoeff f (constantCoeff_eq_zero_of_eq_sum_mul_X hf)
    let Λ := Ideal.Quotient.mk (Ideal.span (Set.range f)) a.det
    (∀ j, Λ * Ideal.Quotient.mk _ (X j) = 0) ∧ Λ ∈ (RingHom.ker ε).annihilator ∧
      ε Λ = (a.map constantCoeff).det ∧
      ε Λ = (Matrix.of fun i j => coeff (Finsupp.single j 1) (f i)).det := by
  have ha (i) : Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)) (∑ j, a i j * X j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, hf i⟩)
  exact ⟨map_det_mul_map_X ha,
    map_det_mem_annihilator_ker (Ideal.Quotient.mkₐ_surjective R _) (fun _ => rfl) ha,
    RingHom.map_det (constantCoeff : MvPowerSeries σ R →+* R) a, constantCoeff_det hf⟩

end Cramer

universe u v w


section Examples

example : ¬ ∀ w : CartierDual ℤ (AddMonoidAlgebra ℤ (ZMod 2)),
    dualContraction (comul (R := ℤ)) w (AddMonoidAlgebra.single (1 : ZMod 2) (1 : ℤ)) =
      w 1 • AddMonoidAlgebra.single (1 : ZMod 2) (1 : ℤ) := fun h => by
  have h1 := h ((CartierDual.addMonoidAlgebraEquiv ℤ (ZMod 2)).symm (Pi.single 0 1))
  rw [dualContraction_apply, AddMonoidAlgebra.one_def] at h1
  simp [eq_comm] at h1

open MvPowerSeries in

example : ∃ ε : (MvPowerSeries Unit ℤ ⧸
      Ideal.span (Set.range fun _ : Unit => (2 + X ()) * (X () : MvPowerSeries Unit ℤ))) →ₐ[ℤ] ℤ,
    Ideal.Quotient.mk _ (2 + X ()) ∈ (RingHom.ker ε).annihilator ∧
      ε (Ideal.Quotient.mk _ (2 + X ())) = 2 := by
  have h := cramer_quotient (a := Matrix.of fun _ _ : Unit => (2 + X () : MvPowerSeries Unit ℤ))
    (f := fun _ : Unit => (2 + X ()) * X ()) (by simp)
  refine ⟨_, by simpa using h.2.1, ?_⟩
  simp [map_ofNat]

end Examples

end GlobalTheory
