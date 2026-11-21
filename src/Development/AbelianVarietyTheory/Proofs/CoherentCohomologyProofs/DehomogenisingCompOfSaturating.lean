import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteGrCechHomology
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingEqZeroIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulMemSpanOfFiniteQuot
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteQuotSMulTopXSubOneOfChart

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_isBaseChange_coker {R₀ R A₀ A M₁ M₂ N₁ N₂ : Type*} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [Ring A₀] [Ring A] [Algebra R₀ A₀] [Algebra R A] [SMul R₀ A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R₀ M₁] [Module R₀ M₂] [Module A₀ M₁] [Module A₀ M₂]
    [IsScalarTower R₀ A₀ M₁] [IsScalarTower R₀ A₀ M₂]
    [Module R₀ N₁] [Module R₀ N₂] [Module R N₁] [Module R N₂] [Module A N₁] [Module A N₂]
    [IsScalarTower R₀ R N₁] [IsScalarTower R₀ R N₂] [IsScalarTower R A N₁] [IsScalarTower R A N₂]
    [IsScalarTower R₀ A N₂]
    (f₀ : M₁ →ₗ[A₀] M₂) (f : N₁ →ₗ[A] N₂) (h₁ : M₁ →ₗ[R₀] N₁) (h₂ : M₂ →ₗ[R₀] N₂)
    (b₁ : IsBaseChange R h₁) (b₂ : IsBaseChange R h₂) (hcomm : ∀ x, h₂ (f₀ x) = f (h₁ x)) :
    ∃ ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f),
      IsBaseChange R ψ ∧ ∀ y, ψ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (h₂ y) := by
  let q₀ : M₂ →ₗ[R₀] (M₂ ⧸ LinearMap.range f₀) := (LinearMap.range f₀).mkQ.restrictScalars R₀
  let q : N₂ →ₗ[R] (N₂ ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.restrictScalars R
  have hq₀ : Function.Surjective q₀ := (LinearMap.range f₀).mkQ_surjective
  have hq : Function.Surjective q := (LinearMap.range f).mkQ_surjective
  have hex₀ : Function.Exact (f₀.restrictScalars R₀) q₀ := LinearMap.exact_map_mkQ_range f₀
  have hex : Function.Exact (f.restrictScalars R) q := LinearMap.exact_map_mkQ_range f
  have hker : LinearMap.ker q₀ ≤ LinearMap.ker ((q.restrictScalars R₀).comp h₂) := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hex₀ y).1 hy
    exact (hex _).2 ⟨h₁ x, (hcomm x).symm⟩
  let ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f) :=
    ((LinearMap.ker q₀).liftQ _ hker).comp (q₀.quotKerEquivOfSurjective hq₀).symm.toLinearMap
  have hψ : ∀ y, ψ (q₀ y) = q (h₂ y) := by
    intro y
    have : (q₀.quotKerEquivOfSurjective hq₀).symm (q₀ y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  exact ⟨ψ, IsBaseChange.of_right_exact R (f := f₀.restrictScalars R₀) (g := q₀)
    (f' := f.restrictScalars R) (g' := q) h₁ h₂ ψ (LinearMap.ext hcomm) (LinearMap.ext hψ)
    b₁ b₂ hex₀ hq₀ hex hq, hψ⟩

theorem isBaseChange_coker_matrix_mvPolynomial :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (a b : ℕ)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀))
      (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      Φ₀.map (MvPolynomial.map (algebraMap R₀ R)) = Φ →
      ∃ ψ : ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin) →ₗ[R₀]
          ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin),
        IsBaseChange R ψ ∧ ∀ y : Fin a → MvPolynomial ι R₀,
          ψ (Submodule.Quotient.mk y) =
            Submodule.Quotient.mk fun l => MvPolynomial.map (algebraMap R₀ R) (y l) := by
  intro ι R₀ R _ _ _ a b Φ₀ Φ hΦ
  have hm : IsBaseChange R (mapAlgHom (σ := ι) (Algebra.ofId R₀ R)).toLinearMap :=
    IsBaseChange.of_equiv (algebraTensorAlgEquiv R₀ R).toLinearEquiv fun p => by
      simp [mapAlgHom_apply]
  refine exists_isBaseChange_coker Φ₀.mulVecLin Φ.mulVecLin _ _
    (IsBaseChange.finitePow (Fin b) hm) (IsBaseChange.finitePow (Fin a) hm) fun x => ?_
  funext l
  rw [← hΦ]
  exact RingHom.map_mulVec (MvPolynomial.map (algebraMap R₀ R)) Φ₀ x l

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

section

variable {R₀ R A₀ A : Type} [CommRing R₀] [CommRing R] [CommRing A₀] [CommRing A] [Algebra R₀ R]
  [Algebra R₀ A₀] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  {N₀ N : Type} [AddCommGroup N₀] [Module R₀ N₀] [Module A₀ N₀] [IsScalarTower R₀ A₀ N₀]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module R₀ N]
  [IsScalarTower R₀ R N] [IsScalarTower R₀ A N]

theorem exists_awayFrac_common {f : A₀} (z w : LocalizedModule.Away f N₀) :
    ∃ k m m', awayFrac N₀ f k m = z ∧ awayFrac N₀ f k m' = w := by
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨j, m', rfl⟩ := exists_awayFrac w
  exact ⟨k + j, f ^ j • m, f ^ k • m', awayFrac_add_pow_smul _ _ _ _,
    by rw [add_comm, awayFrac_add_pow_smul]⟩

omit [Algebra R A] [IsScalarTower R₀ R A] [Module R N] [IsScalarTower R A N]
  [IsScalarTower R₀ R N] in

theorem exists_away_map_of_intertwine (ψ : N₀ →ₗ[R₀] N) (x₀ : A₀) (x : A)
    (h : ∀ (k : ℕ) y, ψ (x₀ ^ k • y) = x ^ k • ψ y) :
    ∃ θ : LocalizedModule.Away x₀ N₀ →ₗ[R₀] LocalizedModule.Away x N,
      ∀ (k : ℕ) y, θ (awayFrac N₀ x₀ k y) = awayFrac N x k (ψ y) := by
  choose d n hdn using fun z : LocalizedModule.Away x₀ N₀ => exists_awayFrac z
  have key (k : ℕ) (y : N₀) :
      awayFrac N x (d (awayFrac N₀ x₀ k y)) (ψ (n (awayFrac N₀ x₀ k y))) =
        awayFrac N x k (ψ y) := by
    obtain ⟨l, hl⟩ := awayFrac_eq_iff.1 (hdn (awayFrac N₀ x₀ k y))
    exact awayFrac_eq_iff.2 ⟨l, by rw [← h, ← h, hl]⟩
  refine ⟨⟨⟨fun z => awayFrac N x (d z) (ψ (n z)), fun z w => ?_⟩, fun r z => ?_⟩, key⟩
  · obtain ⟨k, m, m', rfl, rfl⟩ := exists_awayFrac_common z w
    rw [← map_add, key, key, key, map_add, map_add]
  · obtain ⟨k, m, rfl⟩ := exists_awayFrac z
    simp only [RingHom.id_apply]
    rw [← LinearMap.map_smul_of_tower, key, key, map_smul, LinearMap.map_smul_of_tower]

theorem isBaseChange_away_of_intertwine (ψ : N₀ →ₗ[R₀] N) (hψ : IsBaseChange R ψ) (x₀ : A₀)
    (x : A) (h : ∀ (k : ℕ) y, ψ (x₀ ^ k • y) = x ^ k • ψ y)
    (θ : LocalizedModule.Away x₀ N₀ →ₗ[R₀] LocalizedModule.Away x N)
    (hθ : ∀ (k : ℕ) y, θ (awayFrac N₀ x₀ k y) = awayFrac N x k (ψ y)) : IsBaseChange R θ := by
  let F (k : ℕ) : R ⊗[R₀] N₀ →ₗ[R] R ⊗[R₀] LocalizedModule.Away x₀ N₀ :=
    ((awayFrac N₀ x₀ k).restrictScalars R₀).baseChange R
  let P (k : ℕ) : R ⊗[R₀] N₀ →ₗ[R] R ⊗[R₀] N₀ :=
    ((LinearMap.lsmul A₀ N₀ (x₀ ^ k)).restrictScalars R₀).baseChange R
  have hFP (k l : ℕ) (t : R ⊗[R₀] N₀) : F (k + l) (P l t) = F k t := by
    induction t with
    | zero => simp
    | tmul r y => exact congrArg (r ⊗ₜ[R₀] ·) (awayFrac_add_pow_smul x₀ k l y)
    | add a b ha hb => simp only [map_add, ha, hb]
  have hP (l : ℕ) (t : R ⊗[R₀] N₀) : hψ.equiv (P l t) = x ^ l • hψ.equiv t := by
    induction t with
    | zero => simp
    | tmul r y => simp [P, IsBaseChange.equiv_tmul, h, smul_comm r]
    | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  have hF (k : ℕ) (t : R ⊗[R₀] N₀) :
      θ.liftBaseChange R (F k t) = awayFrac N x k (hψ.equiv t) := by
    induction t with
    | zero => simp
    | tmul r y => simp [F, IsBaseChange.equiv_tmul, hθ, LinearMap.map_smul_of_tower]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hsurj (z : R ⊗[R₀] LocalizedModule.Away x₀ N₀) : ∃ k t, F k t = z := by
    induction z with
    | zero => exact ⟨0, 0, map_zero _⟩
    | tmul r z =>
      obtain ⟨k, y, rfl⟩ := exists_awayFrac z
      exact ⟨k, r ⊗ₜ y, by simp [F]⟩
    | add a b ha hb =>
      obtain ⟨k, t, rfl⟩ := ha
      obtain ⟨j, u, rfl⟩ := hb
      exact ⟨k + j, P j t + P k u, by rw [map_add, hFP, add_comm k j, hFP]⟩
  suffices hb : Function.Bijective (θ.liftBaseChange R) from
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hb) fun z => by simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨k, t, rfl⟩ := hsurj z
    rw [hF, awayFrac_eq_zero_iff] at hz
    obtain ⟨l, hl⟩ := hz
    rw [← hP, map_eq_zero_iff _ hψ.equiv.injective] at hl
    rw [← hFP k l, hl, map_zero]
  · intro z
    obtain ⟨k, y, rfl⟩ := exists_awayFrac z
    obtain ⟨t, rfl⟩ := hψ.equiv.surjective y
    exact ⟨F k t, hF k t⟩

end

theorem exists_isBaseChange_away_xProd :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (s : Finset ι), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → ∃ θ : LocalizedModule.Away (xProd R₀ s) N₀ →ₗ[R₀] LocalizedModule.Away (xProd R s) N, IsBaseChange R θ ∧ ∀ (k : ℕ) y, θ (awayFrac N₀ (xProd R₀ s) k y) = awayFrac N (xProd R s) k (ψ y) := by
  intro ι R₀ R _ _ _ N₀ N _ _ _ _ _ _ _ _ _ _ _ ψ s hψ hX
  classical
  have h₁ (y : N₀) : ψ (xProd R₀ s • y) = xProd R s • ψ y := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp only [xProd] at ih ⊢; simp only [Finset.prod_insert hi, mul_smul, hX, ih]
  have h (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h₁, ih]
  obtain ⟨θ, hθ⟩ := exists_away_map_of_intertwine ψ _ _ h
  exact ⟨θ, isBaseChange_away_of_intertwine ψ hψ _ _ h θ hθ, hθ⟩

end GlobalTheory
end
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isBaseChange_gradedPiece : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [AddCommGroup N] [Module R₀ N] [Module R N] [IsScalarTower R₀ R N] (𝒩₀ : ℤ → Submodule R₀ N₀) [Decomposition 𝒩₀] (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩] (ψ : N₀ →ₗ[R₀] N) (n : ℤ) (θ : 𝒩₀ n →ₗ[R₀] 𝒩 n), IsBaseChange R ψ → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → (∀ y, (θ y : N) = ψ y) → IsBaseChange R θ := by
  intro R₀ R _ _ _ N₀ N _ _ _ _ _ _ 𝒩₀ _ 𝒩 _ ψ n θ h hdeg hθ
  let p₀ : N₀ →ₗ[R₀] 𝒩₀ n :=
    DirectSum.component R₀ ℤ (fun i => 𝒩₀ i) n ∘ₗ (decomposeLinearEquiv 𝒩₀).toLinearMap
  let p : N →ₗ[R] 𝒩 n :=
    DirectSum.component R ℤ (fun i => 𝒩 i) n ∘ₗ (decomposeLinearEquiv 𝒩).toLinearMap
  have hp₀ : ∀ y, p₀ y = decompose 𝒩₀ y n := fun _ => rfl
  have hp : ∀ y, p y = decompose 𝒩 y n := fun _ => rfl
  have hp₀i : ∀ y : 𝒩₀ n, p₀ (y : N₀) = y := fun y => by
    apply Subtype.ext
    rw [hp₀]
    exact decompose_of_mem_same 𝒩₀ y.2
  have hpi : ∀ y : 𝒩 n, p (y : N) = y := fun y => by
    apply Subtype.ext
    rw [hp]
    exact decompose_of_mem_same 𝒩 y.2
  have hcomm : ∀ y, θ (p₀ y) = p (ψ y) := by
    intro y
    induction y using Decomposition.inductionOn 𝒩₀ with
    | zero => simp
    | @homogeneous j y =>
      by_cases hj : j = n
      · subst hj
        rw [hp₀i, ← hθ, hpi]
      · have h1 : p₀ (y : N₀) = 0 := by
          apply Subtype.ext
          rw [hp₀]
          exact decompose_of_mem_ne 𝒩₀ y.2 hj
        have h2 : p (ψ y) = 0 := by
          apply Subtype.ext
          rw [hp]
          exact decompose_of_mem_ne 𝒩 (hdeg j y y.2) hj
        rw [h1, h2, map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
  let L : R ⊗[R₀] 𝒩₀ n →ₗ[R] 𝒩 n := LinearMap.liftBaseChange R θ
  have hL1 : ∀ x, L (p₀.baseChange R x) = p (h.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hcomm]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hL2 : ∀ x, (L x : N) = h.equiv ((𝒩₀ n).subtype.baseChange R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hθ]
    | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]
  have hret : ∀ x, p₀.baseChange R ((𝒩₀ n).subtype.baseChange R x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [hp₀i]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hbij : Function.Bijective L := by
    constructor
    · intro a b hab
      have h1 : h.equiv ((𝒩₀ n).subtype.baseChange R a)
          = h.equiv ((𝒩₀ n).subtype.baseChange R b) := by
        rw [← hL2, ← hL2, hab]
      rw [← hret a, h.equiv.injective h1, hret]
    · intro z
      refine ⟨p₀.baseChange R (h.equiv.symm z), ?_⟩
      rw [hL1, LinearEquiv.apply_symm_apply, hpi]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun x => ?_
  simp [L]

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem map_xProd_pow_smul_of_X {ι R₀ R : Type} [CommRing R₀] [CommRing R] {N₀ N : Type}
    [AddCommGroup N₀] [Module (MvPolynomial ι R₀) N₀] [AddCommGroup N]
    [Module (MvPolynomial ι R) N] (ψ : N₀ → N)
    (hX : ∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y)
    (s : Finset ι) (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by
  classical
  have h1 : ∀ y, ψ (xProd R₀ s • y) = xProd R s • ψ y := by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [xProd, xProd, Finset.prod_insert ha, Finset.prod_insert ha, mul_smul, mul_smul, hX, ih]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h1, ih]

theorem nonempty_baseChange_grCube_iso : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] (𝒩₀ : ℤ → Submodule R₀ N₀) [PolyGradedSMul ι 𝒩₀] [Decomposition 𝒩₀] (N : Type) [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩] [Decomposition 𝒩] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (n : ℤ), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → Nonempty (Cube.baseChange R (grCube ι 𝒩₀ n) ≅ grCube ι 𝒩 n) := by
  intro ι _ _ R₀ R _ _ _ N₀ _ _ _ _ 𝒩₀ _ _ N _ _ _ _ 𝒩 _ _ _ _ _ ψ n hψ hX hgr
  choose θ hθ hθe using fun s : Finset ι => GlobalTheory.exists_isBaseChange_away_xProd ι R₀ R N₀ N ψ s hψ hX
  have hg : ∀ s j, ∀ y ∈ homLoc 𝒩₀ s j, θ s y ∈ homLoc 𝒩 s j := by
    rintro s j _ ⟨k, m, hm, rfl⟩
    rw [hθe]
    exact awayFrac_mem_homLoc (hgr _ _ hm) rfl
  let η : ∀ s, homLoc 𝒩₀ s n →ₗ[R₀] homLoc 𝒩 s n := fun s =>
    { toFun := fun y => ⟨θ s y, hg s n _ y.2⟩
      map_add' := fun a b => Subtype.ext (map_add (θ s) a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul (θ s) r a.1) }
  have hη : ∀ s, IsBaseChange R (η s) := fun s =>
    GlobalTheory.isBaseChange_gradedPiece R₀ R _ _ (homLoc 𝒩₀ s) (homLoc 𝒩 s) (θ s) n (η s) (hθ s) (hg s) fun _ => rfl
  have hres : ∀ {s t : Finset ι} (h : s ⊆ t) (z : homLoc 𝒩₀ s n),
      η t (homLocRes 𝒩₀ h n z) = homLocRes 𝒩 h n (η s z) := by
    rintro s t h ⟨_, k, m, hm, rfl⟩
    apply Subtype.ext
    change θ t (locRes X N₀ h (awayFrac N₀ _ k m)) = locRes X N h (θ s (awayFrac N₀ _ k m))
    rw [hθe, locRes_awayFrac X h (Finset.prod_sdiff h).symm,
      locRes_awayFrac X h (Finset.prod_sdiff h).symm, hθe]
    exact congrArg _ (map_xProd_pow_smul_of_X ψ hX (t \ s) k m)
  have key : ∀ {s t : Finset ι} (h : s ⊆ t) (x : R ⊗[R₀] homLoc 𝒩₀ s n),
      (hη t).equiv ((homLocRes 𝒩₀ h n).baseChange R x) = homLocRes 𝒩 h n ((hη s).equiv x) := by
    intro s t h x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r z =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul,
        hres]
  exact ⟨Cube.isoMk (fun s => (hη s).equiv) fun h x => key h x⟩

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isGradedMap_mulVecLin {ι : Type} {R : Type*} [CommRing R] {κ μ : Type*} [Fintype μ]
    {d : κ → ℤ} {e : μ → ℤ} {Φ : Matrix κ μ (MvPolynomial ι R)}
    (h : ∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) :
    IsGradedMap (grFree ι R e) (grFree ι R d) Φ.mulVecLin := by
  intro n v hv
  refine mem_grPi.2 fun l => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, grShift_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have := grSMul_mem (polyGrading ι R) (h l j) (mem_grPi.1 hv j)
  rwa [smul_eq_mul, show n + -e j + (e j - d l) = n + -d l by ring] at this

theorem isHomogeneous_range_mulVecLin :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ)
      (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) →
        (LinearMap.range Φ.mulVecLin).IsHomogeneous (grFree ι R d) :=
  fun _ _ _ _ _ _ _ _ _ _ h => (isGradedMap_mulVecLin h).isHomogeneous_range

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem nonempty_homLoc_singleton_equiv_quotSMulTop : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Nonempty (homLoc ℳ {i} 0 ≃ₗ[R] QuotSMulTop (X i - 1 : MvPolynomial ι R) M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  obtain ⟨-, h2, h3⟩ := GlobalTheory.X_sub_one_smul_graded ι R M ℳ i
  let K : Submodule (MvPolynomial ι R) M := (X i - 1 : MvPolynomial ι R) • ⊤
  have hK : ∀ y : M, y ∈ K ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := fun y => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨w, _, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, trivial, h.symm⟩⟩
  let φ : ∀ k : ℕ, ℳ (0 + k * (({i} : Finset ι).card : ℤ)) →ₗ[R]
      QuotSMulTop (X i - 1 : MvPolynomial ι R) M :=
    fun k => (K.mkQ.restrictScalars R) ∘ₗ (ℳ _).subtype
  have hφv : ∀ k m, φ k m = Submodule.Quotient.mk (m : M) := fun _ _ => rfl
  have hφ : ∀ (k : ℕ) (m : ℳ (0 + k * (({i} : Finset ι).card : ℤ)))
      (m' : ℳ (0 + (k + 1 : ℕ) * (({i} : Finset ι).card : ℤ))),
      (m' : M) = xProd R {i} • (m : M) → φ (k + 1) m' = φ k m := by
    intro k m m' h
    rw [hφv, hφv, Submodule.Quotient.eq]
    refine (hK _).2 ⟨m, ?_⟩
    rw [h, sub_smul, one_smul, xProd, Finset.prod_singleton]
  refine ⟨LinearEquiv.ofBijective (homLocLift φ hφ) ⟨?_, ?_⟩⟩
  · rw [homLocLift_injective_iff]
    intro k m hm
    rw [hφv, Submodule.Quotient.mk_eq_zero] at hm
    obtain ⟨w, hw⟩ := (hK _).1 hm
    obtain ⟨l, hl⟩ := h2 _ _ w m.2 hw
    exact ⟨l, by rwa [xProd, Finset.prod_singleton]⟩
  · rw [homLocLift_surjective_iff]
    intro t
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    obtain ⟨n₀, hn⟩ := h3 y
    obtain ⟨y', hy', w, hw⟩ := hn (0 + (n₀.toNat : ℕ) * (({i} : Finset ι).card : ℤ))
      (by simp)
    refine ⟨n₀.toNat, ⟨y', hy'⟩, ?_⟩
    rw [hφv, eq_comm, Submodule.Quotient.eq]
    exact (hK _).2 ⟨w, by rw [hw, add_sub_cancel_left]⟩

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_sum_mul_of_mem_span_range_sq {S : Type} [CommRing S] {r : ℕ} (g : Fin r → S)
    (x : S) (hx : x ∈ Ideal.span (Set.range g) * Ideal.span (Set.range g)) :
    ∃ b : Fin r → Fin r → S, x = ∑ k, ∑ l, b k l * (g k * g l) := by

  have hx' : x ∈ Ideal.span (Set.range fun p : Fin r × Fin r => g p.1 * g p.2) := by
    open Pointwise in
    have hset : Set.range g * Set.range g =
        Set.range fun p : Fin r × Fin r => g p.1 * g p.2 := by
      ext y
      simp [Set.mem_mul]
    open Pointwise in
    rwa [Ideal.span_mul_span', hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hx'
  refine ⟨fun k l => c (k, l), ?_⟩
  rw [← hc, Fintype.sum_prod_type]
  simp only [smul_eq_mul]

theorem exists_witnesses_of_formallySmooth_quotient :
    ∀ (ι : Type) [Fintype ι] (R : Type) [CommRing R] (r : ℕ) (g : Fin r → MvPolynomial ι R), Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) → ∃ (a : ι → Fin r → MvPolynomial ι R) (b : Fin r → Fin r → Fin r → MvPolynomial ι R), ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l) := by
  intro ι _ R _ r g hs
  set I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range g) with hI
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I

  obtain ⟨σ, hσ⟩ := (Algebra.FormallySmooth.iff_split_surjection _ hsurj).1 hs
  have hK : RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom = I := by
    ext x
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem

  have hlift : ∀ i : ι, ∃ y : MvPolynomial ι R,
      Ideal.Quotient.mk _ y = σ (Ideal.Quotient.mkₐ R I (X i)) :=
    fun i => Ideal.Quotient.mk_surjective _
  choose y hy using hlift

  have hdiff : ∀ i, y i - X i ∈ I := by
    intro i
    have h1 := congrArg (Ideal.Quotient.mkₐ R I).kerSquareLift (hy i)
    rw [AlgHom.kerSquareLift_mk, ← AlgHom.comp_apply, hσ, AlgHom.id_apply] at h1
    exact Ideal.Quotient.eq.1 h1
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 (hdiff i)
  have hy' : ∀ i, X i + ∑ k, a i k * g k = y i := by
    intro i
    have := ha i
    simp only [smul_eq_mul] at this
    rw [this]
    ring

  have hcomp : (Ideal.Quotient.mkₐ R _).comp
      (aeval fun i => X i + ∑ k, a i k * g k : MvPolynomial ι R →ₐ[R] MvPolynomial ι R) =
      σ.comp (Ideal.Quotient.mkₐ R I) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X, hy', AlgHom.comp_apply, ← hy i]
    rfl

  have hmem : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) ∈ I * I := by
    intro j
    have hgj : Ideal.Quotient.mkₐ R I (g j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := AlgHom.congr_fun hcomp (g j)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hgj, map_zero, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, hK, pow_two] at h2
    exact h2
  choose b hb using fun j => exists_sum_mul_of_mem_span_range_sq g _ (hmem j)
  exact ⟨a, b, hb⟩

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

open scoped Pointwise

namespace GlobalTheory

theorem flat_quotSMulTop_coker_of_matrix_witnesses :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (r a b : ℕ) (g : Fin r → S) (u : S) (Φ : Matrix (Fin a) (Fin b) S), Module.Flat R (S ⧸ Ideal.span (Set.range g)) → (∃ c : Fin r → S, u = ∑ k, c k * g k) → (∀ k, ∃ (C : Matrix (Fin b) (Fin a) S) (C' : Matrix (Fin a) (Fin a) S), g k • (1 : Matrix (Fin a) (Fin a) S) = Φ * C + u • C') → (∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S), Φ * Ψ * Φ = Φ + ∑ k, g k • E k) → Module.Flat R (QuotSMulTop u ((Fin a → S) ⧸ LinearMap.range Φ.mulVecLin)) := by
  intro R S _ _ _ r a b g u Φ hflat hu hker hreg
  obtain ⟨c, hc⟩ := hu
  obtain ⟨Ψ, E, hΨ⟩ := hreg
  let I : Ideal S := Ideal.span (Set.range g)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have huI : u ∈ I := by
    rw [hc]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hgI k)
  have hmv : ∀ {m : ℕ} (A : Matrix (Fin a) (Fin m) S), (∀ j i, A j i ∈ I) →
      ∀ y j, (Matrix.mulVec A y) j ∈ I := by
    intro m A hA y j
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hA j i)
  let K := LinearMap.range Φ.mulVecLin
  let M := (Fin a → S) ⧸ K
  let T : Submodule S M := u • (⊤ : Submodule S M)
  let pr : (Fin a → S) →ₗ[S] QuotSMulTop u M := T.mkQ ∘ₗ K.mkQ
  have hK : ∀ y, pr (Matrix.mulVec Φ y) = 0 := by
    intro y
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    have hy : K.mkQ (Matrix.mulVec Φ y) = 0 := (Submodule.Quotient.mk_eq_zero K).2 ⟨y, rfl⟩
    rw [hy, Submodule.Quotient.mk_zero]
  have hU : ∀ z, pr (u • z) = 0 := by
    intro z
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [map_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hG : ∀ k x, g k • pr x = 0 := by
    intro k x
    obtain ⟨C, C', h⟩ := hker k
    have hx : g k • x = Matrix.mulVec Φ (Matrix.mulVec C x) + u • Matrix.mulVec C' x := by
      have := congrArg (fun A => Matrix.mulVec A x) h
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec] at this
      exact this
    rw [← map_smul, hx, map_add, hK, hU, add_zero]
  have hI : ∀ s ∈ I, ∀ x, s • pr x = 0 := by
    intro s hs x
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hs
    simp only [Finset.sum_smul, smul_eq_mul, mul_smul, hG, smul_zero, Finset.sum_const_zero]
  let q : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) :=
    LinearMap.pi fun j => (Submodule.mkQ I) ∘ₗ LinearMap.proj j
  have hq : ∀ v, (∀ j, v j ∈ I) → q v = 0 := by
    intro v hv
    funext j
    exact (Submodule.Quotient.mk_eq_zero I).2 (hv j)
  have hqI : ∀ s ∈ I, ∀ w : Fin a → S ⧸ I, s • w = 0 := by
    intro s hs w
    funext j
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective I (w j)
    rw [Pi.smul_apply, ← ht, ← Submodule.Quotient.mk_smul, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hs
  have hE : ∀ j i, (∑ k, g k • E k) j i ∈ I := by
    intro j i
    rw [Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hgI k)
  let f0 : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) := q ∘ₗ (LinearMap.id - (Φ * Ψ).mulVecLin)
  have h1 : K ≤ LinearMap.ker f0 := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [f0, LinearMap.comp_apply]
    apply hq
    intro j
    have hy : Φ.mulVecLin y - (Φ * Ψ).mulVecLin (Φ.mulVecLin y) = -(Matrix.mulVec (∑ k, g k • E k) y) := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hΨ, Matrix.add_mulVec]
      abel
    rw [LinearMap.sub_apply, LinearMap.id_apply, hy, Pi.neg_apply]
    exact Submodule.neg_mem _ (hmv _ hE y j)
  let f1 : M →ₗ[S] (Fin a → S ⧸ I) := K.liftQ f0 h1
  have h2 : T ≤ LinearMap.ker f1 := by
    intro m hm
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    rw [LinearMap.mem_ker, map_smul]
    exact hqI u huI _
  let i : QuotSMulTop u M →ₗ[S] (Fin a → S ⧸ I) := T.liftQ f1 h2
  let p : (Fin a → S ⧸ I) →ₗ[S] QuotSMulTop u M :=
    ∑ j, (Submodule.liftQ I (LinearMap.toSpanSingleton S _ (pr (Pi.single j 1)))
      (fun s hs => by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
        exact hI s hs _)) ∘ₗ LinearMap.proj j
  have hpq : ∀ v, p (q v) = pr v := by
    intro v
    simp only [p, q, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply]
    conv_rhs => rw [← Finset.univ_sum_single v, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    refine congrArg pr ?_
    funext k
    by_cases h : k = j <;> simp [h]
  have hpi : p ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun n => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective T n
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K m
    show p (q (x - (Φ * Ψ).mulVecLin x)) = pr x
    rw [hpq, map_sub, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hK, sub_zero]
  have := hflat
  have : Module.Flat R (Fin a → S ⧸ I) :=
    Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin a => S ⧸ I)).symm
  exact Module.Flat.of_retract (i.restrictScalars R) (p.restrictScalars R)
    (LinearMap.ext fun n => LinearMap.congr_fun hpi n)

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
private theorem exists_generalized_inverse_mod_ideal {R S B P : Type} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing B] [Algebra R B] [AddCommGroup P] [Module B P] {a b r : ℕ}
    (Φ : Matrix (Fin a) (Fin b) S) (u : S) (g : Fin r → S) (π : S →ₐ[R] B)
    (hker : RingHom.ker (π : S →+* B) = Ideal.span (Set.range g))
    (hπ : Function.Surjective π) (ε : (Fin a → S) →ₛₗ[(π : S →+* B)] P)
    (hproj : Module.Projective B P) (hε : Function.Surjective ε)
    (hkerε : ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + u • w') (hu : π u = 0) :
    ∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S),
      Φ * Ψ * Φ = Φ + ∑ k, g k • E k := by
  classical
  let p : Fin a → P := fun m => ε (Pi.single m 1)
  have hεsum : ∀ y : Fin a → S, ε y = ∑ m, π (y m) • p m := by
    intro y
    conv_lhs => rw [show y = ∑ m, y m • Pi.single m 1 from by
      funext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, p]
  let F : (Fin a → B) →ₗ[B] P := Fintype.linearCombination B p
  have hF : ∀ β, F β = ∑ m, β m • p m := fun β => Fintype.linearCombination_apply B p β
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨y, rfl⟩ := hε x
    exact ⟨fun m => π (y m), by rw [hF, hεsum]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property F LinearMap.id hFsurj
  have hlift : ∀ β : Fin a → B, ∃ y : Fin a → S, (fun m => π (y m)) = β := by
    intro β
    choose y hy using fun m => hπ (β m)
    exact ⟨y, funext hy⟩
  have hcol : ∀ m : Fin a, ∃ w : Fin b → S,
      (fun j => π ((Φ.mulVec w) j)) = Pi.single m 1 - s (p m) := by
    intro m
    obtain ⟨y, hy⟩ := hlift (Pi.single m 1 - s (p m))
    have h0 : ε y = 0 := by
      rw [hεsum, ← hF]
      have : (fun m => π (y m)) = Pi.single m 1 - s (p m) := hy
      rw [show (fun m => π (y m)) = _ from this, map_sub, hF]
      have hs' : F (s (p m)) = p m := by
        have := congr_arg (fun φ => φ (p m)) hs
        simpa using this
      rw [hs']
      simp [Pi.single_apply]
    obtain ⟨w, w', hw⟩ := (hkerε y).1 h0
    refine ⟨w, ?_⟩
    rw [← hy, hw]
    funext j
    simp [hu]
  choose w hw using hcol
  have hs' : ∀ x, F (s x) = x := fun x => by
    have := congr_arg (fun φ => φ x) hs
    simpa using this
  have hcolε : ∀ j, ε (fun l => Φ l j) = 0 := by
    intro j
    refine (hkerε _).2 ⟨Pi.single j 1, 0, ?_⟩
    funext l
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  let Ψ : Matrix (Fin b) (Fin a) S := Matrix.of fun j m => w m j
  have hD : ∀ l j, (Φ * Ψ * Φ - Φ) l j ∈ Ideal.span (Set.range g) := by
    intro l j
    rw [← hker, RingHom.mem_ker]
    have hcomp : ∀ m, π ((Φ * Ψ) l m) = (Pi.single m 1 - s (p m) : Fin a → B) l := by
      intro m
      have := congr_fun (hw m) l
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ψ] using this
    have hsum : ∑ m, π (Φ m j) • s (p m) = 0 := by
      have h1 := hεsum (fun l => Φ l j)
      rw [hcolε j] at h1
      simp_rw [← LinearMap.map_smul, ← map_sum, ← h1, map_zero]
    have hsuml := congr_fun hsum l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsuml
    rw [Matrix.sub_apply, map_sub, Matrix.mul_apply, map_sum]
    simp only [AlgHom.coe_toRingHom, map_mul, hcomp, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [show ∑ m, s (p m) l * π (Φ m j) = ∑ m, π (Φ m j) * s (p m) l from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, hsuml]
    ring
  choose c hc using fun l j => (Submodule.mem_span_range_iff_exists_fun S).1 (hD l j)
  refine ⟨Ψ, fun k => Matrix.of fun l j => c l j k, ?_⟩
  ext l j
  have h1 := hc l j
  simp only [smul_eq_mul] at h1
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [show ∑ k, g k * c l j k = ∑ k, c l j k * g k from Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
  simp

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
private theorem chart_witnesses_lemma {ι : Type} [Fintype ι] {R : Type} [CommRing R] {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (i : ι)
    (H : ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P) (ε : (Fin a → MvPolynomial ι R) →ₛₗ[(π : MvPolynomial ι R →+* B)] P), Algebra.Smooth R B ∧ Module.Projective B P ∧ Function.Surjective π ∧ π (X i) = 1 ∧ Function.Surjective ε ∧ ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w') :
    ∃ (r : ℕ) (g : Fin r → MvPolynomial ι R),
      Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) ∧
      (∃ c : Fin r → MvPolynomial ι R, (X i - 1 : MvPolynomial ι R) = ∑ k, c k * g k) ∧
      (∀ k, ∃ (C : Matrix (Fin b) (Fin a) (MvPolynomial ι R)) (C' : Matrix (Fin a) (Fin a) (MvPolynomial ι R)),
        g k • (1 : Matrix (Fin a) (Fin a) (MvPolynomial ι R)) = Φ * C + (X i - 1 : MvPolynomial ι R) • C') ∧
      (∃ (Ψ : Matrix (Fin b) (Fin a) (MvPolynomial ι R)) (E : Fin r → Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
        Φ * Ψ * Φ = Φ + ∑ k, g k • E k) := by
  classical
  obtain ⟨B, _, _, π, P, _, _, ε, hsm, hproj, hπ, hX, hεs, hkerε⟩ := H
  have hfg := Algebra.FinitePresentation.ker_fG_of_surjective π hπ
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hker : RingHom.ker (π : MvPolynomial ι R →+* B) = Ideal.span (Set.range g) := hg.symm
  have hu : π (X i - 1) = 0 := by rw [map_sub, hX, map_one, sub_self]
  refine ⟨r, g, ?_, ?_, ?_, ?_⟩
  · have e : (MvPolynomial ι R ⧸ RingHom.ker (π : MvPolynomial ι R →+* B)) ≃ₐ[R] B :=
      Ideal.quotientKerAlgEquivOfSurjective hπ
    have : Algebra.FormallySmooth R (MvPolynomial ι R ⧸ RingHom.ker (π : MvPolynomial ι R →+* B)) :=
      Algebra.FormallySmooth.of_equiv e.symm
    rw [hker] at this
    exact this
  · have hmem : (X i - 1 : MvPolynomial ι R) ∈ Ideal.span (Set.range g) := by
      rw [← hker, RingHom.mem_ker]; exact hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 hmem
    exact ⟨c, by rw [← hc]; simp [smul_eq_mul]⟩
  · intro k
    have hgk : π (g k) = 0 := by
      have : g k ∈ RingHom.ker (π : MvPolynomial ι R →+* B) := by
        rw [hker]; exact Ideal.subset_span ⟨k, rfl⟩
      exact this
    have hcol : ∀ m : Fin a, ∃ w w', g k • (Pi.single m 1 : Fin a → MvPolynomial ι R) =
        Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w' := by
      intro m
      refine (hkerε _).1 ?_
      rw [LinearMap.map_smulₛₗ]
      simp [hgk]
    choose w w' hw using hcol
    refine ⟨Matrix.of fun j m => w m j, Matrix.of fun l m => w' m l, ?_⟩
    ext l m
    have h1 := congr_fun (hw m) l
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply] at h1
    simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, smul_eq_mul]
    rw [h1]
    simp [Matrix.mulVec, dotProduct]
  · exact exists_generalized_inverse_mod_ideal Φ (X i - 1) g π hker hπ ε hproj hεs hkerε hu

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
private theorem formallySmooth_quotient_of_aeval_shift_mem_sq {ι R : Type} [CommRing R] {r : ℕ}
    (g : Fin r → MvPolynomial ι R) (a : ι → Fin r → MvPolynomial ι R)
    (b : Fin r → Fin r → Fin r → MvPolynomial ι R)
    (h : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) :
    Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) := by
  set I := Ideal.span (Set.range g) with hI
  let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I := Ideal.Quotient.mkₐ R I
  have hkerf : RingHom.ker f.toRingHom = I := Ideal.Quotient.mkₐ_ker R I
  let x : ι → MvPolynomial ι R := fun i => X i + ∑ k, a i k * g k
  let φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ R _).comp (aeval x)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have hφ : ∀ p ∈ I, φ p = 0 := by
    have hle : I ≤ RingHom.ker φ := by
      show Ideal.span (Set.range g) ≤ RingHom.ker φ
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      show Ideal.Quotient.mk _ (aeval x (g j)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hkerf, h j, pow_two]
      exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ =>
        Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (hgI k) (hgI l))
    exact fun p hp => hle hp
  let s := Ideal.Quotient.liftₐ I φ hφ
  refine Algebra.FormallySmooth.of_split f s ?_
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hs : s (Ideal.Quotient.mkₐ R I (X i)) = Ideal.Quotient.mk _ (x i) := by
    show (Ideal.Quotient.liftₐ I φ hφ) (Ideal.Quotient.mk I (X i)) = _
    rw [Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
    show (Ideal.Quotient.mkₐ R _) (aeval x (X i)) = _
    rw [aeval_X]
    rfl
  simp only [AlgHom.comp_apply, hs, AlgHom.id_apply]
  rw [AlgHom.kerSquareLift_mk]
  simp [f, x, Ideal.Quotient.eq_zero_iff_mem.2 (hgI _)]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in

theorem _root_.GlobalTheory.exists_noetherian_subring_homogeneous_matrix_flat_charts :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)), (∀ l j, Φ l j ∈ _root_.GlobalTheory.polyGrading ι R (e j - d l)) → (∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P) (ε : (Fin a → MvPolynomial ι R) →ₛₗ[(π : MvPolynomial ι R →+* B)] P), Algebra.Smooth R B ∧ Module.Projective B P ∧ Function.Surjective π ∧ π (X i) = 1 ∧ Function.Surjective ε ∧ ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w') → ∃ (R₀ : Subring R) (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)), IsNoetherianRing R₀ ∧ Φ₀.map (MvPolynomial.map R₀.subtype) = Φ ∧ (∀ l j, Φ₀ l j ∈ _root_.GlobalTheory.polyGrading ι R₀ (e j - d l)) ∧ ∀ i : ι, Module.Flat R₀ (QuotSMulTop (X i - 1 : MvPolynomial ι R₀) ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin)) := by
  intro ι _ _ R _ a b d e Φ hΦ H
  classical
  choose r g hsm hc hC hΨ using fun i => chart_witnesses_lemma Φ i (H i)
  choose wa wb hwit using fun i => _root_.GlobalTheory.exists_witnesses_of_formallySmooth_quotient ι R (r i) (g i) (hsm i)
  choose c hc' using hc
  choose C C' hCC using hC
  choose Ψ E hΨE using hΨ
  let pols : (Fin a × Fin b) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, ι × Fin (r i)) ⊕
      (Σ i, Fin (r i) × Fin (r i) × Fin (r i)) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, Fin (r i) × Fin b × Fin a) ⊕
      (Σ i, Fin (r i) × Fin a × Fin a) ⊕ (Σ i, Fin b × Fin a) ⊕ (Σ i, Fin (r i) × Fin a × Fin b) →
      MvPolynomial ι R :=
    Sum.elim (fun x => Φ x.1 x.2) (Sum.elim (fun x => g x.1 x.2) (Sum.elim (fun x => wa x.1 x.2.1 x.2.2)
      (Sum.elim (fun x => wb x.1 x.2.1 x.2.2.1 x.2.2.2) (Sum.elim (fun x => c x.1 x.2)
      (Sum.elim (fun x => C x.1 x.2.1 x.2.2.1 x.2.2.2) (Sum.elim (fun x => C' x.1 x.2.1 x.2.2.1 x.2.2.2)
      (Sum.elim (fun x => Ψ x.1 x.2.1 x.2.2) (fun x => E x.1 x.2.1 x.2.2.1 x.2.2.2))))))))
  let T : Set R := ⋃ j, ↑(pols j).coeffs
  have hT : T.Finite := Set.finite_iUnion fun j => Finset.finite_toSet _
  let R₀ := Subring.closure T
  have hnoeth : IsNoetherianRing R₀ := is_noetherian_subring_closure T hT
  let φ : MvPolynomial ι R₀ →+* MvPolynomial ι R := MvPolynomial.map R₀.subtype
  have hφinj : Function.Injective φ := MvPolynomial.map_injective _ Subtype.val_injective
  have hlift : ∀ j, ∃ p₀, φ p₀ = pols j := by
    intro j
    have : pols j ∈ Set.range φ := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro x hx
      exact ⟨⟨x, Subring.subset_closure (Set.mem_iUnion.2 ⟨j, hx⟩)⟩, rfl⟩
    exact this
  choose L hL using hlift
  let Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀) := Matrix.of fun l j => L (Sum.inl (l, j))
  let g₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀ := fun i k => L (Sum.inr (Sum.inl ⟨i, k⟩))
  let wa₀ : ∀ i, ι → Fin (r i) → MvPolynomial ι R₀ := fun i v k =>
    L (Sum.inr (Sum.inr (Sum.inl ⟨i, v, k⟩)))
  let wb₀ : ∀ i, Fin (r i) → Fin (r i) → Fin (r i) → MvPolynomial ι R₀ := fun i j k l =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, k, l⟩))))
  let c₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀ := fun i k =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩)))))
  let C₀ : ∀ i, Fin (r i) → Matrix (Fin b) (Fin a) (MvPolynomial ι R₀) := fun i k => Matrix.of fun j m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, j, m⟩))))))
  let C'₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin a) (MvPolynomial ι R₀) := fun i k => Matrix.of fun l m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, l, m⟩)))))))
  let Ψ₀ : ∀ i, Matrix (Fin b) (Fin a) (MvPolynomial ι R₀) := fun i => Matrix.of fun j m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, m⟩))))))))
  let E₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin b) (MvPolynomial ι R₀) := fun i k => Matrix.of fun l j =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, k, l, j⟩))))))))
  have hΦ₀ : ∀ l j, φ (Φ₀ l j) = Φ l j := fun l j => hL _
  have hg₀ : ∀ i k, φ (g₀ i k) = g i k := fun i k => hL _
  have hwa₀ : ∀ i v k, φ (wa₀ i v k) = wa i v k := fun i v k => hL _
  have hwb₀ : ∀ i j k l, φ (wb₀ i j k l) = wb i j k l := fun i j k l => hL _
  have hc₀ : ∀ i k, φ (c₀ i k) = c i k := fun i k => hL _
  have hC₀ : ∀ i k j m, φ (C₀ i k j m) = C i k j m := fun i k j m => hL _
  have hC'₀ : ∀ i k l m, φ (C'₀ i k l m) = C' i k l m := fun i k l m => hL _
  have hΨ₀ : ∀ i j m, φ (Ψ₀ i j m) = Ψ i j m := fun i j m => hL _
  have hE₀ : ∀ i k l j, φ (E₀ i k l j) = E i k l j := fun i k l j => hL _
  have hφX : ∀ v, φ (X v) = X v := fun v => MvPolynomial.map_X _ _
  refine ⟨R₀, Φ₀, hnoeth, ?_, ?_, ?_⟩
  · exact Matrix.ext fun l j => hΦ₀ l j
  · intro l j
    rw [_root_.GlobalTheory.mem_polyGrading_iff]
    intro α hα
    refine (_root_.GlobalTheory.mem_polyGrading_iff.1 (hΦ l j)) α ?_
    rw [← hΦ₀ l j, MvPolynomial.coeff_map]
    intro h0
    exact hα (Subtype.val_injective (by simpa using h0))
  · intro i
    have hwit₀ : ∀ j, aeval (fun v => X v + ∑ k, wa₀ i v k * g₀ i k) (g₀ i j) =
        ∑ k, ∑ l, wb₀ i j k l * (g₀ i k * g₀ i l) := by
      intro j
      apply hφinj
      rw [aeval_eq_bind₁, MvPolynomial.map_bind₁]
      simp only [φ] at hg₀ hwa₀ hwb₀ hφX ⊢
      simp only [map_add, map_sum, map_mul, hg₀, hwa₀, hwb₀, hφX]
      rw [← aeval_eq_bind₁]
      exact hwit i j
    haveI : Algebra.FormallySmooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      formallySmooth_quotient_of_aeval_shift_mem_sq (g₀ i) (wa₀ i) (wb₀ i) hwit₀
    haveI : Algebra.FinitePresentation R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      Algebra.FinitePresentation.of_finiteType.1 inferInstance
    haveI : Algebra.Smooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      ⟨inferInstance, inferInstance⟩
    refine _root_.GlobalTheory.flat_quotSMulTop_coker_of_matrix_witnesses R₀ (MvPolynomial ι R₀) (r i) a b (g₀ i)
      (X i - 1) Φ₀ inferInstance ⟨c₀ i, ?_⟩ (fun k => ⟨C₀ i k, C'₀ i k, ?_⟩) ⟨Ψ₀ i, E₀ i, ?_⟩
    · apply hφinj
      simp only [map_sub, map_one, map_sum, map_mul, hc₀, hg₀, hφX]
      exact hc' i
    · refine Matrix.ext fun l m => ?_
      apply hφinj
      have h1 := congr_fun (congr_fun (hCC i k) l) m
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
        smul_eq_mul] at h1 ⊢
      simp only [map_add, map_mul, map_sum, map_sub, map_one, hg₀, hφX, hΦ₀, hC₀, hC'₀,
        apply_ite φ, map_zero, map_one]
      simpa [Φ₀, C₀, C'₀] using h1
    · refine Matrix.ext fun l j => ?_
      apply hφinj
      have h1 := congr_fun (congr_fun (hΨE i) l) j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul] at h1 ⊢
      simp only [map_add, map_mul, map_sum, hΦ₀, hΨ₀, hE₀, hg₀]
      exact h1

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

private theorem flat_loc_over_algebra {A S M N : Type} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M] [AddCommGroup N] [Module A N]
    [Module S N] [IsScalarTower A S N] (T : Submonoid S) (f : M →ₗ[S] N) [IsLocalizedModule T f]
    (h : Module.Flat A M) : Module.Flat A N := by
  rw [Module.Flat.iff_lTensor_injectiveₛ] at h ⊢
  intro P _ _ Q
  have := IsLocalizedModule.map_injective T (AlgebraTensorModule.rTensor A Q f)
    (AlgebraTensorModule.rTensor A P f) (AlgebraTensorModule.lTensor S M Q.subtype) (h Q)
  rw [IsLocalizedModule.map_lTensor] at this
  exact this

private theorem flat_iff_forall_piece {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ] :
    Module.Flat R M ↔ ∀ n, Module.Flat R (ℳ n) :=
  (Module.Flat.equiv_iff (decomposeLinearEquiv ℳ)).trans Module.Flat.directSum_iff

theorem flat_homLoc_of_flat_homLoc_singleton :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
      [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
      (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) (s : Finset ι)
      (n : ℤ), i ∈ s → Module.Flat R (homLoc ℳ {i} 0) → Module.Flat R (homLoc ℳ s n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i s n hi h0
  have step (t : ℤ) : Module.Flat R (homLoc ℳ {i} t) ↔ Module.Flat R (homLoc ℳ {i} (t + 1)) :=
    Module.Flat.equiv_iff (LinearEquiv.ofBijective _
      (homLocSMul_X_bijective ℳ (Finset.mem_singleton_self i) t))
  have hall (t : ℤ) : Module.Flat R (homLoc ℳ {i} t) := by
    induction t using Int.induction_on with
    | zero => exact h0
    | succ k ih => exact (step _).1 ih
    | pred k ih => exact (step _).2 (by rwa [sub_add_cancel])
  have h1 := (flat_iff_forall_piece (homLoc ℳ {i})).2 hall
  have hsub : ({i} : Finset ι) ⊆ s := Finset.singleton_subset_iff.2 hi
  have hc : xProd R s = xProd R (s \ {i}) * xProd R {i} := (Finset.prod_sdiff hsub).symm
  have h2 : IsLocalizedModule.Away (xProd R (s \ {i}) * xProd R {i})
      (locRes X M hsub ∘ₗ LocalizedModule.mkLinearMap (.powers (xProd R {i})) M) := by
    rw [locRes_comp_mkLinearMap, ← hc]
    exact localizedModuleIsLocalizedModule _
  have h3 : IsLocalizedModule.Away (xProd R (s \ {i})) (locRes X M hsub) :=
    isLocalizedModule_away_of_comp (b := xProd R {i})
      (LocalizedModule.mkLinearMap (.powers (xProd R {i})) M) _
  have h4 := flat_loc_over_algebra (A := R) (.powers (xProd R (s \ {i}))) (locRes X M hsub) h1
  exact (flat_iff_forall_piece (homLoc ℳ s)).1 h4 n

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
theorem _root_.GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) M) → ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M) := by
  first | exact @GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot | exact GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot | (intros; apply GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem exists_pow_smul_eq_add_sub_one_smul {S M : Type} [CommRing S] [AddCommGroup M]
    [Module S M] (x : S) (k : ℕ) (y : M) : ∃ w : M, x ^ k • y = y + (x - 1) • w := by
  refine ⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩
  rw [smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

private lemma comap_ker_inf_smul_whole_eq_smul_whole_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) :
    Submodule.comap (LinearMap.ker φ).subtype (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F)) =
      u • (⊤ : Submodule S (LinearMap.ker φ)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨-, hx⟩
    obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have hvK : v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply hreg
      rw [← map_smul, hv]
      exact LinearMap.mem_ker.mp x.2
    have hx' : x = u • (⟨v, hvK⟩ : LinearMap.ker φ) := Subtype.ext hv.symm
    rw [hx']
    exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine ⟨(u • b).2, ?_⟩
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem_pointwise_smul (b : F) u ⊤ Submodule.mem_top

private lemma ker_sup_smul_whole_eq_ker_mkQ_comp {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    LinearMap.ker φ ⊔ u • (⊤ : Submodule S F) =
      LinearMap.ker ((u • (⊤ : Submodule S G)).mkQ ∘ₗ φ) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [LinearMap.comp_apply, hy, map_zero]
    · intro y hy
      obtain ⟨v, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨k, v, hk, rfl⟩ := hker y w hw.symm
    exact Submodule.add_mem_sup (LinearMap.mem_ker.mpr hk)
      (Submodule.smul_mem_pointwise_smul v u ⊤ Submodule.mem_top)

theorem finite_quotSMulTop_ker_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) [Module.Finite S F]
    [Module.FinitePresentation S (QuotSMulTop u G)]
    (hsurj : ∀ z : G, ∃ (y : F) (w : G), φ y = z + u • w)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    Module.Finite S (QuotSMulTop u (LinearMap.ker φ)) := by
  let ψ : F →ₗ[S] QuotSMulTop u G := (u • (⊤ : Submodule S G)).mkQ ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (u • (⊤ : Submodule S G)) z
    obtain ⟨y, w, hy⟩ := hsurj z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hy, add_sub_cancel_left]
    exact Submodule.smul_mem_pointwise_smul w u ⊤ Submodule.mem_top
  have hfg : (LinearMap.ker ψ).FG := Module.FinitePresentation.fg_ker ψ hψ
  have hfin : Module.Finite S ↥(LinearMap.ker φ ⊔ u • (⊤ : Submodule S F)) := by
    rw [ker_sup_smul_whole_eq_ker_mkQ_comp u φ hker]
    exact Module.Finite.iff_fg.mpr hfg
  have h2 : Module.Finite S (LinearMap.ker φ ⧸ Submodule.comap (LinearMap.ker φ).subtype
      (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F))) :=
    Module.Finite.equiv (LinearMap.quotientInfEquivSupQuotient (LinearMap.ker φ)
      (u • (⊤ : Submodule S F))).symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ (u • (⊤ : Submodule S (LinearMap.ker φ)))
    (comap_ker_inf_smul_whole_eq_smul_whole_of_regular u φ hreg))

theorem finite_quotSMulTop_ker_of_graded :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (F : Type) [AddCommGroup F] [Module R F] [Module (MvPolynomial ι R) F] [IsScalarTower R (MvPolynomial ι R) F] (ℱ : ℤ → Submodule R F) [PolyGradedSMul ι ℱ] [Decomposition ℱ] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢] (φ : F →ₗ[MvPolynomial ι R] G) (i : ι), IsGradedMap ℱ 𝒢 φ → Module.Finite (MvPolynomial ι R) F → (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ) → Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G) → Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) (LinearMap.ker φ)) := by
  intro ι _ _ R _ F _ _ _ _ ℱ _ _ G _ _ _ _ 𝒢 _ _ φ i hφ hF hpow hfp
  obtain ⟨hregG, hkillG, -⟩ := X_sub_one_smul_graded ι R G 𝒢 i
  obtain ⟨-, -, hhomF⟩ := X_sub_one_smul_graded ι R F ℱ i
  refine finite_quotSMulTop_ker_of_regular (X i - 1 : MvPolynomial ι R) φ hregG ?_ ?_
  · intro z
    obtain ⟨k, hk⟩ := hpow z
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hk
    obtain ⟨w, hw⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k z
    exact ⟨y, w, hy.trans hw⟩
  · intro y w hyw
    obtain ⟨n₀, hn⟩ := hhomF y
    obtain ⟨y', hy', v₀, hyv⟩ := hn n₀ le_rfl
    have hφy' : φ y' ∈ 𝒢 n₀ := hφ hy'
    have h1 : φ y = φ y' + (X i - 1 : MvPolynomial ι R) • φ v₀ := by
      rw [hyv, map_add, map_smul]
    have h2 : φ y' = (X i - 1 : MvPolynomial ι R) • (w - φ v₀) := by
      rw [smul_sub, ← hyw, h1]
      abel
    obtain ⟨k, hk⟩ := hkillG n₀ (φ y') (w - φ v₀) hφy' h2
    obtain ⟨w₁, hw₁⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k y'
    refine ⟨(X i : MvPolynomial ι R) ^ k • y', v₀ - w₁, ?_, ?_⟩
    · rw [map_smul, hk]
    · rw [hyv, hw₁, smul_sub]
      abel

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_graded_presentation_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢], (∀ i : ι, Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G)) → ∃ (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (ψ : ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin) →ₗ[MvPolynomial ι R] G), (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) ∧ IsGradedMap (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 ψ ∧ ∀ i : ι, (∀ y, ψ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧ (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ) := by
  intro ι _ _ R _ G _ _ _ _ 𝒢 _ _ hG
  obtain ⟨a, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 fun i =>
    GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R G 𝒢 i (haveI := hG i; inferInstance)
  set φ := Fintype.linearCombination (MvPolynomial ι R) g with hφdef
  have hφ : IsGradedMap (grFree ι R d) 𝒢 φ := isGradedMap_linearCombination 𝒢 hg
  have hsat' : ∀ (i : ι) (z : G), ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ := by
    intro i z
    rw [hφdef, Fintype.range_linearCombination]
    exact hsat i z
  let _ : Decomposition (grSub (grFree ι R d) (LinearMap.ker φ)) :=
    grSubDecomposition _ hφ.isHomogeneous_ker
  obtain ⟨b, e, κ, hκ, hksat⟩ := exists_homogeneous_family_saturating ι R (LinearMap.ker φ)
    (grSub (grFree ι R d) (LinearMap.ker φ)) fun i =>
      GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R _ (grSub (grFree ι R d) (LinearMap.ker φ)) i
        (GlobalTheory.finite_quotSMulTop_ker_of_graded ι R _ (grFree ι R d) G 𝒢 φ i hφ inferInstance (hsat' i) (hG i))
  let Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R) := Matrix.of fun l j => (κ j).1 l
  have hrange : LinearMap.range Φ.mulVecLin =
      (Submodule.span (MvPolynomial ι R) (Set.range κ)).map (LinearMap.ker φ).subtype := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : LinearMap.range Φ.mulVecLin ≤ LinearMap.ker φ := by
    rw [hrange]
    exact Submodule.map_subtype_le _ _
  refine ⟨a, b, d, e, Φ, Submodule.liftQ _ φ hle, fun l j => ?_, hφ.liftQ _ hle,
    fun i => ⟨fun y hy => ?_, fun z => ?_⟩⟩
  · have := mem_grPi.1 (mem_grSub.1 (hκ j)) l
    rw [sub_eq_add_neg]
    exact this
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨k, hk⟩ := hksat i ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hrange]
    exact ⟨_, hk, rfl⟩
  · rw [Submodule.range_liftQ]
    exact hsat' i z

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits DirectSum TensorProduct

noncomputable section

namespace GlobalTheory

theorem dehomogenising_comp_of_saturating {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type}
    [CommRing R] {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    [Decomposition 𝒩] {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    (𝒢 : ℤ → Submodule R G) {ψ : N →ₗ[MvPolynomial ι R] G} (hψ : IsGradedMap 𝒩 𝒢 ψ) (i : ι)
    (h₁ : ∀ y, ψ y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    (h₂ : ∀ z : G, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ)
    {B : Type} [CommRing B] (π : MvPolynomial ι R →+* B) {P : Type} [AddCommGroup P] [Module B P]
    (ε : G →ₛₗ[π] P) (hπ : π (MvPolynomial.X i) = 1) (hε : Function.Surjective ε)
    (hk : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    Function.Surjective (ε.comp ψ) ∧
      ∀ y, ε.comp ψ y = 0 ↔ ∃ w : N, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w := by
  refine ⟨fun p => ?_, dehomogenising_eq_zero_iff ι R N 𝒩 i B π P (ε.comp ψ) hπ ?_⟩
  · obtain ⟨z, rfl⟩ := hε p
    obtain ⟨k, y, hy⟩ := h₂ z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, hy, LinearMap.map_smulₛₗ, map_pow, hπ, one_pow, one_smul]
  · intro n y hy h
    obtain ⟨k, hk⟩ := hk n _ (hψ hy) h
    obtain ⟨j, hj⟩ := h₁ _ ((map_smul ψ _ y).trans hk)
    exact ⟨j + k, by rw [pow_add, mul_smul, hj]⟩

theorem exists_noetherian_model_grCube (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢]
    (H : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
      (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
      Algebra.Smooth R B ∧ Module.FinitePresentation B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
        ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 →
          ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    ∃ (R₀ : Subring R) (_ : IsNoetherianRing R₀) (C₀ : Cube.{0} ι R₀)
      (θ : Cube.baseChange R C₀ ⟶ grCube ι 𝒢 0),
      (∀ I : Finset ι, I.Nonempty → Module.Flat R₀ (C₀.obj I)) ∧
        (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) ∧
        ∀ I : Finset ι, I.Nonempty → Function.Bijective (θ.app I).hom := by
  obtain ⟨a, b, d, e, Φ, ψ, hΦ, hψ, hsat⟩ :=
    exists_graded_presentation_saturating ι R G 𝒢 fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, hfp, -, h⟩ := H i
      exact (finite_quotSMulTop_X_sub_one_of_chart ι R G 𝒢 i B iB iA π P iP iM ε h).2
        inferInstance hfp
  let := grQuotDecomposition (grFree ι R d) (isHomogeneous_range_mulVecLin ι R a b d e Φ hΦ)
  obtain ⟨R₀, Φ₀, hN, hmap, hΦ₀, hflat⟩ :=
    exists_noetherian_subring_homogeneous_matrix_flat_charts ι R a b d e Φ hΦ fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, -, hp, hπs, hπ, hε, hk⟩ := H i
      obtain ⟨k₁, k₂⟩ := dehomogenising_comp_of_saturating
        (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 hψ i (hsat i).1 (hsat i).2
        (π : MvPolynomial ι R →+* B) ε hπ hε hk
      refine ⟨B, iB, iA, π, P, iP, iM, (ε.comp ψ).comp (LinearMap.range Φ.mulVecLin).mkQ, hs, hp,
        hπs, hπ, k₁.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
      rw [LinearMap.comp_apply, k₂]
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨w', rfl⟩ := Submodule.mkQ_surjective _ w
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hw
        obtain ⟨v, hv⟩ := hw
        exact ⟨v, w', by rw [← Matrix.mulVecLin_apply, hv, sub_add_cancel]⟩
      · rintro ⟨v, w', rfl⟩
        refine ⟨Submodule.mkQ _ w', ?_⟩
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        exact ⟨v, by rw [Matrix.mulVecLin_apply, add_sub_cancel_right]⟩
  let := grQuotDecomposition (grFree ι R₀ d)
    (isHomogeneous_range_mulVecLin ι R₀ a b d e Φ₀ hΦ₀)
  obtain ⟨ψ₀, hbc, hψ₀⟩ := isBaseChange_coker_matrix_mvPolynomial ι R₀ R a b Φ₀ Φ hmap
  obtain ⟨iso⟩ := nonempty_baseChange_grCube_iso ι R₀ R _
    (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) _
    (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) ψ₀ 0 hbc
    (fun i y => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, hψ₀, hψ₀, ← Submodule.Quotient.mk_smul]
      congr 1
      ext1 l
      simp)
    (by
      rintro j _ ⟨y, hy, rfl⟩
      refine mem_grQuot.2 ⟨_, mem_grPi.2 fun l => ?_, (hψ₀ y).symm⟩
      have := mem_polyGrading_iff.1 (mem_grPi.1 hy l)
      refine mem_polyGrading_iff.2 fun c hc => this c fun h0 => hc ?_
      rw [MvPolynomial.coeff_map, h0, map_zero])
  refine ⟨R₀, hN, grCube ι (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) 0,
    iso.hom ≫ grCubeMap hψ 0, ?_, ?_, ?_⟩
  · rintro I ⟨i, hi⟩
    obtain ⟨f⟩ := nonempty_homLoc_singleton_equiv_quotSMulTop ι R₀ _
      (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) i
    have := hflat i
    exact flat_homLoc_of_flat_homLoc_singleton ι R₀ _ _ i I 0 hi (Module.Flat.of_linearEquiv f)
  · exact finite_grCech_homology ι R₀ _ _ inferInstance 0
  · rintro I ⟨i, hi⟩
    rw [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp]
    exact (homLocMap_bijective_of_X hψ hi (hsat i).1 (hsat i).2 0).comp
      (ConcreteCategory.bijective_of_isIso (iso.hom.app I))

end GlobalTheory
end
end
