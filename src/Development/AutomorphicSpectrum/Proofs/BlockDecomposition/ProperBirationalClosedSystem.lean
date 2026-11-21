import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullback
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Chart

attribute [local instance] algebraOfOver

variable {X Z : Scheme.{0}}

theorem idealPowι_comp_pullback_map_cokernel_eq_zero {A : Type} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (E : X.Modules) (D : Subobject E) (m : ℕ)
    (hD : powSub I E m ≤ D) :
    idealPowι I ((Scheme.Modules.pullback φ).obj E) m ≫
      (Scheme.Modules.pullback φ).map (cokernel.π D.arrow) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage
    (idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ m)))).1
  rw [comp_zero, ← Category.assoc, Abelian.image.fac]
  apply biproduct.hom_ext'
  intro k
  rw [comp_zero, idealSumMap, biproduct.ι_desc_assoc, smulHom_comp, ← appTop_algebraMap φ hφ,
    ← pullback_map_smulHom_appTop, ← Functor.map_comp, ← smulHom_comp]
  obtain ⟨L, hL⟩ := exists_smulHom_eq_comp_idealSumMap E (I ^ m) (idealGen_mem (I ^ m) k)
  have hι : idealPowι I E m ≫ cokernel.π D.arrow = 0 := by
    have h := Subobject.ofMkLE_arrow (f := idealPowι I E m) (X := D) hD
    rw [← h, Category.assoc, cokernel.condition, comp_zero]
  rw [hL, ← Abelian.image.fac (idealSumMap E (I ^ m)), Category.assoc, Category.assoc, hι,
    comp_zero, comp_zero, Functor.map_zero]

theorem chartIn_of_pullback_app_eq_zero (φ : Z ⟶ X) {E : X.Modules} [E.IsQuasicoherent]
    (D : Subobject E) [(D : X.Modules).IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V)
    (x : Γ(E, V))
    (hx : ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
      ((Scheme.Modules.pullback φ).map (cokernel.π D.arrow)).app U
        (GlobalTheory.QCoh.pullbackSections φ E h x) = 0) :
    ChartIn φ V (secsSub D V) x := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have hx' := hx U hU h
  rw [GlobalTheory.QCoh.pullback_map_app_pullbackSections] at hx'
  letI := GlobalTheory.QCoh.appLEModule φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  haveI := GlobalTheory.QCoh.appLE_isScalarTower φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  have hbc := GlobalTheory.QCoh.isBaseChange_pullbackSections φ (cokernel D.arrow) hU hV h
  let πl : Γ(E, V) →ₗ[Γ(X, V)] Γ(cokernel D.arrow, V) :=
    { toFun := (cokernel.π D.arrow).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hsurj : Function.Surjective πl := surjective_cokernel_π_app D.arrow hV
  have hex : Function.Exact (secsSub D V).subtype πl := by
    intro m
    have hm : m ∈ Set.range (secsSub D V).subtype ↔ m ∈ Set.range (D.arrow.app V) := by
      rw [Submodule.coe_subtype, Subtype.range_coe_subtype]
      rfl
    rw [hm, mem_range_app_iff D.arrow hV m]
    rfl
  have hex' := rTensor_exact Γ(Z, U) hex hsurj
  refine (hex' _).1 ?_
  rw [LinearMap.rTensor_tmul]
  have h1 : (1 : Γ(Z, U)) ⊗ₜ[Γ(X, V)] πl x = 0 := by
    apply hbc.equiv.injective
    rw [hbc.equiv_tmul, one_smul, map_zero]
    exact hx'
  rw [← TensorProduct.comm_tmul, h1, map_zero]

theorem chartIn_adjKer : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X),
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S →
    ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)),
    (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V →
    ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  intro A _ _ I X Z _ _ _ φ hφ E hE S hS B hB V hV x hx n
  have : E.IsQuasicoherent := hE.1
  have : ((S n : Subobject E) : X.Modules).IsQuasicoherent := hS.qcoh n
  apply chartIn_of_pullback_app_eq_zero φ (S n) V hV x
  intro U hU h
  obtain ⟨y, rfl⟩ := hx
  set g := (Scheme.Modules.pullback φ).map (cokernel.π (S n).arrow) with hg
  have hK : pullSys I φ E S n ≤ kernelSubobject g := by
    refine sup_le (image_le_kernel _ _ ?_) (le_kernelSubobject _ _ ?_)
    · rw [hg, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
    · rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_pullback_map_cokernel_eq_zero I φ hφ E (S n) (n + 1) (hS.pow_le n),
        comp_zero]
  have hBle : B ≤ kernelSubobject g := by
    rw [← hB n] at hK
    exact le_sup_left.trans hK
  have hBg : B.arrow ≫ g = 0 := by
    rw [← Subobject.ofLE_arrow hBle, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  have h0 : (adjMap φ B).app V ((adjKer φ B).arrow.app V y) = 0 := by
    have hk : (adjKer φ B).arrow ≫ adjMap φ B = 0 := kernelSubobject_arrow_comp _
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hk]
    rfl
  have h1 : (cokernel.π B.arrow).app (φ ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app E).app V
        ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [adjMap, Adjunction.homEquiv_unit] at h0
    exact h0
  have hfac : g = cokernel.π B.arrow ≫ cokernel.desc B.arrow g hBg := (cokernel.π_desc _ _ _).symm
  have h2 : (cokernel.π B.arrow).app U
      (GlobalTheory.QCoh.pullbackSections φ E h ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [GlobalTheory.QCoh.pullbackSections_apply]
    erw [GlobalTheory.QCoh.hom_app_res (cokernel.π B.arrow) h]
    rw [h1, map_zero]
  rw [hfac, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h2, map_zero]

end GlobalTheory.CompanionTheory.GE.Chart
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_system_affine_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V → ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer
end

section
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.KrullBaseChange

theorem krull_after_base_change {B R C M : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M)
    (hy : ∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈
      LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C))
    (Q₁ : Ideal (R ⊗[B] C)) (hQ : Q₁.IsPrime)
    (hI : I.map (algebraMap B R) ≤
      Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C)) :
    ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by
  classical
  set K : Ideal (R ⊗[B] C) := I.map (algebraMap B (R ⊗[B] C)) with hK
  have hKQ : K ≤ Q₁ := by
    rw [hK, Ideal.map_le_iff_le_comap]
    intro b hb
    have h1 := hI (Ideal.mem_map_of_mem (algebraMap B R) hb)
    simpa [Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply] using h1
  have key : ∀ (b : B) (c : C), (1 : R) ⊗ₜ[B] (b • c) = (algebraMap B R b) • ((1 : R) ⊗ₜ[B] c) := by
    intro b c
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one]
  let φ : M ⊗[B] C →+ (R ⊗[B] C) ⊗[R] M :=
    (TensorProduct.liftAddHom
      { toFun := fun m =>
          { toFun := fun c => ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m
            map_zero' := by simp
            map_add' := by intro a b; simp [TensorProduct.tmul_add, TensorProduct.add_tmul] }
        map_zero' := by ext c; simp
        map_add' := by intro a b; ext c; simp [TensorProduct.tmul_add] }
      (by
        intro b m c
        have h : (b • m : M) = (algebraMap B R b) • m := (algebraMap_smul R b m).symm
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, key]
        rw [TensorProduct.smul_tmul]))
  have hφ : ∀ (m : M) (c : C), φ (m ⊗ₜ[B] c) = ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m := fun m c => rfl
  have hmem : ∀ (n : ℕ) (z : M), z ∈ (I ^ n • ⊤ : Submodule B M) → ∀ c : C,
      ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] z ∈ (K ^ n • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    intro n z hz c
    induction hz using Submodule.smul_induction_on' with
    | smul b hb m hm =>
      have h : (b • m : M) = (algebraMap B R b) • m := (algebraMap_smul R b m).symm
      have h2 : ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] (b • m) =
          (algebraMap B (R ⊗[B] C) b) • (((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m) := by
        have h3 : (algebraMap B R b) • ((1 : R) ⊗ₜ[B] c) =
            (algebraMap B (R ⊗[B] C) b) • ((1 : R) ⊗ₜ[B] c) := by
          rw [Algebra.TensorProduct.algebraMap_apply, smul_eq_mul,
            Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul]
          simp
        rw [h, ← TensorProduct.smul_tmul, h3, TensorProduct.smul_tmul']
      rw [h2]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hK, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hb
    | add x _ y _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy
  have hall : ∀ n : ℕ, ∀ x : (I ^ (n + 1) • ⊤ : Submodule B M) ⊗[B] C,
      φ ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C x) ∈
        (K ^ (n + 1) • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    intro n x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z c =>
      simpa [hφ] using hmem (n + 1) z z.2 c
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  have hone : φ (y ⊗ₜ[B] (1 : C)) = (1 : R ⊗[B] C) ⊗ₜ[R] y := rfl
  have hinf : ((1 : R ⊗[B] C) ⊗ₜ[R] y) ∈
      (⨅ i : ℕ, K ^ i • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨x, hx⟩ := hy i
    have h := hall i x
    rw [hx, hone] at h
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h
  haveI : Module.Finite (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M) := Module.Finite.base_change R (R ⊗[B] C) M
  haveI : IsNoetherian (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M) := isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨⟨r, hr⟩, e⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff K _).1 hinf
  refine ⟨1 - r, ?_, ?_⟩
  · intro hw
    exact hQ.ne_top ((Ideal.eq_top_iff_one _).2 (by
      have := Q₁.add_mem hw (hKQ hr)
      simpa using this))
  · rw [sub_smul, one_smul]
    exact sub_eq_zero.2 e.symm

end GlobalTheory.CompanionTheory.KrullBaseChange
end

open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_prime_over_ideal_completion : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M), (∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈ LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C)) → ∀ Q₁ : Ideal (R ⊗[B] C), Q₁.IsPrime → I.map (algebraMap B R) ≤ Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) → ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change
end

section
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.KrullLocal

theorem exists_ringHom_of_fractions {B C D : Type} [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime] (φ : B →+* D)
    (hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ t))
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ q ∧ v * algebraMap B C b = 0) → φ b = 0) :
    ∃ g : C →+* D, (∀ b, g (algebraMap B C b) = φ b) ∧ ∀ v, v ∉ q → IsUnit (g v) := by
  classical
  choose bb tt ht vv hv hvt using h1
  have hmul : ∀ {x y : C}, x ∉ q → y ∉ q → x * y ∉ q := fun hx hy hm =>
    (hq.mem_or_mem hm).elim hx hy
  have hone : (1 : C) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
  have hone' : algebraMap B C 1 ∉ q := by simpa using hone
  let f : C → D := fun c => φ (bb c) * Ring.inverse (φ (tt c))
  have hft : ∀ c, f c * φ (tt c) = φ (bb c) := by
    intro c
    simp only [f]
    rw [mul_assoc, Ring.inverse_mul_cancel _ (hu _ (ht c)), mul_one]
  have key : ∀ (c : C) (b t : B) (v : C), algebraMap B C t ∉ q → v ∉ q →
      v * (algebraMap B C t * c) = v * algebraMap B C b → f c * φ t = φ b := by
    intro c b t v htq hvq h
    have hz : φ (tt c * b - t * bb c) = 0 := by
      apply h2
      refine ⟨vv c * v, hmul (hv c) hvq, ?_⟩
      have h' := hvt c
      simp only [map_sub, map_mul]
      linear_combination (-(vv c * algebraMap B C (tt c))) * h + (v * algebraMap B C t) * h'
    have hz' : φ (tt c) * φ b = φ (tt c) * (f c * φ t) := by
      have e : φ (tt c) * φ b - φ t * φ (bb c) = 0 := by simpa using hz
      rw [← hft c] at e
      linear_combination e
    exact ((hu _ (ht c)).mul_left_cancel hz').symm
  have hhom1 : f 1 = 1 := by
    have := key 1 1 1 1 hone' hone (by simp)
    simpa using this
  have hhom0 : f 0 = 0 := by
    have := key 0 0 1 1 hone' hone (by simp)
    simpa using this
  have hhommul : ∀ c c', f (c * c') = f c * f c' := by
    intro c c'
    have e := key (c * c') (bb c * bb c') (tt c * tt c') (vv c * vv c')
      (by rw [map_mul]; exact hmul (ht c) (ht c')) (hmul (hv c) (hv c'))
      (by
        have h := hvt c
        have h' := hvt c'
        simp only [map_mul]
        linear_combination (vv c' * algebraMap B C (tt c') * c') * h +
          (vv c * algebraMap B C (bb c)) * h')
    have hU : IsUnit (φ (tt c * tt c')) := by
      rw [map_mul]; exact (hu _ (ht c)).mul (hu _ (ht c'))
    apply hU.mul_right_cancel
    rw [e, map_mul, map_mul, ← hft c, ← hft c']
    ring
  have hhomadd : ∀ c c', f (c + c') = f c + f c' := by
    intro c c'
    have e := key (c + c') (tt c' * bb c + tt c * bb c') (tt c * tt c') (vv c * vv c')
      (by rw [map_mul]; exact hmul (ht c) (ht c')) (hmul (hv c) (hv c'))
      (by
        have h := hvt c
        have h' := hvt c'
        simp only [map_mul, map_add]
        linear_combination (vv c' * algebraMap B C (tt c')) * h +
          (vv c * algebraMap B C (tt c)) * h')
    have hU : IsUnit (φ (tt c * tt c')) := by
      rw [map_mul]; exact (hu _ (ht c)).mul (hu _ (ht c'))
    apply hU.mul_right_cancel
    rw [e, map_add, map_mul, map_mul, map_mul, ← hft c, ← hft c']
    ring
  refine ⟨{ toFun := f, map_one' := hhom1, map_mul' := hhommul, map_zero' := hhom0,
            map_add' := hhomadd }, ?_, ?_⟩
  · intro b
    have := key (algebraMap B C b) b 1 1 hone' hone (by simp [mul_comm])
    simpa using this
  · intro v hvq
    have hb : algebraMap B C (bb v) ∉ q := by
      intro hm
      have h := hvt v
      have : vv v * (algebraMap B C (tt v) * v) ∈ q := by
        rw [h]; exact q.mul_mem_left _ hm
      exact hmul (hv v) (hmul (ht v) hvq) this
    have hU := hu _ hb
    rw [← hft v] at hU
    exact isUnit_of_mul_isUnit_left hU

theorem exists_mul_eq_tmul {B R C : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime]
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (w : R ⊗[B] C) :
    ∃ (s : B) (v : C) (r : R), algebraMap B C s ∉ q ∧ v ∉ q ∧
      ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) * w = r ⊗ₜ[B] v := by
  have hmul : ∀ {x y : C}, x ∉ q → y ∉ q → x * y ∉ q := fun hx hy hm =>
    (hq.mem_or_mem hm).elim hx hy
  have hone : (1 : C) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, 1, 0, by simpa using hone, hone, by simp⟩
  | tmul r0 c =>
    obtain ⟨b, t, ht, v, hv, h⟩ := h1 c
    refine ⟨t, v, b • r0, ht, hv, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc, h, TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    obtain ⟨s, v, r, hs, hv, e⟩ := hx
    obtain ⟨s', v', r', hs', hv', e'⟩ := hy
    refine ⟨s * s', v * v', s' • r + s • r', by rw [map_mul]; exact hmul hs hs', hmul hv hv', ?_⟩
    have a1 : ((1 : R) ⊗ₜ[B] (v * v' * algebraMap B C (s * s'))) =
        ((1 : R) ⊗ₜ[B] (v' * algebraMap B C s')) * ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      congr 1
      ring
    have a2 : ((1 : R) ⊗ₜ[B] (v * v' * algebraMap B C (s * s'))) =
        ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) * ((1 : R) ⊗ₜ[B] (v' * algebraMap B C s')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      congr 1
      ring
    rw [mul_add]
    nth_rewrite 1 [a1]
    rw [a2, mul_assoc, mul_assoc, e, e', Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, TensorProduct.add_tmul,
      TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def]
    congr 2 <;> ring

theorem map_eq_zero_of_smul_tmul {B R C M D N : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [CommRing D] [Algebra R D]
    [AddCommGroup N] [Module R N] [Module D N] [IsScalarTower R D N]
    (J : Ideal B) (hJ : ∀ a ∈ J, algebraMap R D (algebraMap B R a) = 0)
    (Q₀ : Ideal (R ⊗[B] C)) (hQ : Q₀.IsPrime)
    (hunit : ∀ r : R, r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) →
      IsUnit (algebraMap R D r))
    (h1 : ∀ c : C, ∃ b t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * algebraMap B C b = 0) → ∃ t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      t * b ∈ J)
    (ι : M →ₗ[R] N) (y : M) (w : R ⊗[B] C) (hw0 : w ∉ Q₀)
    (hw : w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0) : ι y = 0 := by
  set q : Ideal C := Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) with hqdef
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hLR : ∀ t : B, (algebraMap B R t) ⊗ₜ[B] (1 : C) = (1 : R) ⊗ₜ[B] algebraMap B C t := by
    intro t
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hmemq : ∀ c : C, c ∈ q ↔ (1 : R) ⊗ₜ[B] c ∈ Q₀ := fun c => Iff.rfl
  have hmemp : ∀ r : R, r ∈ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ↔
      r ⊗ₜ[B] (1 : C) ∈ Q₀ := fun r => Iff.rfl
  let φ₀ : B →+* D := (algebraMap R D).comp (algebraMap B R)
  have hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ₀ t) := by
    intro t ht
    apply hunit
    rw [hmemp, hLR]
    exact fun h => ht ((hmemq _).2 h)
  have h1' : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b := h1
  obtain ⟨g, hg, hgu⟩ := exists_ringHom_of_fractions q φ₀ hu h1' (by
    intro b hb
    obtain ⟨t, ht, htb⟩ := h2 b hb
    have e : φ₀ (t * b) = 0 := hJ _ htb
    rw [map_mul] at e
    exact (hu t ht).mul_right_eq_zero.1 e)
  letI : Algebra B D := φ₀.toAlgebra
  haveI : IsScalarTower B R D := .of_algebraMap_eq (fun _ => rfl)
  let gA : C →ₐ[B] D := { g with commutes' := hg }
  let fA : R →ₐ[B] D := IsScalarTower.toAlgHom B R D
  let φ : R ⊗[B] C →ₐ[B] D := Algebra.TensorProduct.productMap fA gA
  have hφ : ∀ (r : R) (c : C), φ (r ⊗ₜ[B] c) = algebraMap R D r * g c := by
    intro r c
    simp [φ, fA, gA]
  have hφr : ∀ (r : R) (τ : R ⊗[B] C), φ (r • τ) = algebraMap R D r * φ τ := by
    intro r τ
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hφ]
    simp
  let Ψ : (R ⊗[B] C) ⊗[R] M →ₗ[R] N := TensorProduct.lift (LinearMap.mk₂ R
    (fun (τ : R ⊗[B] C) (m : M) => φ τ • ι m)
    (fun a b m => by simp [add_smul])
    (fun r a m => by rw [hφr, mul_smul, algebraMap_smul])
    (fun a m n => by simp)
    (fun r a m => by rw [map_smul, smul_comm]))
  have hΨ : φ w • ι y = 0 := by
    have e := congrArg Ψ hw
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_zero] at e
    simpa [Ψ] using e
  obtain ⟨s, v, r, hs, hv, e⟩ := exists_mul_eq_tmul (R := R) q h1' w
  have hr : r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) := by
    intro hm
    rw [hmemp] at hm
    have h3 : (r ⊗ₜ[B] v) ∈ Q₀ := by
      have := Q₀.mul_mem_right ((1 : R) ⊗ₜ[B] v) hm
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
    rw [← e] at h3
    rcases hQ.mem_or_mem h3 with h4 | h4
    · have : v * algebraMap B C s ∈ q := (hmemq _).2 h4
      exact (hq.mem_or_mem this).elim hv hs
    · exact hw0 h4
  have hunitw : IsUnit (φ w) := by
    have e2 := congrArg φ e
    rw [map_mul, hφ, hφ] at e2
    have hU : IsUnit (algebraMap R D r * g v) := (hunit r hr).mul (hgu v hv)
    rw [← e2] at hU
    exact isUnit_of_mul_isUnit_right hU
  obtain ⟨u, hu'⟩ := hunitw
  have : ι y = (↑u⁻¹ : D) • (φ w • ι y) := by
    rw [← hu', smul_smul, Units.inv_mul, one_smul]
  rw [this, hΨ, smul_zero]

theorem smul_eq_zero_of_smul_one_tmul_eq_zero : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] (J : Ideal B), (∀ a ∈ J, ∀ m : M, a • m = 0) → ∀ Q₀ : Ideal (R ⊗[B] C), Q₀.IsPrime → (∀ c : C, ∃ b t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * (algebraMap B C t * c) = v * algebraMap B C b) → (∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * algebraMap B C b = 0) → ∃ t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ t * b ∈ J) → ∀ (y : M) (w : R ⊗[B] C), w ∉ Q₀ → w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 → ∃ u : R, u ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ∧ u • y = 0 := by
  intro B R C M _ _ _ _ _ _ _ _ _ J hJ Q₀ hQ h1 h2 y w hw0 hw
  let p : Ideal R := Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C)
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  let A := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  letI : Module (A ⧸ Module.annihilator A N) N := Module.quotientAnnihilator
  haveI : IsScalarTower R (A ⧸ Module.annihilator A N) N := by
    refine ⟨fun r d n => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    have e : ∀ (x : A) (n : N), (Ideal.Quotient.mk (Module.annihilator A N) x) • n = x • n :=
      fun _ _ => rfl
    have e2 : r • Ideal.Quotient.mk (Module.annihilator A N) a =
        Ideal.Quotient.mk (Module.annihilator A N) (r • a) := rfl
    rw [e2, e, e, smul_assoc]
  have hJ' : ∀ a ∈ J, algebraMap R (A ⧸ Module.annihilator A N) (algebraMap B R a) = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ Module.annihilator A N),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
    intro n
    induction n using LocalizedModule.induction_on with
    | _ m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, algebraMap_smul, hJ a ha, LocalizedModule.zero_mk]
  have hunit : ∀ r : R, r ∉ p → IsUnit (algebraMap R (A ⧸ Module.annihilator A N) r) := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ Module.annihilator A N)]
    exact (IsLocalization.map_units A (⟨r, hr⟩ : p.primeCompl)).map _
  have hy := map_eq_zero_of_smul_tmul (D := A ⧸ Module.annihilator A N) J hJ' Q₀ hQ hunit h1 h2
    (LocalizedModule.mkLinearMap p.primeCompl M) y w hw0 hw
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).1 hy
  exact ⟨s, s.2, hs⟩

end GlobalTheory.CompanionTheory.KrullLocal
end

open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_prime_localization_criterion : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] (J : Ideal B), (∀ a ∈ J, ∀ m : M, a • m = 0) → ∀ Q₀ : Ideal (R ⊗[B] C), Q₀.IsPrime → (∀ c : C, ∃ b t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * (algebraMap B C t * c) = v * algebraMap B C b) → (∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * algebraMap B C b = 0) → ∃ t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ t * b ∈ J) → ∀ (y : M) (w : R ⊗[B] C), w ∉ Q₀ → w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 → ∃ u : R, u ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ∧ u • y = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.KrullLocal.smul_eq_zero_of_smul_one_tmul_eq_zero
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Krull

theorem stalkMap_germ_appLE {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) (W : Y.Opens) (U : Z.Opens)
    (h : U ≤ ψ ⁻¹ᵁ W) (z : Z) (hz : z ∈ U) (hy : ψ z ∈ W) (a : Γ(Y, W)) :
    ψ.stalkMap z (Y.presheaf.germ W (ψ z) hy a) = Z.presheaf.germ U z hz (ψ.appLE W U h a) := by
  simp [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]

theorem isUnit_germ_fromSpec {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (c : Γ(Z, U)) :
    IsUnit (Z.presheaf.germ U _ hz c) ↔ c ∉ q.asIdeal := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (hU.fromSpec q)) := (Z.presheaf.germ U _ hz).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal := hU.isLocalization_stalk' q hz
  rw [← Ideal.mem_primeCompl_iff]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal c

theorem exists_mul_eq_of_germ_eq {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (c d : Γ(Z, U))
    (e : Z.presheaf.germ U _ hz c = Z.presheaf.germ U _ hz d) :
    ∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * c = v * d := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (hU.fromSpec q)) := (Z.presheaf.germ U _ hz).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal := hU.isLocalization_stalk' q hz
  obtain ⟨⟨v, hv⟩, hvcd⟩ :=
    (IsLocalization.eq_iff_exists q.asIdeal.primeCompl (Z.presheaf.stalk (hU.fromSpec q))).mp e
  exact ⟨v, hv, hvcd⟩

theorem exists_frac_stalk {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (y : Y) (hy : y ∈ W)
    (s : Y.presheaf.stalk y) :
    ∃ a u : Γ(Y, W), IsUnit (Y.presheaf.germ W y hy u) ∧
      s * Y.presheaf.germ W y hy u = Y.presheaf.germ W y hy a := by
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨a, u⟩, hs⟩ := IsLocalization.surj (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl s
  exact ⟨a, u.1, IsLocalization.map_units (Y.presheaf.stalk y) u, hs⟩

theorem exists_mul_eq_zero_of_germ {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (y : Y)
    (hy : y ∈ W) (a : Γ(Y, W)) (e : Y.presheaf.germ W y hy a = 0) :
    ∃ u : Γ(Y, W), IsUnit (Y.presheaf.germ W y hy u) ∧ u * a = 0 := by
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨u, hu⟩, hua⟩ :=
    (IsLocalization.map_eq_zero_iff (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) a).mp e
  exact ⟨u, IsLocalization.map_units (Y.presheaf.stalk y) (⟨u, hu⟩ : (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), hua⟩

theorem isIso_stalkMap_of_isIso_restrict {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) (W : Y.Opens)
    (h : IsIso (ψ ∣_ W)) (z : Z) (hz : z ∈ ψ ⁻¹ᵁ W) : IsIso (ψ.stalkMap z) := by
  haveI : IsIso ((ψ ∣_ W).stalkMap ⟨z, hz⟩) := by
    first
    | infer_instance
    | (haveI : IsOpenImmersion (ψ ∣_ W) := inferInstance; infer_instance)
    | (haveI : IsOpenImmersion (ψ ∣_ W) := IsOpenImmersion.of_isIso _; infer_instance)
    | exact PresheafedSpace.IsOpenImmersion.stalk_iso (ψ ∣_ W).toPshHom ⟨z, hz⟩
  have e := morphismRestrictStalkMap ψ W ⟨z, hz⟩
  show IsIso (ψ.stalkMap (⟨z, hz⟩ : (ψ ⁻¹ᵁ W : Z.Opens)).1)
  rw [Arrow.iso_w' e]
  infer_instance

theorem chart_fractions_of_isIso_stalkMap {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) {U : Z.Opens} (hU : IsAffineOpen U) (h : U ≤ ψ ⁻¹ᵁ W)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (hiso : IsIso (ψ.stalkMap (hU.fromSpec q))) :
    (∀ c : Γ(Z, U), ∃ a u : Γ(Y, W), ψ.appLE W U h u ∉ q.asIdeal ∧
      ∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * (ψ.appLE W U h u * c) = v * ψ.appLE W U h a) ∧
    (∀ a : Γ(Y, W), (∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * ψ.appLE W U h a = 0) →
      ∃ u : Γ(Y, W), ψ.appLE W U h u ∉ q.asIdeal ∧ u * a = 0) := by
  have hy : ψ (hU.fromSpec q) ∈ W := h hz
  have hbij := (ConcreteCategory.isIso_iff_bijective (ψ.stalkMap (hU.fromSpec q))).mp hiso
  constructor
  · intro c
    obtain ⟨s, hs0⟩ := hbij.2 (Z.presheaf.germ U _ hz c)
    obtain ⟨a, u, hu, hs⟩ := exists_frac_stalk hW (ψ (hU.fromSpec q)) hy s
    have hs' := congrArg (ψ.stalkMap (hU.fromSpec q)) hs
    rw [map_mul, hs0, stalkMap_germ_appLE ψ W U h _ hz hy u, stalkMap_germ_appLE ψ W U h _ hz hy a] at hs'
    have hu' : IsUnit (Z.presheaf.germ U _ hz (ψ.appLE W U h u)) := by
      rw [← stalkMap_germ_appLE ψ W U h _ hz hy u]
      exact hu.map _
    rw [isUnit_germ_fromSpec hU q hz] at hu'
    refine ⟨a, u, hu', ?_⟩
    apply exists_mul_eq_of_germ_eq hU q hz
    rw [map_mul, mul_comm, hs']
  · rintro a ⟨v, hv, hva⟩
    have h0 : Z.presheaf.germ U _ hz (ψ.appLE W U h a) = 0 := by
      have hvu : IsUnit (Z.presheaf.germ U _ hz v) := (isUnit_germ_fromSpec hU q hz v).mpr hv
      have hh := congrArg (Z.presheaf.germ U _ hz) hva
      rw [map_mul, map_zero] at hh
      exact hvu.mul_right_eq_zero.mp hh
    have h1 : Y.presheaf.germ W _ hy a = 0 := by
      apply hbij.1
      rw [map_zero, stalkMap_germ_appLE ψ W U h _ hz hy a, h0]
    obtain ⟨u, hu, hua⟩ := exists_mul_eq_zero_of_germ hW _ hy a h1
    refine ⟨u, ?_, hua⟩
    rw [← isUnit_germ_fromSpec hU q hz, ← stalkMap_germ_appLE ψ W U h _ hz hy u]
    exact hu.map _

theorem chart_fractions_subscheme {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}}
    (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V))
    (hiso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f))) (U : Z.Opens) (hU : IsAffineOpen U)
    (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V) (q : Ideal Γ(Z, U)) (hq : q.IsPrime)
    (hf : (ψ ≫ J.subschemeι).appLE V U h f ∉ q) :
    (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t ∉ q ∧
      ∃ v : Γ(Z, U), v ∉ q ∧ v * ((ψ ≫ J.subschemeι).appLE V U h t * c) =
        v * (ψ ≫ J.subschemeι).appLE V U h b) ∧
    (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * (ψ ≫ J.subschemeι).appLE V U h b = 0) →
      ∃ t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t ∉ q ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  let p : PrimeSpectrum Γ(Z, U) := ⟨q, hq⟩
  have hz : hU.fromSpec p ∈ (U : Set Z) := by
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self _
  have hunit : IsUnit (Z.presheaf.germ U _ hz ((ψ ≫ J.subschemeι).appLE V U h f)) :=
    (isUnit_germ_fromSpec hU p hz _).mpr hf
  have hb : hU.fromSpec p ∈ Z.basicOpen ((ψ ≫ J.subschemeι).appLE V U h f) :=
    (Z.mem_basicOpen _ _ hz).mpr hunit
  have e1 : Z.basicOpen ((ψ ≫ J.subschemeι).appLE V U h f) =
      U ⊓ Z.basicOpen ((ψ ≫ J.subschemeι).app V f) := Z.basicOpen_res _ (homOfLE h).op
  have hb2 : hU.fromSpec p ∈ Z.basicOpen ((ψ ≫ J.subschemeι).app V f) :=
    (TopologicalSpace.Opens.mem_inf.mp (e1 ▸ hb)).2
  have e2 := Scheme.preimage_basicOpen (ψ ≫ J.subschemeι) f
  have hmem : hU.fromSpec p ∈ ψ ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ X.basicOpen f) := by
    have hh : hU.fromSpec p ∈ (ψ ≫ J.subschemeι) ⁻¹ᵁ X.basicOpen f := e2 ▸ hb2
    exact hh
  have hist : IsIso (ψ.stalkMap (hU.fromSpec p)) := isIso_stalkMap_of_isIso_restrict ψ _ hiso _ hmem
  have hW' : IsAffineOpen (J.subschemeι ⁻¹ᵁ V) := hV.preimage J.subschemeι
  obtain ⟨H1, H2⟩ := chart_fractions_of_isIso_stalkMap ψ hW' hU h p hz hist
  have hce : ∀ t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t =
      ψ.appLE (J.subschemeι ⁻¹ᵁ V) U h (J.subschemeι.app V t) := by
    intro t
    rw [Scheme.Hom.comp_appLE]
    rfl
  have hsurj := J.subschemeι_app_surjective ⟨V, hV⟩
  constructor
  · intro c
    obtain ⟨a, u, hu, v, hv, hvc⟩ := H1 c
    obtain ⟨b, rfl⟩ := hsurj a
    obtain ⟨t, rfl⟩ := hsurj u
    refine ⟨b, t, ?_, v, hv, ?_⟩
    · rw [hce]
      exact hu
    · rw [hce, hce]
      exact hvc
  · rintro b ⟨v, hv, hvb⟩
    rw [hce] at hvb
    obtain ⟨u, hu, hub⟩ := H2 (J.subschemeι.app V b) ⟨v, hv, hvb⟩
    obtain ⟨t, rfl⟩ := hsurj u
    refine ⟨t, ?_, ?_⟩
    · rw [hce]
      exact hu
    · rw [← J.ker_subschemeι_app ⟨V, hV⟩, RingHom.mem_ker, map_mul]
      exact hub

theorem stalk_over_isoLocus : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ q : Ideal Γ(Z, U), q.IsPrime → f ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) → (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ ∃ v : Γ(Z, U), v ∉ q ∧ v * (algebraMap Γ(X, V) Γ(Z, U) t * c) = v * algebraMap Γ(X, V) Γ(Z, U) b) ∧ (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * algebraMap Γ(X, V) Γ(Z, U) b = 0) → ∃ t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  intro X J Z ψ V hV f hiso U hU h q hq hf
  exact chart_fractions_subscheme J ψ V hV f hiso U hU h q hq hf

end GlobalTheory.CompanionTheory.GE.Krull
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_prime_criterion : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ q : Ideal Γ(Z, U), q.IsPrime → f ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) → (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ ∃ v : Γ(Z, U), v ∉ q ∧ v * (algebraMap Γ(X, V) Γ(Z, U) t * c) = v * algebraMap Γ(X, V) Γ(Z, U) b) ∧ (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * algebraMap Γ(X, V) Γ(Z, U) b = 0) → ∃ t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

namespace KrullPts

theorem exists_specialization_over {W S : Type*} [TopologicalSpace W] [TopologicalSpace S]
    {q : W → S} (hq : IsClosedMap q) {y₀ : W} {m : S} (h : q y₀ ⤳ m) :
    ∃ y₁, y₀ ⤳ y₁ ∧ q y₁ = m := by
  have hcl : IsClosed (q '' closure {y₀}) := hq _ isClosed_closure
  have hmem : q y₀ ∈ q '' closure {y₀} := ⟨y₀, subset_closure rfl, rfl⟩
  obtain ⟨y₁, hy₁, rfl⟩ := h.mem_closed hcl hmem
  exact ⟨y₁, specializes_iff_mem_closure.mpr hy₁, rfl⟩

theorem exists_chart_map {X Z W : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra Γ(X, V) R] (a : W ⟶ Z) (q : W ⟶ Spec (.of R))
    (hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec)
    (U : Z.Opens) (hU : IsAffineOpen U) (h : U ≤ φ ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    ∃ l : (a ⁻¹ᵁ U).toScheme ⟶ Spec (.of (R ⊗[Γ(X, V)] Γ(Z, U))),
      l ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))) =
        (a ⁻¹ᵁ U).ι ≫ q := by
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) ≫ hV.fromSpec =
      hU.fromSpec ≫ φ := IsAffineOpen.SpecMap_appLE_fromSpec φ hV hU h
  have key : ((a ⁻¹ᵁ U).ι ≫ q) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) =
      ((a ∣_ U) ≫ hU.isoSpec.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) := by
    rw [← cancel_mono hV.fromSpec]
    simp only [Category.assoc, e]
    rw [← hc, ← hU.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι_assoc]
  exact ⟨pullback.lift _ _ key ≫ (pullbackSpecIso _ _ _).hom, by
    rw [Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]⟩

theorem exists_chart_primes {X Z : Scheme.{0}} (φ : Z ⟶ X) [IsProper φ] (V : X.Opens)
    (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (p : Ideal R) (hp : p.IsPrime)
    (hz : ∃ z : Z, φ z = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R))
      (⟨p, hp⟩ : PrimeSpectrum R))) :
    ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ φ ⁻¹ᵁ V),
      letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
      ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧
        Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧
        (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom :
          R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  obtain ⟨z₀, hz₀⟩ := hz
  let g : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec
  let a := pullback.fst φ g
  let q := pullback.snd φ g
  have hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec :=
    pullback.condition
  obtain ⟨y₀, -, hq₀⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := g) z₀
    (⟨p, hp⟩ : PrimeSpectrum R) hz₀
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  have hspec : q y₀ ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := by
    change pullback.snd φ g y₀ ⤳ _
    rw [hq₀]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hpm
  obtain ⟨y₁, hsp, hq₁⟩ := exists_specialization_over q.isClosedMap hspec
  have hy₁ : a y₁ ∈ φ ⁻¹ᵁ V := by
    have e : φ (a y₁) = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (q y₁)) := by
      have := congr($hc y₁)
      simpa using this
    change φ (a y₁) ∈ V
    rw [e]
    exact hV.range_fromSpec.subset ⟨_, rfl⟩
  obtain ⟨U', hU', hmem, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hy₁
  have hU : IsAffineOpen U' := hU'
  refine ⟨U', hU, hle, ?_⟩
  letI : Algebra Γ(X, V) Γ(Z, U') := (φ.appLE V U' hle).hom.toAlgebra
  obtain ⟨l, hl⟩ := exists_chart_map φ V hV a q hc U' hU hle
  have hT₁ : y₁ ∈ a ⁻¹ᵁ U' := hmem
  have hT₀ : y₀ ∈ a ⁻¹ᵁ U' := hsp.mem_open (a ⁻¹ᵁ U').isOpen hT₁
  let t₀ : (a ⁻¹ᵁ U').toScheme := ⟨y₀, hT₀⟩
  let t₁ : (a ⁻¹ᵁ U').toScheme := ⟨y₁, hT₁⟩
  have ht : t₀ ⤳ t₁ := Topology.IsInducing.subtypeVal.specializes_iff.mp hsp
  have hcomp : ∀ t : (a ⁻¹ᵁ U').toScheme, Spec.map (CommRingCat.ofHom
      Algebra.TensorProduct.includeLeftRingHom) (l t) = q t.1 := fun t => congr($hl t)
  let P₀ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U')) := l t₀
  let P₁ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U')) := l t₁
  refine ⟨P₀.asIdeal, P₁.asIdeal, P₀.isPrime, P₁.isPrime, ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.le_iff_specializes P₀ P₁).mpr (ht.map l.continuous)
  · exact congrArg PrimeSpectrum.asIdeal ((hcomp t₀).trans hq₀)
  · have e : P₁.asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U')) = m :=
      congrArg PrimeSpectrum.asIdeal ((hcomp t₁).trans hq₁)
    rw [e]
    exact hm

end KrullPts

theorem exists_chart_primes_of_isProper : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ p : Ideal R, p.IsPrime → (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p → algebraMap Γ(X, V) R f ∉ p → ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V), letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧ (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  intro X J Z ψ hψ V hV R _ _ f hiso p hp hJ hf
  haveI := hψ
  refine KrullPts.exists_chart_primes (ψ ≫ J.subschemeι) V hV p hp ?_
  let P : PrimeSpectrum Γ(X, V) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (⟨p, hp⟩ : PrimeSpectrum R)
  change ∃ z : Z, (ψ ≫ J.subschemeι) z = hV.fromSpec P
  have hxf : hV.fromSpec P ∈ X.basicOpen f := by
    have h1 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hf
    exact h1
  have hxV : hV.fromSpec P ∈ (V : Set X) := hV.range_fromSpec.subset ⟨_, rfl⟩
  have hxs : hV.fromSpec P ∈ (J.support : Set X) := by
    have h1 : hV.fromSpec P ∈ (J.support : Set X) ∩ (V : Set X) := by
      have e := J.coe_support_inter ⟨V, hV⟩
      refine e.symm.subset ⟨?_, hxV⟩
      rw [Scheme.mem_zeroLocus_iff]
      intro b hb hbx
      have h2 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen b := hbx
      rw [hV.fromSpec_preimage_basicOpen] at h2
      exact h2 (hJ (Ideal.mem_map_of_mem _ hb))
    exact h1.1
  obtain ⟨y, hy⟩ := J.range_subschemeι.ge hxs
  have hyD : y ∈ J.subschemeι ⁻¹ᵁ X.basicOpen f := by
    change J.subschemeι y ∈ X.basicOpen f
    rw [hy]
    exact hxf
  haveI := hiso
  obtain ⟨w, hw⟩ := (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)).surjective ⟨y, hyD⟩
  have hψw : ψ w.1 = y :=
    (morphismRestrict_base_coe ψ _ w).symm.trans (congrArg Subtype.val hw)
  refine ⟨w.1, ?_⟩
  rw [Scheme.Hom.comp_apply, hψw, hy]

end GlobalTheory.CompanionTheory.GE
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_prime_exists : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ p : Ideal R, p.IsPrime → (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p → algebraMap Γ(X, V) R f ∉ p → ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V), letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧ (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.exists_chart_primes_of_isProper
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

theorem krull_noeth_chart : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens), IsAffineOpen V → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R], IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := by
  intro X J Z ψ hψ V hV U hU h
  have hft : ((ψ ≫ J.subschemeι).appLE V U h).hom.FiniteType := by
    haveI : LocallyOfFiniteType ψ := inferInstance
    haveI : LocallyOfFiniteType (ψ ≫ J.subschemeι) := inferInstance
    exact LocallyOfFiniteType.finiteType_appLE (ψ ≫ J.subschemeι) hV hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra
  intro R _ _ _
  haveI : Algebra.FiniteType Γ(X, V) Γ(Z, U) := by
    exact hft
  haveI : Algebra.FiniteType R (R ⊗[Γ(X, V)] Γ(Z, U)) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing R _

end GlobalTheory.CompanionTheory.GE
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_noetherian_affine_open : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens), IsAffineOpen V → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R], IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.krull_noeth_chart
end

section
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Krull

theorem fPow_torsion_of_chartIn : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (I : Ideal Γ(X, V)) {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R] {M : Type} [AddCommGroup M] [Module R M] [Module Γ(X, V) M] [IsScalarTower Γ(X, V) R M] [Module.Finite R M], I.map (algebraMap Γ(X, V) R) ≤ Ideal.jacobson ⊥ → (∀ a ∈ J.ideal ⟨V, hV⟩, ∀ m : M, a • m = 0) → ∀ f : Γ(X, V), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ y : M, (∀ n, ChartIn (ψ ≫ J.subschemeι) V (I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) y) → ∃ k : ℕ, f ^ k • y = 0 := by
  intro X J Z ψ hψ V hV _ I R _ _ _ M _ _ _ _ _ hIR hJM f hiso y hy
  by_contra hne
  push_neg at hne
  let A : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M y)
  have hA : ∀ a : R, a ∈ A ↔ a • y = 0 := fun a => by
    simp [A, LinearMap.toSpanSingleton_apply]
  have hdisj : Disjoint (A : Set R) (Submonoid.powers (algebraMap Γ(X, V) R f) : Set R) := by
    refine Set.disjoint_left.2 fun x hxA hxS => ?_
    obtain ⟨k, rfl⟩ := hxS
    apply hne k
    have h1 := (hA _).1 hxA
    simp only at h1
    rwa [← map_pow, algebraMap_smul] at h1
  obtain ⟨p, hp, hAp, hpS⟩ := Ideal.exists_le_prime_disjoint A _ hdisj
  have hfp : algebraMap Γ(X, V) R f ∉ p := fun h =>
    Set.disjoint_left.1 hpS h (Submonoid.mem_powers _)
  have hJp : (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => hAp ((hA _).2 ?_)
    rw [algebraMap_smul]
    exact hJM a ha y
  obtain ⟨U, hU, h, Q₀, Q₁, hQ₀, hQ₁, hle, hQ₀p, hQ₁m⟩ := GlobalTheory.T.proper_birational_prime_exists J ψ hψ V hV f hiso p hp hJp hfp
  letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra
  haveI : IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := GlobalTheory.T.tensor_noetherian_affine_open J ψ hψ V hV U hU h R
  have hy' : ∀ n : ℕ, y ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range
      ((I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M).subtype.rTensor Γ(Z, U)) := fun n => hy n U hU h
  have hIQ : I.map (algebraMap Γ(X, V) R) ≤
      Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) :=
    hIR.trans (sInf_le ⟨bot_le, hQ₁m⟩)
  obtain ⟨w, hw, hwy⟩ := GlobalTheory.T.tensor_prime_over_ideal_completion I y hy' Q₁ hQ₁ hIQ
  have hw0 : w ∉ Q₀ := fun h' => hw (hle h')
  have hfq : f ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : Γ(Z, U) →ₐ[Γ(X, V)] R ⊗[Γ(X, V)] Γ(Z, U))).comap
      (algebraMap Γ(X, V) Γ(Z, U)) := by
    intro hf
    apply hfp
    rw [← hQ₀p]
    simp only [Ideal.mem_comap] at hf ⊢
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply] at hf
    simpa [Algebra.TensorProduct.includeLeftRingHom_apply] using hf
  obtain ⟨hloc1, hloc2⟩ := GlobalTheory.T.proper_birational_prime_criterion J ψ V hV f hiso U hU h _ (Ideal.comap_isPrime _ _) hfq
  obtain ⟨u, hu, huy⟩ := GlobalTheory.T.tensor_prime_localization_criterion (J.ideal ⟨V, hV⟩) hJM Q₀ hQ₀ hloc1 hloc2 y w hw0 hwy
  rw [hQ₀p] at hu
  exact hu (hAp ((hA u).2 huy))

end GlobalTheory.CompanionTheory.GE.Krull
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobson_ideal_faithful_module : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (I : Ideal Γ(X, V)) {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R] {M : Type} [AddCommGroup M] [Module R M] [Module Γ(X, V) M] [IsScalarTower Γ(X, V) R M] [Module.Finite R M], I.map (algebraMap Γ(X, V) R) ≤ Ideal.jacobson ⊥ → (∀ a ∈ J.ideal ⟨V, hV⟩, ∀ m : M, a • m = 0) → ∀ f : Γ(X, V), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ y : M, (∀ n, ChartIn (ψ ≫ J.subschemeι) V (I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) y) → ∃ k : ℕ, f ^ k • y = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Krull.fPow_torsion_of_chartIn
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

variable {B : Type} [CommRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N]

theorem exists_eval_smul (r : AdicCompletion I B) (x : AdicCompletion I N) (n : ℕ) :
    ∃ b : B, eval I N n (r • x) = b • eval I N n x := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (r.val n)
  exact ⟨b, by show (r • x).val n = b • x.val n; rw [smul_eval, ← hb]; rfl⟩

theorem finite_adicCompletion [Module.Finite B N] :
    Module.Finite (AdicCompletion I B) (AdicCompletion I N) :=
  Module.Finite.of_surjective (ofTensorProduct I N) (ofTensorProduct_surjective_of_finite I N)

theorem span_range_of [Module.Finite B N] :
    Submodule.span (AdicCompletion I B) (Set.range (of I N)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I N x
  induction t with
  | zero => simp
  | tmul a e =>
    rw [ofTensorProduct_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

variable {I} (T : ℕ → Submodule B N) (hT : ∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n)

noncomputable def toQuot (n : ℕ) : AdicCompletion I N →ₗ[B] N ⧸ T n :=
  Submodule.factor (hT n) ∘ₗ eval I N (n + 1)

theorem toQuot_of (n : ℕ) (e : N) : toQuot T hT n (of I N e) = (T n).mkQ e := by
  simp [toQuot, eval_of, Submodule.factor_mk]

theorem toQuot_mk (n : ℕ) (f : AdicCauchySequence I N) :
    toQuot T hT n (AdicCompletion.mk I N f) = (T n).mkQ (f (n + 1)) := by
  show Submodule.factor (hT n) ((AdicCompletion.mk I N f).val (n + 1)) = _
  rw [mk_apply_coe, Submodule.factor_mk]

noncomputable def Tb (n : ℕ) : Submodule (AdicCompletion I B) (AdicCompletion I N) where
  carrier := {x | toQuot T hT n x = 0}
  add_mem' {x y} hx hy := by simp_all
  zero_mem' := by simp
  smul_mem' r x hx := by
    obtain ⟨b, hb⟩ := exists_eval_smul I r x (n + 1)
    have : toQuot T hT n (r • x) = b • toQuot T hT n x := by
      simp only [toQuot, LinearMap.comp_apply, hb, map_smul]
    simp_all

theorem mem_Tb (n : ℕ) (x : AdicCompletion I N) : x ∈ Tb T hT n ↔ toQuot T hT n x = 0 := Iff.rfl

theorem antitone_of_eq_sup_pow_smul_whole_module (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) : Antitone T :=
  antitone_nat_of_succ_le fun n ↦ (hT' n).symm ▸ le_sup_left

theorem exists_lift (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) (n : ℕ) (e : N)
    (he : e ∈ T n) : ∃ l ∈ ⨅ m, Tb T hT m, eval I N (n + 1) l = eval I N (n + 1) (of I N e) := by
  have step : ∀ j (x : T (n + j)), ∃ y : T (n + j + 1),
      (x : N) - y ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
    intro j x
    have hx : (x : N) ∈ T (n + j + 1) ⊔ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
      rw [← hT']; exact x.2
    obtain ⟨a, ha, c, hc, hxe⟩ := Submodule.mem_sup.1 hx
    exact ⟨⟨a, ha⟩, by rw [← hxe]; simpa using hc⟩
  choose f hf using step
  let u : (j : ℕ) → T (n + j) := fun j ↦ Nat.rec ⟨e, he⟩ (fun j x ↦ f j x) j
  have huj : ∀ j, (u (j + 1)).1 = (f j (u j)).1 := fun j ↦ rfl
  have hu : ∀ j, ((u j).1 - (u (j + 1)).1) ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := fun j ↦ by
    rw [huj]; exact hf j (u j)
  let s : ℕ → N := fun k ↦ (u (k - (n + 1))).1
  have huc : ∀ a b, a = b → (u a).1 = (u b).1 := by rintro a b rfl; rfl
  have hs0 : ∀ k, k ≤ n + 1 → s k = e := fun k hk ↦ huc _ 0 (Nat.sub_eq_zero_of_le hk)
  have hs1 : ∀ j, s (n + 1 + j) = (u j).1 := fun j ↦ huc _ _ (by omega)
  have hcau : ∀ k, s k ≡ s (k + 1) [SMOD (I ^ k • ⊤ : Submodule B N)] := by
    intro k
    rw [SModEq.sub_mem]
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [hs0 k hk.le, hs0 (k + 1) hk, sub_self]; exact zero_mem _
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [hs1, show n + 1 + j + 1 = n + 1 + (j + 1) by omega, hs1]
      simpa [show n + 1 + j = n + j + 1 by omega] using hu j
  let F : AdicCauchySequence I N := AdicCauchySequence.mk I N s hcau
  have hF : ∀ k, F k = s k := fun k ↦ rfl
  refine ⟨AdicCompletion.mk I N F, Submodule.mem_iInf _ |>.2 fun m ↦ ?_, ?_⟩
  · rw [mem_Tb, toQuot_mk, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rcases Nat.lt_or_ge m n with hm | hm
    · rw [hs0 _ (by omega)]; exact antitone_of_eq_sup_pow_smul_whole_module T hT' hm.le he
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [show n + j + 1 = n + 1 + j by omega, hs1]; exact (u j).2
  · show (AdicCompletion.mk I N F).val (n + 1) = _
    rw [mk_apply_coe, eval_of, hF, hs0 _ le_rfl]

end GlobalTheory.CompanionTheory.GE.CompletionTower

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

theorem exists_completion_tower : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N),
    (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) →
    (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) →
    ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type)
      (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M)
      (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧
      Submodule.span R (Set.range μ) = ⊤ ∧
      ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  intro B _ _ I N _ _ _ T hT hT'
  haveI := finite_adicCompletion I (N := N)
  haveI := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  let L : Submodule (AdicCompletion I B) (AdicCompletion I N) := ⨅ m, Tb T hT m
  let μ : N →ₗ[B] AdicCompletion I N ⧸ L := (L.mkQ.restrictScalars B) ∘ₗ of I N
  refine ⟨AdicCompletion I B, inferInstance, GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    inferInstance, AdicCompletion I N ⧸ L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, μ, IsAdicComplete.le_jacobson_bot _, ?_, ?_⟩
  · have : Set.range μ = L.mkQ '' Set.range (of I N) := by
      ext y; simp [μ]
    rw [this, ← Submodule.map_span, span_range_of, Submodule.map_top, Submodule.range_mkQ]
  · intro n e
    constructor
    · intro he
      obtain ⟨l, hl, hle⟩ := exists_lift T hT hT' n e he
      have hmem : of I N e - l ∈ (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N)) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker,
          map_sub, hle, sub_self]
      have hl0 : L.mkQ l = 0 := (Submodule.Quotient.mk_eq_zero L).2 hl
      have hμ : μ e = (L.mkQ.restrictScalars B) (of I N e - l) := by
        simp only [μ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_sub, hl0, sub_zero]
      have h2 := Submodule.mem_map_of_mem (f := L.mkQ.restrictScalars B) hmem
      rw [Submodule.map_smul''] at h2
      rw [hμ]
      exact Submodule.smul_mono le_rfl le_top h2
    · intro hμ
      have key : (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N ⧸ L)) ≤
          (LinearMap.ker (toQuot T hT n)).map (L.mkQ.restrictScalars B) := by
        rw [Submodule.smul_le]
        intro i hi m _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective L m
        refine ⟨i • x, ?_, by simp⟩
        show toQuot T hT n (i • x) = 0
        rw [map_smul]
        obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (T n) (toQuot T hT n x)
        rw [← hy, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hT n (Submodule.smul_mem_smul hi Submodule.mem_top)
      obtain ⟨x, hx, hxe⟩ := key hμ
      have hd : x - of I N e ∈ L := (Submodule.Quotient.eq L).1 hxe
      have hd' := (Submodule.mem_iInf _).1 hd n
      rw [mem_Tb, map_sub, LinearMap.mem_ker.1 hx, zero_sub, neg_eq_zero, toQuot_of,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hd'
      exact hd'

end GlobalTheory.CompanionTheory.GE.CompletionTower
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_module_noetherian_realization : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N), (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) → (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) → ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M) (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧ Submodule.span R (Set.range μ) = ⊤ ∧ ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.LocTors

theorem chartIn_map {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) {N M : Type} [AddCommGroup N]
    [Module Γ(X, V) N] [AddCommGroup M] [Module Γ(X, V) M] (g : N →ₗ[Γ(X, V)] M)
    {T : Submodule Γ(X, V) N} {T' : Submodule Γ(X, V) M} (hT : T.map g ≤ T') {x : N}
    (hx : ChartIn φ V T x) : ChartIn φ V T' (g x) := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  obtain ⟨y, hy⟩ := hx U hU h
  let g' : T →ₗ[Γ(X, V)] T' := (g.comp T.subtype).codRestrict T' (fun t => hT ⟨t, t.2, rfl⟩)
  refine ⟨g'.rTensor Γ(Z, U) y, ?_⟩
  have hc : T'.subtype.comp g' = g.comp T.subtype := rfl
  change (T'.subtype.rTensor Γ(Z, U)) (g'.rTensor Γ(Z, U) y) = g x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U))
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hc, LinearMap.rTensor_comp,
    LinearMap.comp_apply, hy, LinearMap.rTensor_tmul]

theorem eq_zero_of_mem_pow {B R M : Type} [CommRing B] [CommRing R] [IsNoetherianRing R]
    [Algebra B R] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] (I : Ideal B) (hjac : I.map (algebraMap B R) ≤ Ideal.jacobson ⊥) (m : M)
    (hm : ∀ n, m ∈ (I ^ (n + 1) • ⊤ : Submodule B M)) : m = 0 := by
  set IR : Ideal R := I.map (algebraMap B R)
  have key : ∀ n, m ∈ (IR ^ n • ⊤ : Submodule R M) := by
    intro n
    have h1 : (I ^ (n + 1) • ⊤ : Submodule B M) ≤ (IR ^ (n + 1) • ⊤ : Submodule R M).restrictScalars B := by
      rw [Submodule.smul_le]
      intro a ha u _
      rw [Submodule.restrictScalars_mem, algebraMap_smul R a u |>.symm]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      have h2 : algebraMap B R a ∈ (I ^ (n + 1)).map (algebraMap B R) := Ideal.mem_map_of_mem _ ha
      rwa [Ideal.map_pow] at h2
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) (h1 (hm n))
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) IR hjac
  have : m ∈ (⨅ n : ℕ, IR ^ n • (⊤ : Submodule R M)) := Submodule.mem_iInf _ |>.2 key
  rw [hK] at this
  exact (Submodule.mem_bot R).1 this

theorem adjKer_pow_smul_mem_secs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme) (hψ : IsProper ψ)
    (hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)))
    (W : J.subscheme.Opens) (hW : IsIso (ψ ∣_ W)) {E : X.Modules} (hE : IsCoherent E)
    {S : ℕ → Subobject E} (hS : ClosedSys I E S) (hK : ∀ e, Killed J (S e))
    (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E))
    (hB : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e)
    (V : X.affineOpens) (f : Γ(X, V)) (hf : J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W)
    (x : Γ(E, V)) (hx : x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V) :
    ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  haveI : Module.Finite Γ(X, V) Γ(E, V) := hE.2 V V.2
  haveI : E.IsQuasicoherent := hE.1
  set IB : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) (V : X.Opens)) I with hIB
  have hpow : ∀ n, Ideal.map (toFunctions (A := A) (V : X.Opens)) (I ^ n) = IB ^ n :=
    fun n => Ideal.map_pow _ _ _
  let T : ℕ → Submodule Γ(X, V) Γ(E, V) := fun n => secsSub (S n) V
  have hpowsecs : ∀ n, secs (powSub I E n) V =
      ((IB ^ n • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
    intro n
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 n V V.2, hpow]
  have h1 : ∀ n, IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) ≤ T n := by
    intro n y hy
    have hy' : y ∈ secs (powSub I E (n + 1)) V := by rw [hpowsecs]; exact hy
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (hS.pow_le n) V hy'
  have h2 : ∀ n, T n = T (n + 1) ⊔ IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) := by
    intro n
    have hq : (powSub I E (n + 1) : X.Modules).IsQuasicoherent := (closedSys_pow I E).qcoh n
    obtain ⟨_, hsum⟩ := GlobalTheory.T.quasicoherent_sup_sections hE.1 (S (n + 1)) (powSub I E (n + 1)) (hS.qcoh (n + 1)) hq
    ext y
    change y ∈ secs (S n) V ↔ _
    rw [hS.succ n, hsum V V.2, Submodule.mem_sup]
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      have ht' : t ∈ ((IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
        rw [← hpowsecs]; exact ht
      exact ht'
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      rw [hpowsecs]
      exact ht
  obtain ⟨R, firstRealIndex, secondRealIndex, iR3, M, familyMassRatio, familyMassSecondLine, iM3, iM4, iM5, μ, hjac, hspan, hiff⟩ :=
    GlobalTheory.T.complete_module_noetherian_realization IB T h1 h2
  have hJ : ∀ a ∈ J.ideal ⟨(V : X.Opens), V.2⟩, ∀ m : M, a • m = 0 := by
    intro a ha m
    have hm : m ∈ Submodule.span R (Set.range μ) := hspan ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun m _ => a • m = 0) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨e, rfl⟩
      apply eq_zero_of_mem_pow IB hjac
      intro n
      rw [← map_smul]
      exact (hiff n (a • e)).1 (hK n V a ha e)
    · exact smul_zero a
    · intro u v _ _ hu hv
      rw [smul_add, hu, hv, add_zero]
    · intro r u _ hu
      rw [smul_comm a r u, hu, smul_zero]
  have hIso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) :=
    GroundTheory.Arith.SchemeCoh.isIso_morphismRestrict_of_le ψ hf
  have hch := GlobalTheory.T.pushforward_system_affine_sections I (ψ ≫ J.subschemeι) hover hE hS B hB (V : X.Opens) V.2 x hx
  have hch' : ∀ n, ChartIn (ψ ≫ J.subschemeι) (V : X.Opens)
      (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) (μ x) := by
    intro n
    refine chartIn_map _ _ μ ?_ (hch n)
    rintro _ ⟨e, he, rfl⟩
    exact (hiff n e).1 he
  obtain ⟨k, hk⟩ := GlobalTheory.T.jacobson_ideal_faithful_module J ψ hψ (V : X.Opens) V.2 IB hjac hJ f hIso (μ x) hch'
  refine ⟨k, fun n => ?_⟩
  have hμ : μ (f ^ k • x) ∈ (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) := by
    rw [map_smul, hk]
    exact Submodule.zero_mem _
  exact (hiff n _).2 hμ

end GlobalTheory.CompanionTheory.GE.LocTors
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_closed_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData) {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → ∀ (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E)), (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e) → ∀ (V : X.affineOpens) (f : Γ(X, V)), J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W → ∀ x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs
end
