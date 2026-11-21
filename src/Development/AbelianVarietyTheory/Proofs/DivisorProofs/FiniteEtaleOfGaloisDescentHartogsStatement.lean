import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.HartFlatBaseChange

def divIdeal (A S X : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup X] [Module S X]
    (a : A) (y : X) : Ideal A where
  carrier := {u | ∃ x : X, algebraMap A S u • y = algebraMap A S a • x}
  add_mem' := by
    rintro u v ⟨x, hx⟩ ⟨x', hx'⟩
    exact ⟨x + x', by rw [map_add, add_smul, hx, hx', smul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c u ⟨x, hx⟩
    refine ⟨algebraMap A S c • x, ?_⟩
    rw [smul_eq_mul, map_mul, mul_smul, hx, smul_comm]

theorem lTensor_smul_id_apply (R M O : Type) [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    [Algebra R O] (r : R) (x : O ⊗[R] M) :
    (r • LinearMap.id : M →ₗ[R] M).lTensor O x = algebraMap R O r • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o n => simp [LinearMap.lTensor_tmul, algebraMap_smul, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

end GlobalTheory.HartFlatBaseChange

open GlobalTheory.HartFlatBaseChange in
theorem GlobalTheory.GoodEtale.hart_tensor_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  intro A R M O _ _ _ _ _ _ _ _ _ _ _ hM a ha m hm
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (divIdeal A O (O ⊗[R] M) a m) : Submodule.FG _)
  have hsI : ∀ b ∈ s, b ∈ divIdeal A O (O ⊗[R] M) a m := fun b hb => hs ▸ Ideal.subset_span hb
  let f : M →ₗ[R] M := algebraMap A R a • LinearMap.id
  let N : Submodule R M := LinearMap.range f
  let g : M →ₗ[R] (s → M ⧸ N) := LinearMap.pi fun i => N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id)
  have hex : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      have hyI : divIdeal A O (O ⊗[R] M) a m ≤ divIdeal A R M a y := by
        rw [← hs, Ideal.span_le]
        intro b hb
        have := congrFun hy ⟨b, hb⟩
        simp only [g, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range] at this
        obtain ⟨x, hx⟩ := this
        exact ⟨x, by simpa [f] using hx.symm⟩
      obtain ⟨m', hm'⟩ := hM a ha y fun p hp hp1 => by
        obtain ⟨u, hup, hu⟩ := hm p hp hp1
        exact ⟨u, hup, hyI hu⟩
      exact ⟨m', by simp [f, hm']⟩
    · rintro ⟨x, rfl⟩
      funext i
      simp only [g, f, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range]
      exact ⟨algebraMap A R i.1 • x, by simp [f, smul_comm (algebraMap A R a)]⟩
  have hexO := Module.Flat.lTensor_exact O hex
  have hcomp : ∀ (z : O ⊗[R] (s → M ⧸ N)) (i : s),
      TensorProduct.piRight R R O (fun _ : s => M ⧸ N) z i = (LinearMap.proj i).lTensor O z := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul o n => simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, map_add]
  have hg : g.lTensor O m = 0 := by
    apply (TensorProduct.piRight R R O (fun _ : s => M ⧸ N)).injective
    funext i
    rw [hcomp, map_zero, Pi.zero_apply, ← LinearMap.lTensor_comp_apply]
    have hpg : (LinearMap.proj i).comp g = N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id) := rfl
    obtain ⟨m', hm'⟩ := hsI i.1 i.2
    rw [hpg, LinearMap.lTensor_comp_apply, lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply,
      hm', IsScalarTower.algebraMap_apply A R O, ← lTensor_smul_id_apply, ← LinearMap.lTensor_comp_apply,
      LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨m', hm'⟩ := (hexO m).1 hg
  exact ⟨m', by rw [← hm', lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply]⟩
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hart_baseChange_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  first | (exact @GlobalTheory.GoodEtale.hart_tensor_of_flat) | (exact GlobalTheory.GoodEtale.hart_tensor_of_flat) | (intros; apply GlobalTheory.GoodEtale.hart_tensor_of_flat  <;> assumption)
end

section
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleFinite

theorem finite_of_trace_relation (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R) :
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  intro hT a ha n x y hrel htf
  set b : R := algebraMap A R a with hb

  have key : ∀ c : C, b • c = ∑ i, T (y i * c) • x i := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i
      rw [Algebra.smul_def, hT, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hrel]
    simp [Algebra.smul_def]
  let S : Submodule R C := Submodule.span R (Set.range x)
  have hmem : ∀ c : C, b • c ∈ S := by
    intro c
    rw [key c]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : C →ₗ[R] S := LinearMap.codRestrict S (b • LinearMap.id) (fun c => by simpa using hmem c)
  have hf : Function.Injective f := by
    intro c d hcd
    have : b • c = b • d := by simpa [f] using congrArg Subtype.val hcd
    have h0 : b • (c - d) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf a ha _ h0)
  haveI : Module.Finite R S := Module.Finite.span_of_finite R (Set.finite_range x)
  haveI : IsNoetherian R S := isNoetherian_of_isNoetherianRing_of_finite R S
  exact Module.Finite.of_injective f hf

end GlobalTheory.GoodEtaleFinite
end

section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_galois_trace_relation : ∀ (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  first | (exact @GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (exact GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (intros; apply GlobalTheory.GoodEtaleFinite.finite_of_trace_relation  <;> assumption)
end

section
open scoped TensorProduct

theorem GlobalTheory.GoodEtale.galMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  intro A R C O _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy htf σ
  set b := algebraMap R C (algebraMap A R a) with hb
  have key : ∀ c : C, ∑ i, T (y i * c) • x i = b * c := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i; rw [Algebra.smul_def, hT, mul_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul, mul_assoc]
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hxy]
    simp
  let L := LinearMap.lTensor O (LinearMap.mulLeft R b)
  have hL : Function.Injective L := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact htf a ha c (by rw [Algebra.smul_def]; simpa using hc)
  let Φ : (G → O) → O ⊗[R] C := fun f => ∑ i, (∑ g, σ (act g (y i)) * f g) ⊗ₜ x i
  have hΦ : ∀ m, Φ (GlobalTheory.GoodEtale.galMap act σ m) = L m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp [Φ]
    | tmul o c =>
      simp only [Φ, GlobalTheory.GoodEtale.galMap_tmul, L, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply]
      have h2 : ∀ i, (∑ g, σ (act g (y i)) * (o * σ (act g c))) = T (y i * c) • o := by
        intro i
        rw [Algebra.smul_def, ← σ.commutes, hT, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, map_mul]; ring
      simp_rw [h2, ← key, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
    | add m m' hm hm' =>
      rw [map_add, map_add, ← hm, ← hm']
      simp only [Φ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul]
  rw [injective_iff_map_eq_zero]
  intro m hm
  apply hL
  rw [← hΦ, hm, map_zero]
  simp [Φ]
end

section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisComparisonMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  first | (exact @GlobalTheory.GoodEtale.galMap_injective_of_flat) | (exact GlobalTheory.GoodEtale.galMap_injective_of_flat) | (intros; apply GlobalTheory.GoodEtale.galMap_injective_of_flat  <;> assumption)
end

section
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem galElt_dvd_of_unramified : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    [Algebra.FormallyUnramified O (O ⊗[R] C)] [Algebra.EssFiniteType O (O ⊗[R] C)]
    (G : Type) [Group G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (b : R) (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) →
    ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) →
    ∀ h : G, ∃ m' : O ⊗[R] C, GlobalTheory.GoodEtale.galElt act σ x y h = algebraMap R O b • m' := by
  intro R C O _ _ _ _ _ _ _ G _ _ act b n x y hxy σ hinj h
  obtain ⟨t, ht1, ht2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := O) (S := O ⊗[R] C)).mp inferInstance
  let τ : O ⊗[R] C →ₐ[O] O := (Pi.evalAlgHom O (fun _ : G => O) h).comp (galMap act σ)
  let ψ : (O ⊗[R] C) ⊗[O] (O ⊗[R] C) →ₐ[O] O ⊗[R] C :=
    Algebra.TensorProduct.lift (AlgHom.id O _) ((Algebra.ofId O (O ⊗[R] C)).comp τ) (fun _ _ => Commute.all _ _)
  have hψ : ∀ a c, ψ (a ⊗ₜ c) = a * algebraMap O (O ⊗[R] C) (τ c) := by
    intro a c; simp [ψ]
  set e := ψ t with he

  have hi : ∀ s, s * e = algebraMap O (O ⊗[R] C) (τ s) * e := by
    intro s
    have := congrArg ψ (ht1 s)
    rw [map_mul, map_sub, hψ, hψ, map_zero] at this
    simp only [map_one, one_mul, mul_one] at this
    rw [← he] at this
    rw [sub_mul, sub_eq_zero] at this
    exact this.symm

  have hii : τ e = 1 := by
    have hcomp : τ.comp ψ = τ.comp (Algebra.TensorProduct.lmul' O) := by
      apply Algebra.TensorProduct.ext'
      intro a c
      simp only [AlgHom.comp_apply, hψ, map_mul, AlgHom.commutes, Algebra.TensorProduct.lmul'_apply_tmul]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have := congrArg (fun f => f t) hcomp
    simp only [AlgHom.comp_apply] at this
    rw [he, this, ht2, map_one]

  have hfix : galElt act σ x y h * e = galElt act σ x y h := by
    apply hinj
    rw [map_mul, galMap_galElt act σ x y b hxy h]
    funext g
    by_cases hg : g = h
    · subst hg
      have : galMap act σ e g = τ e := rfl
      simp [this, hii]
    · simp [Pi.single_apply, hg]
  refine ⟨e, ?_⟩
  rw [← hfix]
  simp only [galElt, Finset.sum_mul]
  have hterm : ∀ i, σ (x i) ⊗ₜ[R] act h⁻¹ (y i) * e = algebraMap O (O ⊗[R] C) (σ (x i) * σ (y i)) * e := by
    intro i
    have hsplit : σ (x i) ⊗ₜ[R] act h⁻¹ (y i) = algebraMap O (O ⊗[R] C) (σ (x i)) * ((1 : O) ⊗ₜ[R] act h⁻¹ (y i)) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hsplit, mul_assoc, hi, ← mul_assoc, ← map_mul]
    congr 3
    have : τ ((1 : O) ⊗ₜ[R] act h⁻¹ (y i)) = σ (act h (act h⁻¹ (y i))) := by
      simp [τ, galMap_tmul]
    rw [this]
    congr 2
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
  simp_rw [hterm, ← Finset.sum_mul, ← map_sum, ← map_mul, ← map_sum]
  have h1 := hxy 1
  simp only [map_one, AlgEquiv.one_apply, if_true] at h1
  rw [h1, AlgHom.commutes, Algebra.smul_def]

end GlobalTheory.GoodEtale
end

section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisElement_dvd_of_formallyUnramified : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    [Algebra.FormallyUnramified O (O ⊗[R] C)] [Algebra.EssFiniteType O (O ⊗[R] C)]
    (G : Type) [Group G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (b : R) (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) →
    ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) →
    ∀ h : G, ∃ m' : O ⊗[R] C, GlobalTheory.GoodEtale.galElt act σ x y h = algebraMap R O b • m' := by
  first | (exact @GlobalTheory.GoodEtale.galElt_dvd_of_unramified) | (exact GlobalTheory.GoodEtale.galElt_dvd_of_unramified) | (intros; apply GlobalTheory.GoodEtale.galElt_dvd_of_unramified  <;> assumption)
end

section
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem etale_localization_of_etaleLow : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := by
  intro A R C O _ _ _ _ _ _ _ Q _ hE hh
  have h := hE (Q.comap (algebraMap R O)) hh
  letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) :=
    (Localization.localRingHom _ Q (algebraMap R O) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply R O (Localization.AtPrime Q)]
  haveI := Algebra.Etale.baseChange (R := Localization.AtPrime (Q.comap (algebraMap R O)))
    (B := Localization.AtPrime Q) (A := Localization.AtPrime (Q.comap (algebraMap R O)) ⊗[R] C)
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange R
    (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) (Localization.AtPrime Q) C)

example : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := etale_localization_of_etaleLow

end GlobalTheory.GoodEtale
end

section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localizationAtPrime_tensor_of_low_height : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := by
  first | (exact @GlobalTheory.GoodEtale.etale_localization_of_etaleLow) | (exact GlobalTheory.GoodEtale.etale_localization_of_etaleLow) | (intros; apply GlobalTheory.GoodEtale.etale_localization_of_etaleLow  <;> assumption)
end

section
open scoped TensorProduct
open TensorProduct

namespace GlobalTheory

theorem exists_smul_dvd_of_localization_atPrime_tensor :
    ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    (Q : Ideal O) [Q.IsPrime] (b : R) (m : O ⊗[R] C),
    (∃ m' : Localization.AtPrime Q ⊗[R] C,
      (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C m = algebraMap R (Localization.AtPrime Q) b • m') →
    ∃ s ∉ Q, ∃ m' : O ⊗[R] C, s • m = algebraMap R O b • m' := by
  intro R C O _ _ _ _ _ Q _ b m ⟨m', hm'⟩
  let f := AlgebraTensorModule.rTensor R C (Algebra.linearMap O (Localization.AtPrime Q))
  haveI : IsLocalizedModule Q.primeCompl f := inferInstance
  have hf : ∀ x, (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C x = f x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [f]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hf, algebraMap_smul] at hm'
  obtain ⟨⟨m'', t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective Q.primeCompl f m'
  simp only [Function.uncurry_apply_pair] at hm'
  have h2 : f ((t : O) • m) = f (b • m'') := by
    rw [LinearMap.map_smul, hm', smul_comm (t : O) b, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
      LinearMap.map_smul_of_tower]
  obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := Q.primeCompl) h2
  refine ⟨(u : O) * t, (Q.primeCompl.mul_mem u.2 t.2 : _), (u : O) • m'', ?_⟩
  rw [algebraMap_smul, mul_smul]
  simpa [Submonoid.smul_def, smul_comm (u : O) b] using hu

end GlobalTheory
end

section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_dvd_of_localization_atPrime_tensor' : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    (Q : Ideal O) [Q.IsPrime] (b : R) (m : O ⊗[R] C),
    (∃ m' : Localization.AtPrime Q ⊗[R] C,
      (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C m = algebraMap R (Localization.AtPrime Q) b • m') →
    ∃ s ∉ Q, ∃ m' : O ⊗[R] C, s • m = algebraMap R O b • m' := by
  first | (exact @GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor) | (exact GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor) | (intros; apply GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodEtale

theorem noTorsion_of_faithfullyFlat_point : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O],
    Nonempty (C →ₐ[R] O) → GlobalTheory.GoodEtale.TorsionFreeOver A R C →
    ∀ (a : A), a ≠ 0 → ∀ v : O, algebraMap R O (algebraMap A R a) * v = 0 → v = 0 := by
  intro A R C O _ _ _ _ _ _ _ _ hσ hTF a ha v hv
  obtain ⟨σ⟩ := hσ
  have hRO : Function.Injective (algebraMap R O) :=
    RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hreg : IsSMulRegular R (algebraMap A R a) := by
    intro r s hrs
    simp only [smul_eq_mul] at hrs
    have h0 : algebraMap A R a * (r - s) = 0 := by rw [mul_sub, hrs, sub_self]
    have h1 : algebraMap A R a • algebraMap R C (r - s) = 0 := by
      rw [Algebra.smul_def, ← map_mul, h0, map_zero]
    have h2 := hTF a ha _ h1
    have h3 : algebraMap R O (r - s) = 0 := by
      rw [← σ.commutes, h2, map_zero]
    exact sub_eq_zero.mp (hRO (by rw [h3, map_zero]))
  have hO : IsSMulRegular O (algebraMap R O (algebraMap A R a)) := IsSMulRegular.of_flat hreg
  apply hO
  simp only [smul_eq_mul, mul_zero]
  exact hv

theorem hart_of_local : ∀ (A O M : Type) [CommRing A] [CommRing O] [Algebra A O] [AddCommGroup M] [Module O M],
    GlobalTheory.GoodEtale.Hart A O M → ∀ (a : A), a ≠ 0 → ∀ m : M,
    (∀ Q : Ideal O, Q.IsPrime → (Q.comap (algebraMap A O)).height ≤ 1 →
      ∃ s ∉ Q, ∃ m' : M, s • m = algebraMap A O a • m') →
    ∃ m' : M, m = algebraMap A O a • m' := by
  intro A O M _ _ _ _ _ hH a ha m hloc
  apply hH a ha m
  intro p hp hpht
  by_contra hcon
  push_neg at hcon
  let J : Ideal O :=
    { carrier := {o | ∃ m' : M, o • m = algebraMap A O a • m'}
      add_mem' := by
        rintro x y ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
        exact ⟨m₁ + m₂, by rw [add_smul, h₁, h₂, smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨m₁, h₁⟩
        refine ⟨c • m₁, ?_⟩
        simp only [smul_eq_mul]
        rw [mul_smul, h₁, smul_comm] }
  have hdisj : Disjoint (J : Set O) ((p.primeCompl.map (algebraMap A O) : Submonoid O) : Set O) := by
    rw [Set.disjoint_left]
    rintro _ ⟨m', hm'⟩ ⟨u, hu, rfl⟩
    exact hcon u hu m' hm'
  obtain ⟨Q, hQ, hJQ, hQd⟩ := Ideal.exists_le_prime_disjoint J _ hdisj
  have hle : Q.comap (algebraMap A O) ≤ p := by
    intro u hu
    by_contra hup
    exact Set.disjoint_left.mp hQd hu ⟨u, hup, rfl⟩
  obtain ⟨s, hs, m', hm'⟩ := hloc Q hQ ((Ideal.height_mono hle).trans hpht)
  exact hs (hJQ ⟨m', hm'⟩)

theorem descent_finiteEtale : ∀ (A R C O : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → GlobalTheory.GoodEtale.Hart A R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    Nonempty (C →ₐ[R] O) →
    Module.Finite R C ∧ Algebra.Etale R C := by
  intro A R C O _ _ _ _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy hTF hH hE hσ
  obtain ⟨σ⟩ := hσ
  refine ⟨GlobalTheory.T.finite_of_galois_trace_relation A R C G act T hT a ha n x y hxy hTF, ?_⟩
  letI : Algebra A O := ((algebraMap R O).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hHO : Hart A O (O ⊗[R] C) := GlobalTheory.T.hart_baseChange_of_flat A R C O hH
  set b := algebraMap A R a with hb
  have hdiv : ∀ h : G, ∃ m' : O ⊗[R] C, galElt act σ x y h = algebraMap R O b • m' := by
    intro h
    refine hart_of_local A O (O ⊗[R] C) hHO a ha (galElt act σ x y h) ?_
    intro Q hQ hht
    haveI := hQ
    haveI : Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) :=
      GlobalTheory.T.etale_localizationAtPrime_tensor_of_low_height A R C O Q hE (by first | exact hht | (rw [Ideal.comap_comap]; exact hht))
    let σQ : C →ₐ[R] Localization.AtPrime Q := (IsScalarTower.toAlgHom R O _).comp σ
    have hinj := GlobalTheory.T.galoisComparisonMap_injective_of_flat A R C (Localization.AtPrime Q) G act T hT a ha n x y hxy hTF σQ
    obtain ⟨m'', hm''⟩ := GlobalTheory.T.galoisElement_dvd_of_formallyUnramified R C (Localization.AtPrime Q) G act b n x y hxy σQ hinj h
    have hcomp : (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C
        (galElt act σ x y h) = galElt act σQ x y h := by
      simp [galElt, map_sum, σQ]
    obtain ⟨s, hs, m', hm'⟩ := GlobalTheory.T.exists_smul_dvd_of_localization_atPrime_tensor' R C O Q b _ ⟨m'', hcomp.trans hm''⟩
    exact ⟨s, hs, m', hm'⟩
  have key : ∀ h, ∃ m, galMap act σ m = Pi.single h 1 := by
    intro h
    obtain ⟨m', hm'⟩ := hdiv h
    refine ⟨m', ?_⟩
    have h1 := galMap_galElt act σ x y b (by simpa [hb] using hxy) h
    rw [hm', map_smul] at h1
    funext g
    have h2 := congrFun h1 g
    refine sub_eq_zero.mp (noTorsion_of_faithfullyFlat_point A R C O ⟨σ⟩ hTF a ha _ ?_)
    rw [mul_sub]
    by_cases hg : g = h
    · subst hg; simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h2 ⊢; rw [h2]; simp [hb]
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hg] at h2 ⊢; rw [h2]; simp
  have hsurj : Function.Surjective (galMap act σ) := by
    intro v
    choose m hm using key
    refine ⟨∑ h, v h • m h, ?_⟩
    rw [map_sum]
    simp only [map_smul, hm]
    funext g
    simp [Finset.sum_apply, Pi.single_apply]
  let e := AlgEquiv.ofBijective (galMap act σ)
    ⟨GlobalTheory.T.galoisComparisonMap_injective_of_flat A R C O G act T hT a ha n x y hxy hTF σ, hsurj⟩
  haveI : Algebra.Etale O (O ⊗[R] C) := Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat O

end GlobalTheory.GoodEtale
end
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEtale_of_galois_descent_hartogs : ∀ (A R C O : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → GlobalTheory.GoodEtale.Hart A R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    Nonempty (C →ₐ[R] O) →
    Module.Finite R C ∧ Algebra.Etale R C := by
  first | (exact @GlobalTheory.GoodEtale.descent_finiteEtale) | (exact GlobalTheory.GoodEtale.descent_finiteEtale) | (intros; apply GlobalTheory.GoodEtale.descent_finiteEtale  <;> assumption)
end
