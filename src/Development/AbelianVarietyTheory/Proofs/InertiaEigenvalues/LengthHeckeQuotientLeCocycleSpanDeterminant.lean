import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetOneAddSmulBlkMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import BuildAid.ForwardExisting

section
open scoped BigOperators

namespace GlobalTheory.BlockDetPoly

def coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ) :
    Subalgebra (MvPolynomial (Fin m) O) (X → MvPolynomial (Fin m) O) where
  carrier := {f | ∀ d, (fun x => MvPolynomial.coeff d (f x)) ∈ T}
  mul_mem' := by
    intro f g hf hg d
    have : (fun x => MvPolynomial.coeff d ((f * g) x)) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal d,
        (fun x => MvPolynomial.coeff p.1 (f x)) * (fun x => MvPolynomial.coeff p.2 (g x)) := by
      funext x
      simp [MvPolynomial.coeff_mul, Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg d
    have : (fun x => MvPolynomial.coeff d ((f + g) x)) =
        (fun x => MvPolynomial.coeff d (f x)) + (fun x => MvPolynomial.coeff d (g x)) := by
      funext x
      simp
    rw [this]
    exact T.add_mem (hf _) (hg _)
  algebraMap_mem' := fun p d => T.algebraMap_mem (MvPolynomial.coeff d p)

theorem C_mem_coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (t : X → O) (ht : t ∈ T) : (fun x => MvPolynomial.C (t x)) ∈ coeffSub T m := by
  show ∀ d : Fin m →₀ ℕ,
    (fun x => MvPolynomial.coeff d (MvPolynomial.C (t x) : MvPolynomial (Fin m) O)) ∈ T
  intro d
  rcases eq_or_ne d 0 with rfl | hd
  · simpa using ht
  · have h0 : (fun x => MvPolynomial.coeff d (MvPolynomial.C (t x) : MvPolynomial (Fin m) O)) = 0 := by
      funext x
      simp [MvPolynomial.coeff_C, Ne.symm hd]
    rw [h0]
    exact T.zero_mem

theorem det_comb_mem {O X Q : Type} [CommRing O] [CommRing Q] (T : Subalgebra O (X → O)) {n : ℕ}
    (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O))
    (hR : ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) →
      ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T)
    (φ : O →+* Q) (S : Subalgebra Q (X → Q)) (hS : ∀ t ∈ T, (fun x => φ (t x)) ∈ S)
    {J : Type} [Fintype J] (b : J → X → Matrix (Fin n) (Fin n) O) (hb : ∀ j, b j ∈ R)
    (c : J → Q) : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) ∈ S := by
  classical

  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a : Fin (Fintype.card J) → X → Matrix (Fin n) (Fin n) O := fun k => b (e k)

  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Fintype.card J)) (X → O)) :=
    Matrix.of fun i j => ∑ k, MvPolynomial.X k * MvPolynomial.C (fun x => a k x i j)
  have hcoef : ∀ d, MvPolynomial.coeff d A.det ∈ T := by
    intro d
    have h1 : MvPolynomial.coeff d A.det = fun x => MvPolynomial.coeff d (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
          (a k x).map MvPolynomial.C)) := by
      funext x
      have h2 : MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) A.det =
          Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
            (a k x).map MvPolynomial.C) := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        simp [A, Matrix.sum_apply]
      rw [← h2, MvPolynomial.coeff_map]
      rfl
    rw [h1]
    exact hR _ a (fun k => hb (e k)) d

  have h3 : ∀ x, Matrix.det (∑ j, c j • (b j x).map φ) =
      MvPolynomial.eval₂ (φ.comp (Pi.evalRingHom (fun _ : X => O) x)) (fun k => c (e k)) A.det := by
    intro x
    rw [← MvPolynomial.coe_eval₂Hom, RingHom.map_det]
    congr 1
    ext i j
    simp only [A, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_C, RingHom.comp_apply, Pi.evalRingHom_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    exact (e.sum_comp (fun j' => c j' * φ (b j' x i j))).symm
  have key : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) =
      ∑ d ∈ A.det.support, (fun x => φ (MvPolynomial.coeff d A.det x)) *
        algebraMap Q (X → Q) (∏ k, c (e k) ^ d k) := by
    funext x
    rw [h3, MvPolynomial.eval₂_eq', Finset.sum_apply]
    simp
  rw [key]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hcoef d)) (S.algebraMap_mem _)

private theorem mem_coeffSub_iff_forall_coeff_mem {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (f : X → MvPolynomial (Fin m) O) :
    f ∈ coeffSub T m ↔ ∀ d, (fun x => MvPolynomial.coeff d (f x)) ∈ T := Iff.rfl

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T) → ∀ (m g : ℕ) (Θ : Fin m → Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ k p q, Θ k p q ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) * MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2)))) ∈ T := by
  intro O X _ T n R hR m g Θ hΘ d
  classical

  let ψ : (X → Matrix (Fin n) (Fin n) O) →+* (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    RingHom.compLeft (MvPolynomial.C : O →+* MvPolynomial (Fin m) O).mapMatrix X
  have hψ : ∀ (a : X → Matrix (Fin n) (Fin n) O) x, ψ a x = (a x).map MvPolynomial.C :=
    fun _ _ => rfl
  let s : Submonoid (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) := R.toSubmonoid.map ψ
  let R' : Subalgebra (MvPolynomial (Fin m) O) (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    Algebra.adjoin (MvPolynomial (Fin m) O) (s : Set _)

  have hrep : ∀ F ∈ R', ∃ (N : ℕ) (c : Fin N → MvPolynomial (Fin m) O)
      (b : Fin N → X → Matrix (Fin n) (Fin n) O), (∀ j, b j ∈ R) ∧ F = ∑ j, c j • ψ (b j) := by
    intro F hF
    have hF' : F ∈ Submodule.span (MvPolynomial (Fin m) O) (s : Set _) := by
      have h := Algebra.adjoin_eq_span (R := MvPolynomial (Fin m) O)
        (s : Set (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)))
      rw [Submonoid.closure_eq] at h
      rw [← h]
      exact hF
    obtain ⟨N, c, b, hsum⟩ := Submodule.mem_span_set'.mp hF'
    choose b' hb' hbe using fun j => Submonoid.mem_map.mp (b j).2
    refine ⟨N, c, b', fun j => hb' j, ?_⟩
    rw [← hsum]
    simp [hbe]

  have hR' : ∀ (m' : ℕ) (a : Fin m' → X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)),
      (∀ k, a k ∈ R') → ∀ d' : Fin m' →₀ ℕ, (fun x => MvPolynomial.coeff d' (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C))) ∈ coeffSub T m := by
    intro m' a ha d'
    choose N c b hb hab using fun k => hrep (a k) (ha k)
    have hS : ∀ t ∈ T, (fun x => ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (t x)) ∈ coeffSub (coeffSub T m) m' :=
      fun t ht => C_mem_coeffSub (coeffSub T m) m' _ (C_mem_coeffSub T m t ht)
    have h := det_comb_mem T R hR ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (coeffSub (coeffSub T m) m') hS
      (J := Σ k, Fin (N k)) (fun kj => b kj.1 kj.2) (fun kj => hb kj.1 kj.2)
      (fun kj => MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2))
    have heq : ∀ x, (∑ kj : (Σ k, Fin (N k)), (MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2) :
          MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) • (b kj.1 kj.2 x).map
          ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
            (MvPolynomial (Fin m) O)).comp MvPolynomial.C)) =
        ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C := by
      intro x
      ext i j
      simp [hab, hψ, Matrix.sum_apply, Fintype.sum_sigma, Finset.mul_sum, mul_assoc, Finset.sum_apply]
    simp only [heq] at h
    exact (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp h d'

  have hblk : ∀ p q, (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
      (Θ k p q x).map MvPolynomial.C) ∈ R' := by
    intro p q
    have h4 : (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
        (Θ k p q x).map MvPolynomial.C) = ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • ψ (Θ k p q) := by
      funext x
      simp [Finset.sum_apply, hψ]
    rw [h4]
    exact R'.sum_mem fun k _ =>
      R'.smul_mem (Algebra.subset_adjoin (Submonoid.mem_map.mpr ⟨Θ k p q, hΘ k p q, rfl⟩)) _
  have h5 := (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp (GlobalTheory.BlockDet.main (coeffSub T m) n R' hR' g _ hblk) d
  have h6 : ∀ x, (Matrix.of fun (pa qb : Fin g × Fin n) => (∑ k, (MvPolynomial.X k :
        MvPolynomial (Fin m) O) • (Θ k pa.1 qb.1 x).map MvPolynomial.C) pa.2 qb.2) =
      Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) *
        MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2) := by
    intro x
    ext pa qb
    simp [Matrix.sum_apply]
  simp only [h6] at h5
  exact h5

end GlobalTheory.BlockDetPoly
end

section
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
open IsDiscreteValuationRing

namespace GlobalTheory.DetGen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem length_quot_le_of_ker_le' {R X S : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup S]
    [Module R S] (f : X →ₗ[R] S) (P : Submodule R X) (h : LinearMap.ker f ≤ P) :
    Module.length R (X ⧸ P) ≤ Module.length R S := by
  refine (Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)).trans ?_
  refine Module.length_le_of_injective ((LinearMap.ker f).liftQ f le_rfl) ?_
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem exists_C_mul_primitive {σ : Type} (F : MvPolynomial σ O) :
    ∃ (c : O) (G : MvPolynomial σ O), F = MvPolynomial.C c * G ∧
      MvPolynomial.map (IsLocalRing.residue O) G ≠ 0 := by
  classical
  by_cases hF : F = 0
  · exact ⟨0, 1, by simp [hF], by simp⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image F.support (fun m => addVal O (F.coeff m))
    (MvPolynomial.support_nonempty.2 hF)
  have hc : F.coeff m ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have hd : MvPolynomial.C (F.coeff m) ∣ F := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : i ∈ F.support
    · exact addVal_le_iff_dvd.1 (hmin i hi)
    · rw [MvPolynomial.notMem_support_iff.1 hi]; exact dvd_zero _
  obtain ⟨G, hG⟩ := hd
  refine ⟨F.coeff m, G, hG, fun h0 => ?_⟩
  have h1 : F.coeff m = F.coeff m * G.coeff m := by
    conv_lhs => rw [hG]
    rw [MvPolynomial.coeff_C_mul]
  have h2 : G.coeff m = 1 := by
    apply mul_left_cancel₀ hc
    rw [← h1, mul_one]
  have h3 := congrArg (MvPolynomial.coeff m) h0
  rw [MvPolynomial.coeff_map, h2] at h3
  simp at h3

theorem length_quot_le_of_coeff_prod {σ J : Type} [Fintype J] (F : J → MvPolynomial σ O) (x : J → σ → O)
    (I : Ideal O) (h : ∀ m, MvPolynomial.coeff m (∏ j, F j) ∈ I) :
    Module.length O (O ⧸ I) ≤ ∑ j, addVal O (MvPolynomial.eval (x j) (F j)) := by
  classical
  choose c G hF hG using fun j => exists_C_mul_primitive (F j)
  have h1 : MvPolynomial.map (IsLocalRing.residue O) (∏ j, G j) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hG j
  obtain ⟨m, hm⟩ : ∃ m, MvPolynomial.coeff m (MvPolynomial.map (IsLocalRing.residue O) (∏ j, G j)) ≠ 0 := by
    by_contra! hh
    exact h1 (MvPolynomial.ext _ _ fun m => by simpa using hh m)
  rw [MvPolynomial.coeff_map] at hm
  have hu : IsUnit (MvPolynomial.coeff m (∏ j, G j)) := by
    by_contra hn
    exact hm ((IsLocalRing.residue_eq_zero_iff _).2 hn)
  have h2 : (∏ j, F j) = MvPolynomial.C (∏ j, c j) * ∏ j, G j := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hF j
  have h3 := h m
  rw [h2, MvPolynomial.coeff_C_mul] at h3
  have h4 : (∏ j, c j) ∈ I := (Ideal.mul_unit_mem_iff_mem I hu).1 h3
  have h5 : Ideal.span {∏ j, c j} ≤ I := (Ideal.span_singleton_le_iff_mem I).2 h4
  calc Module.length O (O ⧸ I) ≤ Module.length O (O ⧸ Ideal.span {∏ j, c j}) :=
        Module.length_le_of_surjective (Submodule.factor h5) (Submodule.factor_surjective h5)
    _ = addVal O (∏ j, c j) := Ring.ord_eq_addVal _
    _ = ∑ j, addVal O (c j) := GlobalTheory.addVal_finset_prod _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => addVal_le_iff_dvd.2 ⟨MvPolynomial.eval (x j) (G j), by
        rw [hF j]; simp⟩

theorem addVal_det_le_length {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module O V]
    (M : Matrix ι ι O) (π : (ι → FractionRing O) →ₗ[O] V)
    (hπ : ∀ y, π y = 0 → ∀ i, ∃ a, algebraMap O (FractionRing O) a = y i) (S : Submodule O V)
    (hS : ∀ y, (∀ p, ∃ a, algebraMap O (FractionRing O) a =
      (M.map (algebraMap O (FractionRing O))).mulVec y p) → π y ∈ S) :
    addVal O M.det ≤ Module.length O S := by
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  set M' := M.map (algebraMap O (FractionRing O)) with hM'
  by_cases h0 : M.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! hh
      exact hv0 (funext hh)
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
    have key : ∀ n : ℕ, (n : ℕ∞) ≤ Module.length O S := by
      intro n
      let y : ι → FractionRing O := fun k =>
        (algebraMap O (FractionRing O) (v i * ϖ ^ n))⁻¹ * algebraMap O (FractionRing O) (v k)
      have hy : M'.mulVec y = 0 := by
        have : y = (algebraMap O (FractionRing O) (v i * ϖ ^ n))⁻¹ • (algebraMap O (FractionRing O) ∘ v) := rfl
        rw [this, Matrix.mulVec_smul]
        funext p
        have h1 := RingHom.map_mulVec (algebraMap O (FractionRing O)) M v p
        rw [hv] at h1
        simp only [Pi.smul_apply, hM', ← h1]
        simp
      have hyS : π y ∈ S := hS y fun p => ⟨0, by rw [hy]; simp⟩
      have h2 := length_quot_le_of_ker_le' (LinearMap.toSpanSingleton O S ⟨π y, hyS⟩)
        (Ideal.span {ϖ ^ n}) (by
          intro a ha
          have h3 : π (a • y) = 0 := by
            rw [map_smul]
            exact congrArg Subtype.val (LinearMap.mem_ker.1 ha)
          obtain ⟨b, hb⟩ := hπ _ h3 i
          refine Ideal.mem_span_singleton'.2 ⟨b, hinj ?_⟩
          have h4 : algebraMap O (FractionRing O) (v i) ≠ 0 := fun h => hi (hinj (by simpa using h))
          have h5 : algebraMap O (FractionRing O) ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by simpa using h))
          rw [map_mul, hb]
          simp only [y, Pi.smul_apply, Algebra.smul_def, map_mul, map_pow]
          field_simp)
      have h6 : Module.length O (O ⧸ Ideal.span {ϖ ^ n}) = addVal O (ϖ ^ n) := Ring.ord_eq_addVal _
      rw [h6, addVal_pow, addVal_uniformizer hϖ] at h2
      simpa using h2
    have : Module.length O S = ⊤ := by
      by_contra hne
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
      have := key (k + 1)
      rw [← hk] at this
      exact absurd (ENat.coe_le_coe.1 this) (by omega)
    rw [this]; exact le_top
  · have hdet : IsUnit M'.det := by
      have : M'.det = algebraMap O (FractionRing O) M.det := (RingHom.map_det _ M).symm
      rw [this]
      exact Ne.isUnit fun h => h0 (hinj (by simpa using h))
    let φ : (ι → O) →ₗ[O] (ι → FractionRing O) :=
      ((M'⁻¹).mulVecLin.restrictScalars O).comp (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) ι)
    have hφ : ∀ u, M'.mulVec (φ u) = algebraMap O (FractionRing O) ∘ u := by
      intro u
      change M'.mulVec ((M'⁻¹).mulVec (algebraMap O (FractionRing O) ∘ u)) = _
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hφS : ∀ u, (π.comp φ) u ∈ S := fun u => hS (φ u) fun p => ⟨u p, by rw [hφ]; rfl⟩
    rw [← GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det]
    refine length_quot_le_of_ker_le' (LinearMap.codRestrict S (π.comp φ) hφS) _ ?_
    intro u hu
    have h3 : π (φ u) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hu)
    choose w hw using hπ _ h3
    refine ⟨w, funext fun p => hinj ?_⟩
    have h4 : φ u = algebraMap O (FractionRing O) ∘ w := funext fun i => (hw i).symm
    have h5 := congrFun (hφ u) p
    rw [h4] at h5
    rw [Matrix.mulVecLin_apply, RingHom.map_mulVec]
    exact h5

omit [IsDiscreteValuationRing O] in
theorem matKO_mk {k : ℕ} (A : Matrix (Fin k) (Fin k) O) (y : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec y) := rfl

omit [IsDiscreteValuationRing O] in
theorem mk_eq_zero_iff {k : ℕ} (y : Fin k → FractionRing O) :
    (Submodule.Quotient.mk y : KOG O k) = 0 ↔ ∀ i, ∃ a, algebraMap O (FractionRing O) a = y i := by
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, rfl⟩ i
    exact ⟨u i, rfl⟩
  · intro h
    choose u hu using h
    exact ⟨u, funext hu⟩

theorem exists_family_span {ι : Type} [Fintype ι] [DecidableEq ι] (N : Submodule O (ι → O)) :
    ∃ r : ι → ι → O, (∀ p, r p ∈ N) ∧ ∀ P : Submodule O (ι → O), (∀ p, r p ∈ P) → N ≤ P := by
  classical
  obtain ⟨n, snf⟩ := N.smithNormalForm (Pi.basisFun O ι)
  refine ⟨Function.extend snf.f (fun i => (snf.bN i : ι → O)) 0, fun p => ?_, fun P hP => ?_⟩
  · by_cases h : ∃ i, snf.f i = p
    · obtain ⟨i, rfl⟩ := h
      rw [snf.f.injective.extend_apply]
      exact (snf.bN i).2
    · rw [Function.extend_apply' _ _ _ h]
      exact N.zero_mem
  · intro v hv
    have h1 : (⟨v, hv⟩ : N) ∈ P.comap N.subtype := by
      have : Submodule.span O (Set.range snf.bN) ≤ P.comap N.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have := hP (snf.f i)
        rw [snf.f.injective.extend_apply] at this
        exact this
      exact this (by rw [snf.bN.span_eq]; trivial)
    exact h1

theorem exists_relations {A : Type} [Ring A] [Algebra O A] {d : ℕ} (ψ : A →ₐ[O] Matrix (Fin d) (Fin d) O)
    (hψ : Function.Surjective ψ) {g : ℕ} (Rel : Submodule A (Fin g → A)) :
    ∃ Θ : Fin g → Fin g → A, (∀ p, Θ p ∈ Rel) ∧
      addVal O (Matrix.det (Matrix.of fun (pa qb : Fin g × Fin d) => ψ (Θ pa.1 qb.1) pa.2 qb.2)) ≤
        Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ (θ q))).comp
          (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d))) := by
  classical
  let N : Submodule O (Fin g × Fin d → O) :=
    { carrier := {v | ∀ a, ∃ θ ∈ Rel, ∀ q a' b, ψ (θ q) a' b = if a' = a then v (q, b) else 0}
      add_mem' := by
        intro v w hv hw a
        obtain ⟨θ, hθ, h⟩ := hv a
        obtain ⟨θ', hθ', h'⟩ := hw a
        refine ⟨θ + θ', Rel.add_mem hθ hθ', fun q a' b => ?_⟩
        rw [Pi.add_apply, map_add, Matrix.add_apply, h, h']
        split_ifs <;> simp
      zero_mem' := fun a => ⟨0, Rel.zero_mem, fun q a' b => by simp⟩
      smul_mem' := by
        intro c v hv a
        obtain ⟨θ, hθ, h⟩ := hv a
        refine ⟨c • θ, Rel.smul_of_tower_mem c hθ, fun q a' b => ?_⟩
        rw [Pi.smul_apply, map_smul, Matrix.smul_apply, h]
        split_ifs <;> simp }
  have hrow : ∀ θ ∈ Rel, ∀ a₀, (fun qb : Fin g × Fin d => ψ (θ qb.1) a₀ qb.2) ∈ N := by
    intro θ hθ a₀ a
    obtain ⟨e, he⟩ := hψ (Matrix.single a a₀ 1)
    refine ⟨e • θ, Rel.smul_mem e hθ, fun q a' b => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, map_mul, he]
    split_ifs with h
    · subst h
      simp
    · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _
  obtain ⟨r, hrN, hr⟩ := exists_family_span N
  choose θ hθ hθr using fun (p : Fin g) (a : Fin d) => hrN (p, a) a
  have hM : (Matrix.of fun (pa qb : Fin g × Fin d) => ψ ((∑ a, θ pa.1 a) qb.1) pa.2 qb.2) = Matrix.of r := by
    ext ⟨p, a⟩ ⟨q, b⟩
    simp [Finset.sum_apply, map_sum, Matrix.sum_apply, hθr]
  refine ⟨fun p => ∑ a, θ p a, fun p => Rel.sum_mem fun a _ => hθ p a, ?_⟩
  rw [hM]
  let π : (Fin g × Fin d → FractionRing O) →ₗ[O] (Fin g → KOG O d) :=
    LinearMap.pi fun q => (stdG O (FractionRing O) d).mkQ.comp
      (LinearMap.funLeft O (FractionRing O) fun b => (q, b))
  have hπ : ∀ y q, π y q = Submodule.Quotient.mk (fun b => y (q, b)) := fun _ _ => rfl
  refine addVal_det_le_length (Matrix.of r) π (fun y hy i => ?_) _ (fun y hy => ?_)
  · have := congrFun hy i.1
    rw [hπ] at this
    exact (mk_eq_zero_iff _).1 this i.2
  · let P : Submodule O (Fin g × Fin d → O) :=
      { carrier := {v | ∃ a, algebraMap O (FractionRing O) a = ∑ i, algebraMap O (FractionRing O) (v i) * y i}
        add_mem' := by
          rintro v w ⟨a, ha⟩ ⟨b, hb⟩
          exact ⟨a + b, by simp [ha, hb, add_mul, Finset.sum_add_distrib]⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c v ⟨a, ha⟩
          exact ⟨c * a, by simp [ha, Finset.mul_sum, mul_assoc]⟩ }
    have hNP : N ≤ P := hr P fun p => hy p
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro t ht
    have h1 : (∑ q : Fin g, (matKO (ψ (t q))).comp
          (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d)) (π y) =
        (stdG O (FractionRing O) d).mkQ
          (∑ q, ((ψ (t q)).map (algebraMap O (FractionRing O))).mulVec fun b => y (q, b)) := by
      rw [LinearMap.sum_apply, map_sum]
      rfl
    rw [h1, Submodule.mkQ_apply, mk_eq_zero_iff]
    intro a
    obtain ⟨c, hc⟩ := hNP (hrow t ht a)
    refine ⟨c, ?_⟩
    rw [hc, Fintype.sum_prod_type, Finset.sum_apply]
    rfl

theorem length_quot_le_sum_length : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [Ring A] [Algebra O A] (J : Type) [Fintype J] (d : J → ℕ) (ψ : ∀ j, A →ₐ[O] Matrix (Fin (d j)) (Fin (d j)) O), (∀ j, Function.Surjective (ψ j)) → ∀ (g : ℕ) (Rel : Submodule A (Fin g → A)) (I : Ideal O), (∀ (n : ℕ) (θ : Fin n → Fin g → Fin g → A), (∀ k p, θ k p ∈ Rel) → ∀ m : Fin n →₀ ℕ, MvPolynomial.coeff m (∏ j, Matrix.det (Matrix.of fun (pa qb : Fin g × Fin (d j)) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin n) O) * MvPolynomial.C (ψ j (θ k pa.1 qb.1) pa.2 qb.2))) ∈ I) → Module.length O (O ⧸ I) ≤ ∑ j, Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ j (θ q))).comp (LinearMap.proj q : (Fin g → KOG O (d j)) →ₗ[O] KOG O (d j)))) := by
  intro O _ _ _ A _ _ J _ d ψ hψ g Rel I hI
  classical
  choose Θ hΘ hle using fun j => exists_relations (ψ j) (hψ j) Rel
  let e := Fintype.equivFin J
  have h1 := length_quot_le_of_coeff_prod _ (fun j => Pi.single (e j) (1 : O)) I
    (hI (Fintype.card J) (fun k => Θ (e.symm k)) fun k p => hΘ _ p)
  refine h1.trans (Finset.sum_le_sum fun j _ => le_trans (le_of_eq ?_) (hle j))
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext pa qb
  simp [Pi.single_apply]

end GlobalTheory.DetGen
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [Ring A] [Algebra O A] (J : Type) [Fintype J] (d : J → ℕ) (ψ : ∀ j, A →ₐ[O] Matrix (Fin (d j)) (Fin (d j)) O), (∀ j, Function.Surjective (ψ j)) → ∀ (g : ℕ) (Rel : Submodule A (Fin g → A)) (I : Ideal O), (∀ (n : ℕ) (θ : Fin n → Fin g → Fin g → A), (∀ k p, θ k p ∈ Rel) → ∀ m : Fin n →₀ ℕ, MvPolynomial.coeff m (∏ j, Matrix.det (Matrix.of fun (pa qb : Fin g × Fin (d j)) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin n) O) * MvPolynomial.C (ψ j (θ k pa.1 qb.1) pa.2 qb.2))) ∈ I) → Module.length O (O ⧸ I) ≤ ∑ j, Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ j (θ q))).comp (LinearMap.proj q : (Fin g → KOG O (d j)) →ₗ[O] KOG O (d j)))) := by
  atlas_forward_decl GlobalTheory.DetGen.length_quot_le_sum_length
end

section
namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem cutVal_exists_single {O X : Type} [CommRing O] [IsDomain O] [Fintype X]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (x : X) :
    ∃ g ∈ T, g x ≠ 0 ∧ ∀ y, y ≠ x → g y = 0 := by
  classical
  have key : ∀ y : X, ∃ f ∈ T, f x ≠ 0 ∧ (y ≠ x → f y = 0) := by
    intro y
    by_cases hy : y = x
    · exact ⟨1, one_mem _, one_ne_zero, fun h => absurd hy h⟩
    · obtain ⟨f, hf, hne⟩ := hsep y x hy
      refine ⟨f - algebraMap _ _ (f y), sub_mem hf (Subalgebra.algebraMap_mem _ _), ?_, fun _ => ?_⟩
      · simpa [sub_eq_zero] using hne.symm
      · simp
  choose f hf h1 h2 using key
  refine ⟨∏ y, f y, prod_mem fun y _ => hf y, ?_, fun y hy => ?_⟩
  · rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.2 fun y _ => h1 y
  · rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (h2 y hy)

theorem cutVal_coord_eq_zero {O X X' ι : Type} [CommRing O] [IsDomain O] [Fintype X] [Fintype ι]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y)
    (p : X' → X) (b : ι → X' → O)
    (huniq : ∀ cf : ι → T, (0 : X' → O) = ∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k →
      cf = 0)
    (cf : ι → T) (x : X)
    (h0 : ∀ x', p x' = x → (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' = 0)
    (k : ι) : (cf k : X → O) x = 0 := by
  obtain ⟨g, hg, hx, hy⟩ := cutVal_exists_single T hsep x
  have h := huniq (fun k => ⟨g, hg⟩ * cf k) (by
    funext x'
    have : (∑ k, ((fun x' => (((⟨g, hg⟩ : T) * cf k : T) : X → O) (p x')) : X' → O) * b k) x' =
        g (p x') * (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' := by
      simp [Finset.sum_apply, Finset.mul_sum, mul_assoc]
    rw [this]
    by_cases hp : p x' = x
    · rw [h0 x' hp]; simp
    · rw [hy _ hp]; simp)
  have h2 : g x * (cf k : X → O) x = 0 := by
    have := congrArg (fun c : ι → T => (c k : X → O) x) h
    simpa using this
  exact (mul_eq_zero.1 h2).resolve_left hx

theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

end GlobalTheory.Cut
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutValue_mem_heckeValueIdealOffSupport : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  first | exact @GlobalTheory.Cut.value_mem_ccOff | exact GlobalTheory.Cut.value_mem_ccOff | (intros; apply GlobalTheory.Cut.value_mem_ccOff <;> assumption)
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.ResidualSelmer

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → NoChiOff i r Xs → ∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → ∃ η : Fin D.R.nV → KK D.nd i, ∃ γ : GE D.nd, ((yg D.nd r S γ x').map (toK D.nd i)).mulVec η ≠ 0 := by
  intro D i r ρ π Xs S _ hG _ hN x' hx hZ
  have hrank : ((Eel D.nd S x').map (toK D.nd i)).rank = 1 := hG.2.2.2.2.2.2.2.2.2.2.1.1 x'
  by_contra hcon
  push Not at hcon
  have h0 : ∀ η : Fin D.R.nV → KK D.nd i, ((Eel D.nd S x').map (toK D.nd i)).mulVec η = 0 := by
    intro η
    apply hN _ hx hZ
    intro g
    have h := hcon η g
    have hy : yg D.nd r S g x' = rTwO D.nd i r (S.p x') g * Eel D.nd S x' - Eel D.nd S x' := by
      unfold yg
      rw [← Matrix.smul_mul]
      rfl
    rw [hy, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.sub_mulVec, sub_eq_zero,
      ← Matrix.mulVec_mulVec] at h
    exact h
  have hz : ((Eel D.nd S x').map (toK D.nd i)).mulVecLin = 0 := LinearMap.ext h0
  unfold Matrix.rank at hrank
  rw [hz, LinearMap.range_zero, finrank_bot] at hrank
  exact zero_ne_one hrank

end GlobalTheory.Cut.ResidualSelmer
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.CutDet

section Abs

open scoped Kronecker

variable {O : Type} [CommRing O] [IsDomain O]

theorem baer_KOG [IsPrincipalIdealRing O] (k : ℕ) : Module.Baer O (KOG O k) := by
  intro I g
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I)
  by_cases ha : a = 0
  · refine ⟨0, fun x hx => ?_⟩
    have hx0 : x = 0 := by simpa [ha] using hx
    subst hx0
    exact (map_zero g).symm
  · have hmem : a ∈ Submodule.span O ({a} : Set O) := Submodule.mem_span_singleton_self a
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (g ⟨a, hmem⟩)
    have ha' : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
    let m : KOG O k := Submodule.Quotient.mk ((algebraMap O (FractionRing O) a)⁻¹ • v)
    have hm : a • m = g ⟨a, hmem⟩ := by
      rw [← hv, ← Submodule.Quotient.mk_smul, ← algebraMap_smul (FractionRing O) a, smul_smul,
        mul_inv_cancel₀ ha', one_smul]
    refine ⟨LinearMap.toSpanSingleton O _ m, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.toSpanSingleton_apply, smul_assoc, hm, ← map_smul]
    rfl

theorem exists_ext {P M Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup M] [Module O M]
    [AddCommGroup Q] [Module O Q] (hQ : Module.Baer O Q) (F : P →ₗ[O] M) (G : P →ₗ[O] Q)
    (h : LinearMap.ker F ≤ LinearMap.ker G) : ∃ φ : M →ₗ[O] Q, ∀ p, φ (F p) = G p := by
  obtain ⟨φ, hφ⟩ := hQ.extension_property ((LinearMap.ker F).liftQ F le_rfl)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)) ((LinearMap.ker F).liftQ G h)
  exact ⟨φ, fun p => LinearMap.congr_fun hφ (Submodule.Quotient.mk p)⟩

theorem matKO_mk {k : ℕ} (A : Matrix (Fin k) (Fin k) O) (v : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec v) := rfl

def matHom (k : ℕ) : Matrix (Fin k) (Fin k) O →ₐ[O] Module.End O (KOG O k) :=
  AlgHom.ofLinearMap
    { toFun := matKO
      map_add' := fun A B => LinearMap.ext fun x => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [LinearMap.add_apply, matKO_mk, matKO_mk, matKO_mk, ← Submodule.Quotient.mk_add,
          Matrix.map_add _ (map_add _), Matrix.add_mulVec]
      map_smul' := fun c A => LinearMap.ext fun x => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [LinearMap.smul_apply, matKO_mk, matKO_mk, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1
        funext j
        rw [Pi.smul_apply, Algebra.smul_def c (Matrix.mulVec _ _ _)]
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }
    (LinearMap.ext fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change matKO 1 _ = _
      rw [matKO_mk, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
      rfl)
    (fun A B => LinearMap.ext fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change matKO (A * B) (Submodule.Quotient.mk v) = matKO A (matKO B (Submodule.Quotient.mk v))
      rw [matKO_mk, matKO_mk, matKO_mk, Matrix.map_mul, Matrix.mulVec_mulVec])

theorem matHom_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) O) : matHom k A = matKO A := rfl

theorem length_sol_le [IsPrincipalIdealRing O] {M Γ : Type} [Ring M] [Algebra O M] (A : Subalgebra O M)
    {d g : ℕ} (ψ : A →ₐ[O] Matrix (Fin d) (Fin d) O) (ψ' : M → Matrix (Fin d) (Fin d) O)
    (hψ : ∀ a : A, ψ a = ψ' a) (y : Γ → M) (γ : Fin g → Γ) (Y Z : M → Prop)
    (hY : ∀ m, Y m → ∃ θ : Fin g → A, m = ∑ q, (θ q : M) * y (γ q))
    (Rel : Submodule A (Fin g → A)) (hRel : ∀ θ : Fin g → A, Z (∑ q, (θ q : M) * y (γ q)) → θ ∈ Rel)
    (hZ : Z 0) :
    Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ (θ q))).comp
      (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d))) ≤
    Module.length O ↥(Submodule.span O {c : Γ → KOG O d | ∃ φ : M →ₗ[O] KOG O d,
      (∀ a, a ∈ A → ∀ m, Y m → φ (a * m) = matKO (ψ' a) (φ m)) ∧
      (∀ m, Y m → Z m → φ m = 0) ∧ c = fun s => φ (y s)}) := by
  classical
  set C := Submodule.span O {c : Γ → KOG O d | ∃ φ : M →ₗ[O] KOG O d,
      (∀ a, a ∈ A → ∀ m, Y m → φ (a * m) = matKO (ψ' a) (φ m)) ∧
      (∀ m, Y m → Z m → φ m = 0) ∧ c = fun s => φ (y s)} with hC
  have hle : (⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ (θ q))).comp
      (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d))) ≤
      C.map (LinearMap.funLeft O (KOG O d) γ) := by
    intro w hw
    have hw' : ∀ θ ∈ Rel, ∑ q, matKO (ψ (θ q)) (w q) = 0 := by
      intro θ hθ
      have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hw θ) hθ
      simpa [LinearMap.sum_apply] using this
    let F : (Fin g → A) →ₗ[O] M := ∑ q, (LinearMap.mulRight O (y (γ q))).comp
      (A.val.toLinearMap.comp (LinearMap.proj q))
    let G : (Fin g → A) →ₗ[O] KOG O d := ∑ q, (LinearMap.applyₗ (w q)).comp
      ((matHom d).toLinearMap.comp (ψ.toLinearMap.comp (LinearMap.proj q)))
    have hF : ∀ θ, F θ = ∑ q, (θ q : M) * y (γ q) := fun θ => by
      simp [F, LinearMap.sum_apply]
    have hG : ∀ θ, G θ = ∑ q, matKO (ψ (θ q)) (w q) := fun θ => by
      simp [G, LinearMap.sum_apply, matHom_apply]
    obtain ⟨φ, hφ⟩ := exists_ext (baer_KOG d) F G (by
      intro θ hθ
      rw [LinearMap.mem_ker] at hθ ⊢
      rw [hG]
      refine hw' θ (hRel θ ?_)
      rw [← hF, hθ]
      exact hZ)
    refine ⟨fun s => φ (y s), Submodule.subset_span ⟨φ, ?_, ?_, rfl⟩, ?_⟩
    · intro a ha m hm
      obtain ⟨θ, rfl⟩ := hY m hm
      have h1 : a * ∑ q, (θ q : M) * y (γ q) = F (fun q => ⟨a, ha⟩ * θ q) := by
        rw [hF, Finset.mul_sum]
        simp [mul_assoc]
      rw [h1, ← hF, hφ, hφ, hG, hG, map_sum, ← hψ ⟨a, ha⟩]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, ← matHom_apply, map_mul]
      rfl
    · intro m hm hz
      obtain ⟨θ, rfl⟩ := hY m hm
      rw [← hF, hφ, hG]
      exact hw' θ (hRel θ hz)
    · funext q
      have h1 : y (γ q) = F (Pi.single q 1) := by
        rw [hF, Finset.sum_eq_single q] <;> simp +contextual
      change φ (y (γ q)) = w q
      rw [h1, hφ, hG, Finset.sum_eq_single q]
      · rw [Pi.single_eq_same, map_one, ← matHom_apply, map_one]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, map_zero, ← matHom_apply, map_zero]
        rfl
      · simp
  refine (Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)).trans ?_
  exact Module.length_le_of_surjective ((LinearMap.funLeft O (KOG O d) γ).submoduleMap C)
    (LinearMap.submoduleMap_surjective _ _)

theorem det_blocks {L ι ρ τ G : Type} [CommRing L] [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ] [Fintype G] [DecidableEq G]
    (P : Matrix (ρ ⊕ τ) ι L) (Q : Matrix ι (ρ ⊕ τ) L) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (a : G → G → Matrix ι ι L) (b : G → G → Matrix ρ ρ L) (c : τ → G → G → L)
    (h : ∀ p q, P * a p q * Q = Matrix.fromBlocks (b p q) 0 0 (Matrix.diagonal fun j => c j p q)) :
    (Matrix.of fun pa qb : G × ι => a pa.1 qb.1 pa.2 qb.2).det =
      (Matrix.of fun pa qb : G × ρ => b pa.1 qb.1 pa.2 qb.2).det *
        ∏ j, (Matrix.of fun p q => c j p q).det := by
  have h1 : ((1 : Matrix G G L) ⊗ₖ P) * ((1 : Matrix G G L) ⊗ₖ Q) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hPQ, one_mul, Matrix.one_kronecker_one]
  have h2 : ((1 : Matrix G G L) ⊗ₖ Q) * ((1 : Matrix G G L) ⊗ₖ P) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hQP, one_mul, Matrix.one_kronecker_one]
  rw [← Matrix.det_conj_of_mul_eq_one h1 h2, ← Matrix.det_blockDiagonal, ← Matrix.det_fromBlocks_zero₂₁ _ 0,
    ← Matrix.det_submatrix_equiv_self (Equiv.prodSumDistrib G ρ τ)]
  congr 1
  ext ⟨p, i⟩ ⟨q, j⟩
  have h3 : (((1 : Matrix G G L) ⊗ₖ P) * (Matrix.of fun pa qb : G × ι => a pa.1 qb.1 pa.2 qb.2) *
      ((1 : Matrix G G L) ⊗ₖ Q)) (p, i) (q, j) = (P * a p q * Q) i j := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_ite_eq]
  rw [h3, h]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.blockDiagonal_apply, Matrix.diagonal_apply]

theorem exists_conj {K ι ρ τ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
    [Fintype τ] [DecidableEq τ] (e : (ι → K) ≃ₗ[K] ((ρ → K) × (τ → K))) :
    ∃ (P : Matrix (ρ ⊕ τ) ι K) (Q : Matrix ι (ρ ⊕ τ) K), P * Q = 1 ∧ Q * P = 1 ∧
      ∀ (a : Matrix ι ι K) (b : Matrix ρ ρ K) (c : τ → K),
        (∀ u, e (a.mulVec u) = (b.mulVec (e u).1, fun j => c j * (e u).2 j)) →
        P * a * Q = Matrix.fromBlocks b 0 0 (Matrix.diagonal c) := by
  let e' := e.trans (LinearEquiv.sumArrowLequivProdArrow ρ τ K K).symm
  refine ⟨LinearMap.toMatrix' e'.toLinearMap, LinearMap.toMatrix' e'.symm.toLinearMap, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · intro a b c h
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    change (LinearEquiv.sumArrowLequivProdArrow ρ τ K K).symm (e (a.mulVec (e.symm
      (LinearEquiv.sumArrowLequivProdArrow ρ τ K K v)))) = _
    rw [h, e.apply_symm_apply, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec]
    funext j
    rcases j with j | j
    · simp
      rfl
    · simp [Matrix.mulVec_diagonal]

end Abs

section Abs2

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

theorem exists_homs (hinj : Function.Injective (algebraMap O K)) {X ι ρ τ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    (A : Subalgebra O (X → Matrix ι ι O)) (π : X)
    (P : Matrix (ρ ⊕ τ) ι K) (Q : Matrix ι (ρ ⊕ τ) K) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (ψρ : (X → Matrix ι ι O) → Matrix ρ ρ O) (ψχ : τ → (X → Matrix ι ι O) → O)
    (h : ∀ a ∈ A, P * (a π).map (algebraMap O K) * Q = Matrix.fromBlocks ((ψρ a).map (algebraMap O K)) 0 0
      (Matrix.diagonal fun j => algebraMap O K (ψχ j a))) :
    (∃ f : A →ₐ[O] Matrix ρ ρ O, ∀ a, f a = ψρ a) ∧ ∀ j, ∃ f : A →ₐ[O] O, ∀ a, f a = ψχ j a := by
  have uniq : ∀ (b b' : Matrix ρ ρ O) (c c' : τ → O),
      Matrix.fromBlocks (b.map (algebraMap O K)) 0 0 (Matrix.diagonal fun j => algebraMap O K (c j)) =
      Matrix.fromBlocks (b'.map (algebraMap O K)) 0 0 (Matrix.diagonal fun j => algebraMap O K (c' j)) →
      b = b' ∧ ∀ j, c j = c' j := by
    intro b b' c c' hh
    obtain ⟨h1, -, -, h2⟩ := Matrix.fromBlocks_inj.1 hh
    exact ⟨Matrix.map_injective hinj h1, fun j => hinj (congrFun (Matrix.diagonal_injective h2) j)⟩
  have hmul : ∀ a b : A, ψρ (a * b) = ψρ a * ψρ b ∧ ∀ j, ψχ j (a * b) = ψχ j a * ψχ j b := by
    intro a b
    refine uniq _ _ (fun j => ψχ j (a * b)) (fun j => ψχ j a * ψχ j b) ?_
    have h1 : P * ((a * b : X → Matrix ι ι O) π).map (algebraMap O K) * Q =
        (P * (a.1 π).map (algebraMap O K) * Q) * (P * (b.1 π).map (algebraMap O K) * Q) := by
      rw [Pi.mul_apply, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
    rw [← h _ (A.mul_mem a.2 b.2), h1, h _ a.2, h _ b.2, Matrix.fromBlocks_multiply]
    simp [Matrix.map_mul]
  have hadd : ∀ a b : A, ψρ (a + b) = ψρ a + ψρ b ∧ ∀ j, ψχ j (a + b) = ψχ j a + ψχ j b := by
    intro a b
    refine uniq _ _ (fun j => ψχ j (a + b)) (fun j => ψχ j a + ψχ j b) ?_
    rw [← h _ (A.add_mem a.2 b.2), Pi.add_apply, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul,
      h _ a.2, h _ b.2, Matrix.fromBlocks_add]
    simp [Matrix.map_add]
  have halg : ∀ c : O, ψρ (algebraMap O _ c) = algebraMap O _ c ∧ ∀ j, ψχ j (algebraMap O _ c) = c := by
    intro c
    refine uniq _ _ (fun j => ψχ j (algebraMap O _ c)) (fun _ => c) ?_
    have h1 : ∀ {κ : Type} [Fintype κ] [DecidableEq κ], (algebraMap O (Matrix κ κ O) c).map (algebraMap O K) =
        algebraMap O K c • (1 : Matrix κ κ K) := by
      intro κ _ _
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply, hij]
    rw [← h _ (A.algebraMap_mem c), Pi.algebraMap_apply, h1, h1, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hPQ, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.smul_one_eq_diagonal,
      Matrix.smul_one_eq_diagonal]
    simp
  refine ⟨⟨{ toFun := fun a => ψρ a
             map_one' := by simpa using (halg 1).1
             map_mul' := fun a b => (hmul a b).1
             map_zero' := by simpa using (halg 0).1
             map_add' := fun a b => (hadd a b).1
             commutes' := fun c => (halg c).1 }, fun _ => rfl⟩, fun j =>
    ⟨{ toFun := fun a => ψχ j a
       map_one' := by simpa using (halg 1).2 j
       map_mul' := fun a b => (hmul a b).2 j
       map_zero' := by simpa using (halg 0).2 j
       map_add' := fun a b => (hadd a b).2 j
       commutes' := fun c => (halg c).2 j }, fun _ => rfl⟩⟩

open MvPolynomial in

theorem det_generic_blocks (hinj : Function.Injective (algebraMap O K)) {ι ρ τ G N : Type}
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] [Fintype τ] [DecidableEq τ]
    [Fintype G] [DecidableEq G] [Fintype N]
    (P : Matrix (ρ ⊕ τ) ι K) (Q : Matrix ι (ρ ⊕ τ) K) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (a : N → G → G → Matrix ι ι O) (b : N → G → G → Matrix ρ ρ O) (c : τ → N → G → G → O)
    (h : ∀ k p q, P * (a k p q).map (algebraMap O K) * Q =
      Matrix.fromBlocks ((b k p q).map (algebraMap O K)) 0 0
        (Matrix.diagonal fun j => algebraMap O K (c j k p q))) :
    (Matrix.of fun pa qb : G × ι => ∑ k, (X k : MvPolynomial N O) * C (a k pa.1 qb.1 pa.2 qb.2)).det =
      (Matrix.of fun pa qb : G × ρ => ∑ k, (X k : MvPolynomial N O) * C (b k pa.1 qb.1 pa.2 qb.2)).det *
        ∏ j, (Matrix.of fun p q : G => ∑ k, (X k : MvPolynomial N O) * C (c j k p q)).det := by
  apply MvPolynomial.map_injective _ hinj
  have key := det_blocks (L := MvPolynomial N K) (P.map C) (Q.map C)
    (by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)])
    (fun p q => ∑ k, (X k : MvPolynomial N K) • ((a k p q).map (algebraMap O K)).map C)
    (fun p q => ∑ k, (X k : MvPolynomial N K) • ((b k p q).map (algebraMap O K)).map C)
    (fun j p q => ∑ k, (X k : MvPolynomial N K) * C (algebraMap O K (c j k p q))) (by
      intro p q
      rw [Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, h]
      ext1 i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Matrix.sum_apply, Matrix.diagonal_apply]
      split_ifs <;> simp)
  rw [map_mul, map_prod, RingHom.map_det, RingHom.map_det]
  simp only [RingHom.map_det]
  convert key using 2
  · ext1 i j
    simp [Matrix.sum_apply]
  · congr 1
    ext1 i j
    simp [Matrix.sum_apply]
  · congr 1
    funext l
    congr 1
    ext1 i j
    simp

open MvPolynomial in

theorem det_generic_eq_zero (hinj : Function.Injective (algebraMap O K)) {ι G N : Type}
    [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G] [Fintype N]
    (a : N → G → G → Matrix ι ι O) (v : G → ι → K) (hv : v ≠ 0)
    (h : ∀ k p, ∑ q, ((a k p q).map (algebraMap O K)).mulVec (v q) = 0) :
    (Matrix.of fun pa qb : G × ι => ∑ k, (X k : MvPolynomial N O) * C (a k pa.1 qb.1 pa.2 qb.2)).det = 0 := by
  apply MvPolynomial.map_injective _ hinj
  rw [RingHom.map_det, map_zero, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun qb => C (v qb.1 qb.2), fun h0 => hv ?_, ?_⟩
  · funext q j
    simpa using congrFun h0 (q, j)
  · funext ⟨p, i⟩
    have h1 : ∀ k, ∑ q, ∑ j, algebraMap O K (a k p q i j) * v q j = 0 := fun k => by
      simpa [Finset.sum_apply, Matrix.mulVec, dotProduct] using congrFun (h k p) i
    calc _ = ∑ k, (X k : MvPolynomial N K) * C (∑ q, ∑ j, algebraMap O K (a k p q i j) * v q j) := by
          simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
            map_sum, map_mul, map_X, map_C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type]
      _ = 0 := by simp [h1]

end Abs2

section Span

variable {O X Γ M : Type} [CommRing O] [Ring M] [Algebra O M] [Monoid Γ]

def spanAlg (T : Subalgebra O (X → O)) (rep : X → (Γ →* M)) : Subalgebra O (X → M) where
  carrier := {a | ∃ (m : ℕ) (f : Fin m → X → O) (g : Fin m → Γ), (∀ k, f k ∈ T) ∧
      a = ∑ k, fun x => f k x • rep x (g k)}
  mul_mem' := by
    rintro _ _ ⟨m, f, g, hf, rfl⟩ ⟨m', f', g', hf', rfl⟩
    let e := (finProdFinEquiv (m := m) (n := m')).symm
    refine ⟨m * m', fun k => f (e k).1 * f' (e k).2, fun k => g (e k).1 * g' (e k).2,
      fun k => T.mul_mem (hf _) (hf' _), ?_⟩
    rw [e.sum_comp (fun k => fun x => (f k.1 * f' k.2) x • rep x (g k.1 * g' k.2)), Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    funext x
    simp [smul_smul, mul_comm]
  add_mem' := by
    rintro _ _ ⟨m, f, g, hf, rfl⟩ ⟨m', f', g', hf', rfl⟩
    refine ⟨m + m', Fin.append f f', Fin.append g g', fun k => ?_, ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simpa using hf k
      · simpa using hf' k
    · rw [Fin.sum_univ_add]
      simp
  algebraMap_mem' := fun c => ⟨1, fun _ => algebraMap O _ c, fun _ => 1, fun _ => T.algebraMap_mem c, by
    funext x
    simp [Algebra.algebraMap_eq_smul_one]⟩

theorem exists_gens {B : Type} [Ring B] [Algebra O B] [IsNoetherian O B] (A : Subalgebra O B) (y : Γ → B) :
    ∃ (g : ℕ) (γ : Fin g → Γ), ∀ (m : ℕ) (a : Fin m → B) (s : Fin m → Γ), (∀ k, a k ∈ A) →
      ∃ θ : Fin g → A, ∑ k, a k * y (s k) = ∑ q, (θ q : B) * y (γ q) := by
  classical
  haveI : IsNoetherian A B := isNoetherian_of_tower O inferInstance
  obtain ⟨t, ht, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := A) (Set.range y)).1
    (IsNoetherian.noetherian _)
  choose σ hσ using fun b : t => ht b.2
  let e := t.equivFin.symm
  refine ⟨t.card, fun q => σ (e q), fun m a s ha => ?_⟩
  have h1 : ∑ k, a k * y (s k) ∈ Submodule.span A (Set.range fun q => y (σ (e q))) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    refine Submodule.smul_mem _ (⟨a k, ha k⟩ : A) (Submodule.span_mono ?_
      (hsp ▸ Submodule.subset_span ⟨s k, rfl⟩ : y (s k) ∈ Submodule.span A (t : Set B)))
    intro b hb
    exact ⟨e.symm ⟨b, hb⟩, by simp [hσ]⟩
  obtain ⟨θ, hθ⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
  exact ⟨θ, hθ.symm⟩

@[reducible] def blockDim (r : ℕ) {τ : Type} : Option τ → ℕ
  | none => r
  | some _ => 1

def blockHom {A τ : Type} [Ring A] [Algebra O A] {r : ℕ} (f : A →ₐ[O] Matrix (Fin r) (Fin r) O)
    (χ : τ → (A →ₐ[O] O)) : ∀ j : Option τ, A →ₐ[O] Matrix (Fin (blockDim r j)) (Fin (blockDim r j)) O
  | none => f
  | some c => (Algebra.ofId O (Matrix (Fin 1) (Fin 1) O)).comp (χ c)

end Span

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → π ∈ D.nd.Z i → NoChiOff i r Xs → Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π) ≤ Module.length (D.nd.O i) ↥(cocRho i r S Xs) + ∑ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) := by
  intro D i r ρ π Xs S hr hS hπ _ hchi
  classical
  have h52 := GlobalTheory.T.cutValue_mem_heckeValueIdealOffSupport D i r ρ π Xs S hr hS hπ
  have h54 := GlobalTheory.Cut.ResidualSelmer.main D i r ρ π Xs S hr hS hπ hchi
  obtain ⟨-, -, hcomp, hsurj, -, -, -, -, -, -, -, h51, -⟩ := hS
  have hinj : Function.Injective (algebraMap (D.nd.O i) (KK D.nd i)) := IsFractionRing.injective _ _
  let A : Subalgebra (D.nd.O i) (S.X' → MatN D.nd i) := spanAlg S.T' (fun x' => rO D.nd i r (S.p x'))
  obtain ⟨g, γ, hγ⟩ := exists_gens A (yg D.nd r S)
  have hY : ∀ m, InY D.nd r S m → ∃ θ : Fin g → A, m = ∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q) := by
    rintro _ ⟨m, a, s, ha, rfl⟩
    exact hγ m a s ha
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := exists_conj S.e
  have hbl := fun a (ha : a ∈ A) => hconj _ _ _ (hcomp a ha)
  obtain ⟨⟨fρ, hfρ⟩, hχ⟩ := exists_homs hinj A S.π' P Q hPQ hQP S.ψρ S.ψχ hbl
  choose fχ hfχ using hχ
  let Rel : Submodule A (Fin g → A) :=
    { carrier := {θ | ∀ x', S.p x' ∈ Xs → (∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q)) x' = 0}
      add_mem' := fun {a b} ha hb x' hx => by
        have := congrArg₂ (· + ·) (ha x' hx) (hb x' hx)
        simpa [add_mul, Finset.sum_add_distrib] using this
      zero_mem' := fun x' _ => by simp
      smul_mem' := fun c θ hθ x' hx => by
        have := congrArg (fun z => (c : S.X' → MatN D.nd i) x' * z) (hθ x' hx)
        simpa [Finset.sum_apply, Finset.mul_sum, mul_assoc] using this }
  let d : Option (Fin D.R.t) → ℕ := blockDim D.R.r
  let ψ := blockHom fρ fχ
  have hψχ : ∀ c (a : A), ψ (some c) a = S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    intro c a
    rw [← hfχ, ← Algebra.algebraMap_eq_smul_one]
    rfl
  have key := GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound (D.nd.O i) A (Option (Fin D.R.t)) d ψ (by
    rintro (_ | c) B
    · obtain ⟨a, ha, rfl⟩ := hsurj B
      exact ⟨⟨a, ha⟩, hfρ _⟩
    · change Matrix (Fin 1) (Fin 1) (D.nd.O i) at B
      refine ⟨algebraMap _ _ (B 0 0), ((ψ (some c)).commutes _).trans ?_⟩
      change algebraMap _ (Matrix (Fin 1) (Fin 1) (D.nd.O i)) _ = B
      ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp [Matrix.algebraMap_matrix_apply]) g Rel (ccOff i Xs π) (by
    intro n θ hθ m
    have hT := GlobalTheory.BlockDetPoly.main S.T' D.R.nV A h51 n g (fun k p q => θ k p q) (fun k p q => (θ k p q).2) m
    have h2 := h52 _ hT (by
      intro x' hx hz
      obtain ⟨η, s, hs⟩ := h54 x' hx hz
      rw [det_generic_eq_zero hinj (fun k p q => (θ k p q : S.X' → MatN D.nd i) x')
        (fun q => ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η) ?_ ?_, MvPolynomial.coeff_zero]
      · intro h0
        apply hs
        obtain ⟨t, ht⟩ := hγ 1 (fun _ => 1) (fun _ => s) (fun _ => A.one_mem)
        rw [Fin.sum_univ_one, one_mul] at ht
        rw [ht, Finset.sum_apply, ← RingHom.mapMatrix_apply, map_sum, Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [Pi.mul_apply, map_mul, ← Matrix.mulVec_mulVec, RingHom.mapMatrix_apply _ (yg D.nd r S (γ q) x'),
          show ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η = 0 from congrFun h0 q, Matrix.mulVec_zero]
      · intro k p
        have h3 := congrArg (fun z => ((toK D.nd i).mapMatrix z).mulVec η) (hθ k p x' hx)
        simp only [Finset.sum_apply, map_sum, Matrix.sum_mulVec, Pi.mul_apply, map_mul, map_zero,
          Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h3
        exact h3)
    rw [det_generic_blocks hinj P Q hPQ hQP (fun k p q => (θ k p q : S.X' → MatN D.nd i) S.π')
      (fun k p q => S.ψρ (θ k p q)) (fun c k p q => S.ψχ c (θ k p q))
      (fun k p q => hbl _ (θ k p q).2)] at h2
    rw [Fintype.prod_option]
    convert h2 using 3
    · congr 1
      ext1 pa qb
      simp only [Matrix.of_apply, ← hfρ]
      rfl
    · refine Finset.prod_congr rfl fun c _ => ?_
      refine (Matrix.det_submatrix_equiv_self (Equiv.prodUnique (Fin g) (Fin 1)).symm _).symm.trans ?_
      congr 1
      ext1 p q
      simp [hψχ])
  refine key.trans ?_
  rw [Fintype.sum_option]
  refine add_le_add ?_ (Finset.sum_le_sum fun c _ => ?_)
  · exact length_sol_le A fρ S.ψρ hfρ (yg D.nd r S) γ (InY D.nd r S) (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0)
      hY Rel (fun _ h => h) (fun _ _ => rfl)
  · exact length_sol_le A (ψ (some c)) _ (hψχ c) (yg D.nd r S) γ (InY D.nd r S)
      (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0) hY Rel (fun _ h => h) (fun _ _ => rfl)

end GlobalTheory.CutDet

end
end
