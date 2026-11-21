import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
import GroundTheory.HeightsAndTheta.Heights.ComplexProjective
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

structure ProjScheme (A : Type u) [CommRing A] (N : ℕ) where

  X : Scheme.{u}

  ι : X ⟶ projectiveSpace A N

  isClosedImmersion : IsClosedImmersion ι

attribute [instance] ProjScheme.isClosedImmersion

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

def self (A : Type u) [CommRing A] (N : ℕ) : ProjScheme A N where
  X := projectiveSpace A N
  ι := 𝟙 _
  isClosedImmersion := inferInstance

variable (X : ProjScheme A N)

def ideal : HomogeneousIdeal (ProjSpace.grading A N) :=
  ProjectiveSpectrum.vanishingIdeal (Set.range X.ι.base)

lemma isClosed_range : IsClosed (Set.range X.ι.base) :=
  X.ι.isClosedEmbedding.isClosed_range

def complexPoints (ρ : A →+* ℂ) : Set (CP N) :=
  {v | projPoint ρ v ∈ Set.range X.ι.base}

lemma le_of_homogeneous (I : HomogeneousIdeal (ProjSpace.grading A N)) (x : projectiveSpace A N)
    (h : ∀ d, ∀ f ∈ ProjSpace.grading A N d, f ∈ I → f ∈ x.asHomogeneousIdeal) :
    (I : Set (MvPolynomial (Fin (N + 1)) A)) ⊆ x.asHomogeneousIdeal := by
  classical
  intro f hf
  rw [← DirectSum.sum_support_decompose (ProjSpace.grading A N) f]
  refine Ideal.sum_mem _ fun d _ => ?_
  exact h d _ (SetLike.coe_mem _) (I.isHomogeneous d hf)

theorem mem_complexPoints_iff (ρ : A →+* ℂ) (v : CP N) :
    v ∈ X.complexPoints ρ ↔ ∀ d, ∀ f ∈ ProjSpace.grading A N d, f ∈ X.ideal →
      f ∈ (projPoint ρ v).asHomogeneousIdeal := by
  have e : (Set.range X.ι.base : Set (ProjectiveSpectrum (ProjSpace.grading A N))) =
      ProjectiveSpectrum.zeroLocus _ (X.ideal : Set (MvPolynomial (Fin (N + 1)) A)) := by
    rw [ideal, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact X.isClosed_range.closure_eq.symm
  change projPoint ρ v ∈ (Set.range X.ι.base : Set (ProjectiveSpectrum (ProjSpace.grading A N))) ↔ _
  rw [e]
  change (X.ideal : Set (MvPolynomial (Fin (N + 1)) A)) ⊆ (projPoint ρ v).asHomogeneousIdeal ↔ _
  constructor
  · intro h d f _ hf
    exact h hf
  · intro h
    exact le_of_homogeneous _ _ h


theorem isClosed_complexPoints (ρ : A →+* ℂ) : IsClosed (X.complexPoints ρ) := by
  have : X.complexPoints ρ = ⋂ d, ⋂ f ∈ {f | f ∈ ProjSpace.grading A N d ∧ f ∈ X.ideal},
      {v : CP N | f ∈ (projPoint ρ v).asHomogeneousIdeal} := by
    ext v
    simp only [mem_complexPoints_iff, Set.mem_iInter, Set.mem_ofPred_eq, and_imp]
  rw [this]
  exact isClosed_iInter fun d => isClosed_biInter fun f hf => isClosed_setOf_mem_projPoint ρ hf.1

theorem isCompact_complexPoints (ρ : A →+* ℂ) : IsCompact (X.complexPoints ρ) :=
  (X.isClosed_complexPoints ρ).isCompact

instance (ρ : A →+* ℂ) : CompactSpace (X.complexPoints ρ) :=
  isCompact_iff_compactSpace.mp (X.isCompact_complexPoints ρ)

lemma conj_mem_complexPoints {ρ : A →+* ℂ} {v : CP N} (hv : v ∈ X.complexPoints ρ) :
    CP.conj v ∈ X.complexPoints ((starRingEnd ℂ).comp ρ) := by
  change projPoint ((starRingEnd ℂ).comp ρ) (CP.conj v) ∈ Set.range X.ι.base
  rw [projPoint_conj]
  exact hv

def conjPoint (ρ : A →+* ℂ) (x : X.complexPoints ρ) :
    X.complexPoints ((starRingEnd ℂ).comp ρ) :=
  ⟨CP.conj x.1, X.conj_mem_complexPoints x.2⟩



theorem complexPoints_self (ρ : A →+* ℂ) : (self A N).complexPoints ρ = Set.univ := by
  ext v
  simp only [complexPoints, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨projPoint ρ v, rfl⟩

end ProjScheme

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization NumberField

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable (A : Type u) [CommRing A] (N : ℕ)

def baseEval : MvPolynomial (Fin (N + 1)) A →+* Γ(Spec (.of A), ⊤) :=
  (Scheme.ΓSpecIso (.of A)).inv.hom.comp (MvPolynomial.eval (Pi.single 0 1))

lemma X_zero_mem_irrelevant :
    (MvPolynomial.X 0 : MvPolynomial (Fin (N + 1)) A) ∈ HomogeneousIdeal.irrelevant (ProjSpace.grading A N) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem 0) one_ne_zero]

lemma baseEval_irrelevant :
    (HomogeneousIdeal.irrelevant (ProjSpace.grading A N)).toIdeal.map (baseEval A N) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have : baseEval A N (MvPolynomial.X 0) = 1 := by simp [baseEval]
  rw [← this]
  exact Ideal.mem_map_of_mem _ (X_zero_mem_irrelevant A N)

def baseSection : Spec (.of A) ⟶ projectiveSpace A N :=
  Proj.fromOfGlobalSections (ProjSpace.grading A N) (baseEval A N) (baseEval_irrelevant A N)

lemma baseSection_toSpecBase : baseSection A N ≫ ProjSpace.toSpecBase A N = 𝟙 _ := by
  rw [ProjSpace.toSpecBase, ← Category.assoc, baseSection, Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom (algebraMap A (ProjSpace.grading A N 0)) ≫
      CommRingCat.ofHom ((baseEval A N).comp (algebraMap _ _)) = (Scheme.ΓSpecIso (.of A)).inv := by
    ext a
    change (Scheme.ΓSpecIso (.of A)).inv.hom (MvPolynomial.eval (Pi.single 0 1)
      (MvPolynomial.C a)) = (Scheme.ΓSpecIso (.of A)).inv.hom a
    rw [MvPolynomial.eval_C]
  rw [this, toSpecΓ_SpecMap_ΓSpecIso_inv]

instance : IsClosedImmersion (baseSection A N) := by
  have : IsClosedImmersion (baseSection A N ≫ ProjSpace.toSpecBase A N) := by
    rw [baseSection_toSpecBase]; infer_instance
  exact IsClosedImmersion.of_comp _ (ProjSpace.toSpecBase A N)

def base : ProjScheme A N where
  X := Spec (.of A)
  ι := baseSection A N
  isClosedImmersion := inferInstance

variable {A N}

lemma mem_baseSection_of_pos (p : Spec (.of A)) {f : MvPolynomial (Fin (N + 1)) A} {n : ℕ}
    (hn : 0 < n) (hf : f ∈ ProjSpace.grading A N n) :
    f ∈ ((baseSection A N).base p).asHomogeneousIdeal ↔
      MvPolynomial.eval (Pi.single 0 1) f ∈ p.asIdeal := by
  have h := Proj.fromOfGlobalSections_preimage_basicOpen (ProjSpace.grading A N) (baseEval A N)
    (baseEval_irrelevant A N) hn hf
  have h' : p ∈ (baseSection A N) ⁻¹ᵁ Proj.basicOpen (ProjSpace.grading A N) f ↔
      p ∈ (Spec (.of A)).basicOpen (baseEval A N f) := by
    rw [baseSection, h]
  rw [baseEval, RingHom.comp_apply, basicOpen_eq_of_affine] at h'
  rw [← not_iff_not]
  exact h'

lemma mem_baseSection (p : Spec (.of A)) {f : MvPolynomial (Fin (N + 1)) A} {n : ℕ}
    (hf : f ∈ ProjSpace.grading A N n) :
    f ∈ ((baseSection A N).base p).asHomogeneousIdeal ↔
      MvPolynomial.eval (Pi.single 0 1) f ∈ p.asIdeal := by
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin (N + 1)) A) ∉ ((baseSection A N).base p).asHomogeneousIdeal := by
    rw [mem_baseSection_of_pos p Nat.one_pos (ProjSpace.X_mem 0), eval_X, Pi.single_eq_same]
    exact (Ideal.ne_top_iff_one _).1 p.isPrime.ne_top
  have hX := mem_baseSection_of_pos p (by omega : 0 < 1 + n)
    (SetLike.mul_mem_graded (ProjSpace.X_mem 0) hf)
  rw [map_mul, eval_X, Pi.single_eq_same, one_mul] at hX
  have hp := ((baseSection A N).base p).isPrime
  constructor
  · intro h
    exact hX.1 (((baseSection A N).base p).asHomogeneousIdeal.toIdeal.mul_mem_left _ h)
  · intro h
    exact (hp.mem_or_mem (hX.2 h)).resolve_left h0

theorem complexPoints_base (ρ : A →+* ℂ) :
    (base A N).complexPoints ρ =
      {Projectivization.mk ℂ (Pi.single 0 1) (by simp [funext_iff, Pi.single_apply])} := by
  have hval : ∀ f : MvPolynomial (Fin (N + 1)) A,
      evalAt ρ (Pi.single 0 1) f = ρ (MvPolynomial.eval (Pi.single 0 1) f) := by
    intro f
    rw [evalAt, MvPolynomial.eval, coe_eval₂Hom, eval₂_comp_left]
    congr 1
    funext j
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  ext v
  induction v using Projectivization.ind with
  | h w hw =>
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, hp⟩
      have hzero : ∀ j, j ≠ 0 → w j = 0 := by
        intro j hj
        have h1 : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ∈ ((baseSection A N).base p).asHomogeneousIdeal := by
          rw [mem_baseSection p (ProjSpace.X_mem j), eval_X, Pi.single_eq_of_ne hj]
          exact zero_mem _
        change (baseSection A N).base p = _ at hp
        rw [hp, mem_projPoint ρ w hw (ProjSpace.X_mem j)] at h1
        simpa using h1
      have h0 : w 0 ≠ 0 := by
        intro h
        exact hw (funext fun j => by by_cases hj : j = 0 <;> simp_all)
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 (w 0) h0, ?_⟩
      funext j
      by_cases hj : j = 0
      · subst hj; simp
      · simp [hzero j hj, hj]
    · intro hv
      rw [hv]
      let p : Spec (.of A) := (⟨RingHom.ker ρ, RingHom.ker_isPrime ρ⟩ : PrimeSpectrum A)
      refine ⟨p, ?_⟩
      refine projPoint_ext fun d f hf => ?_
      change f ∈ ((baseSection A N).base p).asHomogeneousIdeal ↔ _
      rw [mem_baseSection _ hf, mem_projPoint ρ _ _ hf, hval]
      exact RingHom.mem_ker

end ProjScheme

variable {N : ℕ} (K : Type) [Field K]

def complexPointsAt (X : ProjScheme (𝓞 K) N) (σ : K →+* ℂ) : Set (CP N) :=
  X.complexPoints (σ.comp (algebraMap (𝓞 K) K))

variable {K}

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

variable {A : Type u} [CommRing A] {N : ℕ}

def IsOver (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (x : ProjectiveSpectrum (ProjSpace.grading A N)) :
    Prop :=
  ∀ d, ∀ f ∈ ProjSpace.grading A N d, f ∈ x.asHomogeneousIdeal ↔ evalAt ρ w f = 0

lemma isOver_projPoint (ρ : A →+* ℂ) (v : CP N) : IsOver ρ v.rep (projPoint ρ v) :=
  fun _ _ hf => mem_projPointOf ρ _ hf

lemma IsOver.smul {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : ProjectiveSpectrum (ProjSpace.grading A N)}
    (h : IsOver ρ w x) {c : ℂ} (hc : c ≠ 0) : IsOver ρ (c • w) x := by
  intro d f hf
  rw [h d f hf, evalAt_smul ρ hf, mul_eq_zero, or_iff_right (pow_ne_zero _ hc)]

lemma IsOver.conj {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : ProjectiveSpectrum (ProjSpace.grading A N)}
    (h : IsOver ρ w x) : IsOver ((starRingEnd ℂ).comp ρ) (CP.conjVec w) x := by
  intro d f hf
  rw [h d f hf, evalAt_conj, map_eq_zero]

def evalLine (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) : MvPolynomial (Fin (N + 1)) A →+* Polynomial ℂ :=
  eval₂Hom (Polynomial.C.comp ρ) (fun k => Polynomial.C (w k) * Polynomial.X)

lemma evalLine_of_isHomogeneous (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ)
    {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ} (hf : f.IsHomogeneous d) :
    evalLine ρ w f = Polynomial.C (evalAt ρ w f) * Polynomial.X ^ d := by
  rw [evalLine, coe_eval₂Hom, eval₂_eq', evalAt, eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ k, m k = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [RingHom.comp_apply, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd,
    map_mul, map_prod, map_pow]
  ring

lemma coeff_evalLine (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (f : MvPolynomial (Fin (N + 1)) A)
    (d : ℕ) : (evalLine ρ w f).coeff d = evalAt ρ w (homogeneousComponent d f) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [evalLine_of_isHomogeneous ρ w (homogeneousComponent_isHomogeneous _ _),
    Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [homogeneousComponent_eq_zero _ _ (Nat.lt_of_succ_le h)]
    simp

lemma evalLine_ne_zero {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : ProjectiveSpectrum (ProjSpace.grading A N)}
    (h : IsOver ρ w x) {f : MvPolynomial (Fin (N + 1)) A} (hf : f ∉ x.asHomogeneousIdeal) :
    evalLine ρ w f ≠ 0 := by
  intro h0
  apply hf
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ => ?_
  refine (h d _ (homogeneousComponent_isHomogeneous d f)).2 ?_
  rw [← coeff_evalLine, h0, Polynomial.coeff_zero]

variable {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : ProjectiveSpectrum (ProjSpace.grading A N)}

def locToRatFunc (h : IsOver ρ w x) :
    Localization.AtPrime x.asHomogeneousIdeal.toIdeal →+* RatFunc ℂ :=
  IsLocalization.lift (M := x.asHomogeneousIdeal.toIdeal.primeCompl)
    (g := (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp (evalLine ρ w)) fun y => by
      rw [isUnit_iff_ne_zero, RingHom.comp_apply, ne_eq,
        map_eq_zero_iff _ (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))]
      exact evalLine_ne_zero h y.2

def atPrimeToRatFunc (h : IsOver ρ w x) :
    HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal →+*
      RatFunc ℂ :=
  (locToRatFunc h).comp (algebraMap _ _)

lemma atPrimeToRatFunc_mk (h : IsOver ρ w x)
    (c : HomogeneousLocalization.NumDenSameDeg (ProjSpace.grading A N)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    atPrimeToRatFunc h (HomogeneousLocalization.mk c) =
      algebraMap ℂ (RatFunc ℂ) (evalAt ρ w c.num / evalAt ρ w c.den) := by
  have hden : evalAt ρ w (c.den : MvPolynomial (Fin (N + 1)) A) ≠ 0 := fun h0 =>
    c.den_mem ((h _ _ c.den.2).2 h0)
  rw [atPrimeToRatFunc, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', locToRatFunc,
    IsLocalization.lift_mk'_spec]
  simp only [RingHom.comp_apply]
  rw [evalLine_of_isHomogeneous ρ w (c.num.2), evalLine_of_isHomogeneous ρ w (c.den.2),
    IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ), ← map_mul]
  congr 1
  rw [Polynomial.algebraMap_eq, mul_comm (Polynomial.C (evalAt ρ w c.den) * _), ← mul_assoc,
    ← Polynomial.C_mul, div_mul_cancel₀ _ hden]

lemma atPrimeToRatFunc_mem_range (h : IsOver ρ w x)
    (y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal) :
    atPrimeToRatFunc h y ∈ (algebraMap ℂ (RatFunc ℂ)).range := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
  rw [atPrimeToRatFunc_mk]
  exact ⟨_, rfl⟩

def constEquiv : (algebraMap ℂ (RatFunc ℂ)).range ≃+* ℂ :=
  (RingEquiv.ofBijective (algebraMap ℂ (RatFunc ℂ)).rangeRestrict
    ⟨fun _ _ hab => (algebraMap ℂ (RatFunc ℂ)).injective (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩).symm

def evalAtPrime (h : IsOver ρ w x) :
    HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal →+* ℂ :=
  constEquiv.toRingHom.comp ((atPrimeToRatFunc h).codRestrict _ (atPrimeToRatFunc_mem_range h))

lemma algebraMap_evalAtPrime (h : IsOver ρ w x)
    (y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal) :
    algebraMap ℂ (RatFunc ℂ) (evalAtPrime h y) = atPrimeToRatFunc h y := by
  obtain ⟨c, hc⟩ := atPrimeToRatFunc_mem_range h y
  have : evalAtPrime h y = c := by
    rw [evalAtPrime, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      constEquiv, RingEquiv.symm_apply_eq]
    exact Subtype.ext hc.symm
  rw [this, hc]

theorem evalAtPrime_mk (h : IsOver ρ w x)
    (c : HomogeneousLocalization.NumDenSameDeg (ProjSpace.grading A N)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    evalAtPrime h (HomogeneousLocalization.mk c) = evalAt ρ w c.num / evalAt ρ w c.den := by
  apply (algebraMap ℂ (RatFunc ℂ)).injective
  rw [algebraMap_evalAtPrime, atPrimeToRatFunc_mk]

theorem isUnit_of_evalAtPrime_ne_zero (h : IsOver ρ w x)
    {y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal}
    (hy : evalAtPrime h y ≠ 0) : IsUnit y := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
  rw [evalAtPrime_mk, div_ne_zero_iff] at hy
  have hnum : (c.num : MvPolynomial (Fin (N + 1)) A) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
    fun hm => hy.1 ((h _ _ c.num.2).1 hm)
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk']
  refine isUnit_of_mul_isUnit_left (y := algebraMap (MvPolynomial (Fin (N + 1)) A)
    (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (c.den : MvPolynomial (Fin (N + 1)) A)) ?_
  rw [IsLocalization.mk'_spec]
  exact IsLocalization.map_units _ ⟨_, hnum⟩

def evalStalkProj (h : IsOver ρ w x) : (projectiveSpace A N).presheaf.stalk x →+* ℂ :=
  (evalAtPrime h).comp (Proj.stalkIso (ProjSpace.grading A N) x).hom.hom

theorem isUnit_of_evalStalkProj_ne_zero (h : IsOver ρ w x)
    {y : (projectiveSpace A N).presheaf.stalk x} (hy : evalStalkProj h y ≠ 0) : IsUnit y := by
  have hu := isUnit_of_evalAtPrime_ne_zero h hy
  exact (isUnit_map_iff (Proj.stalkIso (ProjSpace.grading A N) x).commRingCatIsoToRingEquiv y).1 hu

lemma evalAtPrime_smul (h : IsOver ρ w x) {c : ℂ} (hc : c ≠ 0)
    (y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal) :
    evalAtPrime (h.smul hc) y = evalAtPrime h y := by
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective y
  rw [evalAtPrime_mk, evalAtPrime_mk, evalAt_smul ρ ((mem_homogeneousSubmodule _ _).1 z.num.2),
    evalAt_smul ρ ((mem_homogeneousSubmodule _ _).1 z.den.2),
    mul_div_mul_left _ _ (pow_ne_zero _ hc)]

lemma evalAtPrime_conj (h : IsOver ρ w x)
    (y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal) :
    evalAtPrime h.conj y = starRingEnd ℂ (evalAtPrime h y) := by
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective y
  rw [evalAtPrime_mk, evalAtPrime_mk, evalAt_conj, evalAt_conj, map_div₀]

lemma evalStalkProj_smul (h : IsOver ρ w x) {c : ℂ} (hc : c ≠ 0)
    (y : (projectiveSpace A N).presheaf.stalk x) :
    evalStalkProj (h.smul hc) y = evalStalkProj h y :=
  evalAtPrime_smul h hc _

lemma evalStalkProj_conj (h : IsOver ρ w x) (y : (projectiveSpace A N).presheaf.stalk x) :
    evalStalkProj h.conj y = starRingEnd ℂ (evalStalkProj h y) :=
  evalAtPrime_conj h _

namespace ProjScheme

variable (X : ProjScheme A N)

def evalStalk {p : X.X} (h : IsOver ρ w (X.ι.base p)) : X.X.presheaf.stalk p →+* ℂ :=
  RingHom.liftOfSurjective (X.ι.stalkMap p).hom (X.ι.stalkMap_surjective p)
    ⟨evalStalkProj h, fun y hy => by
      rw [RingHom.mem_ker] at hy ⊢
      by_contra hne
      have hu := (isUnit_of_evalStalkProj_ne_zero h hne).map (X.ι.stalkMap p).hom
      rw [hy, isUnit_zero_iff] at hu
      exact zero_ne_one hu⟩

theorem evalStalk_stalkMap {p : X.X} (h : IsOver ρ w (X.ι.base p))
    (y : (projectiveSpace A N).presheaf.stalk (X.ι.base p)) :
    X.evalStalk h ((X.ι.stalkMap p).hom y) = evalStalkProj h y :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem evalStalk_smul {p : X.X} (h : IsOver ρ w (X.ι.base p)) {c : ℂ} (hc : c ≠ 0) :
    X.evalStalk (h.smul hc) = X.evalStalk h := by
  ext y
  obtain ⟨z, rfl⟩ := X.ι.stalkMap_surjective p y
  rw [evalStalk_stalkMap, evalStalk_stalkMap]
  exact evalStalkProj_smul h hc z

theorem evalStalk_conj {p : X.X} (h : IsOver ρ w (X.ι.base p)) :
    X.evalStalk h.conj = (starRingEnd ℂ).comp (X.evalStalk h) := by
  ext y
  obtain ⟨z, rfl⟩ := X.ι.stalkMap_surjective p y
  rw [evalStalk_stalkMap, RingHom.comp_apply, evalStalk_stalkMap]
  exact evalStalkProj_conj h z

end ProjScheme

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

def Via {R : Type*} [CommRing R] (_φ : R →+* ℂ) : Type := ℂ

namespace Via

variable {R : Type*} [CommRing R] (φ : R →+* ℂ)

instance : Field (Via φ) := inferInstanceAs (Field ℂ)

instance : Algebra R (Via φ) := φ.toAlgebra

def ofComplex : ℂ ≃+* Via φ := RingEquiv.refl ℂ

lemma algebraMap_apply (r : R) : algebraMap R (Via φ) r = ofComplex φ (φ r) := rfl

def conj : Via φ →ₗ[R] Via ((starRingEnd ℂ).comp φ) where
  toFun z := starRingEnd ℂ (show ℂ from z)
  map_add' a b := map_add (starRingEnd ℂ) (show ℂ from a) (show ℂ from b)
  map_smul' r z := by
    change starRingEnd ℂ (φ r * (show ℂ from z)) = (starRingEnd ℂ) (φ r) * starRingEnd ℂ (show ℂ from z)
    rw [map_mul]

def conjInv : Via ((starRingEnd ℂ).comp φ) →ₗ[R] Via φ where
  toFun z := starRingEnd ℂ (show ℂ from z)
  map_add' a b := map_add (starRingEnd ℂ) (show ℂ from a) (show ℂ from b)
  map_smul' r z := by
    change starRingEnd ℂ (starRingEnd ℂ (φ r) * (show ℂ from z)) =
      φ r * starRingEnd ℂ (show ℂ from z)
    rw [map_mul, Complex.conj_conj]

lemma conjInv_conj (z : Via φ) : conjInv φ (conj φ z) = z := Complex.conj_conj (show ℂ from z)

lemma conj_conjInv (z : Via ((starRingEnd ℂ).comp φ)) : conj φ (conjInv φ z) = z :=
  Complex.conj_conj (show ℂ from z)

end Via

variable {X : Scheme.{u}} (L : X.Modules)

variable (X) in

abbrev locRing (p : X) : CommRingCat.{u} := TopCat.Presheaf.stalk (X := X.toTopCat) X.sheaf.obj p

abbrev modStalk (p : X) : Type u :=
  TopCat.Presheaf.stalk (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf p

def fibreAt (p : X) (φ : locRing X p →+* ℂ) : Type u :=
  TensorProduct (locRing X p) (Via φ) (modStalk L p)

variable {L}

def germM {U : X.Opens} {p : X} (hp : p ∈ U) (s : ((preMod X).obj L).obj (op U)) :
    modStalk L p :=
  TopCat.Presheaf.germ (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf U p hp s

def germR {U : X.Opens} {p : X} (hp : p ∈ U) (r : ringOn X U) : locRing X p :=
  TopCat.Presheaf.germ (X := X.toTopCat) X.sheaf.obj U p hp r

lemma germM_smul {U : X.Opens} {p : X} (hp : p ∈ U) (r : ringOn X U)
    (s : ((preMod X).obj L).obj (op U)) : germM hp (r • s) = germR hp r • germM hp s :=
  PresheafOfModules.germ_smul _ _ _ _ _ _

lemma germM_resM {U V : X.Opens} (hVU : V ≤ U) {p : X} (hp : p ∈ V)
    (s : ((preMod X).obj L).obj (op U)) : germM hp (resM _ hVU s) = germM (hVU hp) s :=
  TopCat.Presheaf.germ_res_apply (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf
    (homOfLE hVU) p hp s

lemma germR_resR {U V : X.Opens} (hVU : V ≤ U) {p : X} (hp : p ∈ V) (r : ringOn X U) :
    germR hp (resR hVU r) = germR (hVU hp) r :=
  TopCat.Presheaf.germ_res_apply (X := X.toTopCat) X.sheaf.obj (homOfLE hVU) p hp r

lemma germM_zero {U : X.Opens} {p : X} (hp : p ∈ U) :
    germM (L := L) hp (0 : ((preMod X).obj L).obj (op U)) = 0 :=
  map_zero _

theorem bijective_smul_germ {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) :
    Function.Bijective (fun r : locRing X p => r • germM hp e) := by
  have key : ∀ r : locRing X p, r • germM hp e = 0 → r = 0 := by
    intro r hr
    obtain ⟨V, hVU, hpV, r', rfl⟩ :=
      TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat) X.sheaf.obj r hp
    change germR hpV r' • germM hp e = 0 at hr
    rw [← germM_resM hVU hpV, ← germM_smul] at hr
    obtain ⟨W, hpW, iV, iV', hW⟩ := TopCat.Presheaf.germ_eq (X := X.toTopCat) (C := Ab.{u})
      ((preMod X).obj L).presheaf p hpV hpV _ 0 (hr.trans (germM_zero hpV).symm)
    have h0 : resR iV.le r' • resM _ (iV.le.trans hVU) e = 0 := by
      rw [← resM_smul_res]
      exact hW.trans (map_zero _)
    have hz : resR iV.le r' = 0 :=
      (he W (iV.le.trans hVU)).1 (a₁ := resR iV.le r') (a₂ := 0) (by
        simp only [zero_smul]; exact h0)
    change germR hpV r' = 0
    rw [← germR_resR iV.le hpW, hz]
    exact map_zero _
  constructor
  · intro r₁ r₂ h
    have := key (r₁ - r₂) (by simp only at h; rw [sub_smul, h, sub_self])
    exact sub_eq_zero.mp this
  · intro m
    obtain ⟨V, hVU, hpV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat)
      (C := Ab.{u}) ((preMod X).obj L).presheaf m hp
    obtain ⟨r, hr⟩ := (he V hVU).2 t
    refine ⟨germR hpV r, ?_⟩
    change germR hpV r • germM hp e = germM hpV t
    rw [← hr, germM_smul, germM_resM]

def stalkEquiv {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : locRing X p ≃ₗ[locRing X p] modStalk L p :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (germM hp e)) (bijective_smul_germ hp he)

lemma stalkEquiv_apply {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) (r : locRing X p) :
    stalkEquiv hp he r = r • germM hp e := rfl

section Fibre

variable {p : X} {φ : locRing X p →+* ℂ}

instance : AddCommGroup (fibreAt L p φ) :=
  inferInstanceAs (AddCommGroup (TensorProduct (locRing X p) (Via φ) (modStalk L p)))

instance : Module (Via φ) (fibreAt L p φ) :=
  inferInstanceAs (Module (Via φ) (TensorProduct (locRing X p) (Via φ) (modStalk L p)))

instance : Module ℂ (fibreAt L p φ) :=
  Module.compHom (fibreAt L p φ) (Via.ofComplex φ).toRingHom

lemma complex_smul_def (c : ℂ) (s : fibreAt L p φ) : c • s = Via.ofComplex φ c • s := rfl

variable (L φ) in

def fibreMk (c : Via φ) (m : modStalk L p) : fibreAt L p φ :=
  (c ⊗ₜ[locRing X p] m : TensorProduct (locRing X p) (Via φ) (modStalk L p))

variable (φ) in

def value {U : X.Opens} (hp : p ∈ U) (s : ((preMod X).obj L).obj (op U)) : fibreAt L p φ :=
  fibreMk L φ 1 (germM hp s)

variable (φ) in

def fibreEquiv {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreAt L p φ ≃ₗ[Via φ] Via φ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Via φ) (Via φ))
    (stalkEquiv hp he).symm).trans
      (TensorProduct.AlgebraTensorModule.rid (locRing X p) (Via φ) (Via φ))

lemma fibreEquiv_fibreMk {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) (c : Via φ) (r : locRing X p) :
    fibreEquiv φ hp he (fibreMk L φ c (r • germM hp e)) = Via.ofComplex φ (φ r) * c := by
  have : (stalkEquiv hp he).symm (r • germM hp e) = r := by
    rw [LinearEquiv.symm_apply_eq, stalkEquiv_apply]
  change TensorProduct.AlgebraTensorModule.rid (locRing X p) (Via φ) (Via φ) (c ⊗ₜ (stalkEquiv hp he).symm
    (r • germM hp e)) = _
  rw [this, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
  rfl

lemma fibreEquiv_value {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreEquiv φ hp he (value φ hp e) = 1 := by
  have := fibreEquiv_fibreMk (φ := φ) hp he 1 1
  rw [one_smul, map_one, mul_one] at this
  exact this

variable (φ) in

def fibreEquivComplex {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreAt L p φ ≃ₗ[ℂ] ℂ where
  toFun s := (Via.ofComplex φ).symm (fibreEquiv φ hp he s)
  invFun c := (fibreEquiv φ hp he).symm (Via.ofComplex φ c)
  map_add' a b := by rw [map_add, map_add]
  map_smul' c s := by
    rw [complex_smul_def, LinearEquiv.map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    rfl
  left_inv s := by simp
  right_inv c := by simp

lemma value_ne_zero {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : value φ hp e ≠ 0 := by
  intro h
  have := fibreEquiv_value (φ := φ) hp he
  rw [h, map_zero] at this
  exact zero_ne_one this

variable (φ) in

def fibreConj : fibreAt L p φ ≃+ fibreAt L p ((starRingEnd ℂ).comp φ) where
  toFun s := TensorProduct.map (Via.conj φ) LinearMap.id
    (show TensorProduct (locRing X p) (Via φ) (modStalk L p) from s)
  invFun s := TensorProduct.map (Via.conjInv φ) LinearMap.id
    (show TensorProduct (locRing X p) (Via ((starRingEnd ℂ).comp φ)) (modStalk L p) from s)
  left_inv s := by
    change TensorProduct.map (Via.conjInv φ) LinearMap.id
      (TensorProduct.map (Via.conj φ) LinearMap.id
        (show TensorProduct (locRing X p) (Via φ) (modStalk L p) from s)) = s
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have : (Via.conjInv φ).comp (Via.conj φ) = LinearMap.id := LinearMap.ext (Via.conjInv_conj φ)
    rw [this, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  right_inv s := by
    change TensorProduct.map (Via.conj φ) LinearMap.id
      (TensorProduct.map (Via.conjInv φ) LinearMap.id
        (show TensorProduct (locRing X p) (Via ((starRingEnd ℂ).comp φ)) (modStalk L p) from s)) = s
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have : (Via.conj φ).comp (Via.conjInv φ) = LinearMap.id := LinearMap.ext (Via.conj_conjInv φ)
    rw [this, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  map_add' a b := map_add _ _ _

end Fibre

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ} (X : ProjScheme A N) {ρ : A →+* ℂ}

def point (x : X.complexPoints ρ) : X.X := Classical.choose x.2

lemma ι_point (x : X.complexPoints ρ) : X.ι.base (X.point x) = projPoint ρ x.1 :=
  Classical.choose_spec x.2

lemma isOver_point (x : X.complexPoints ρ) : IsOver ρ x.1.rep (X.ι.base (X.point x)) :=
  (X.ι_point x) ▸ isOver_projPoint ρ x.1

lemma ι_injective : Function.Injective X.ι.base := X.ι.isClosedEmbedding.injective

def evalAtPoint (x : X.complexPoints ρ) : locRing X.X (X.point x) →+* ℂ :=
  X.evalStalk (X.isOver_point x)

abbrev Fibre (L : X.X.Modules) (x : X.complexPoints ρ) : Type u :=
  fibreAt L (X.point x) (X.evalAtPoint x)

def sectionValue {L : X.X.Modules} (x : X.complexPoints ρ) {U : X.X.Opens} (hx : X.point x ∈ U)
    (s : ((preMod X.X).obj L).obj (op U)) : X.Fibre L x :=
  value _ hx s

lemma point_conjPoint (x : X.complexPoints ρ) : X.point (X.conjPoint ρ x) = X.point x := by
  apply X.ι_injective
  rw [ι_point, ι_point]
  exact projPoint_conj ρ x.1

lemma exists_rep_conj (v : CP N) : ∃ c : ℂˣ, (CP.conj v).rep = (c : ℂ) • CP.conjVec v.rep := by
  have h : Projectivization.mk ℂ (CP.conj v).rep (CP.conj v).rep_nonzero =
      Projectivization.mk ℂ (CP.conjVec v.rep) (CP.conjVec_ne_zero v.rep_nonzero) := by
    rw [Projectivization.mk_rep, ← CP.conj_mk v.rep v.rep_nonzero, Projectivization.mk_rep]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (CP.conj v).rep_nonzero
    (CP.conjVec_ne_zero v.rep_nonzero)).1 h
  exact ⟨c, hc.symm⟩

lemma evalStalk_eq_conj {p : X.X} {w w' : Fin (N + 1) → ℂ} (c : ℂˣ)
    (hw : w' = (c : ℂ) • CP.conjVec w) (h : IsOver ρ w (X.ι.base p))
    (h' : IsOver ((starRingEnd ℂ).comp ρ) w' (X.ι.base p)) :
    X.evalStalk h' = (starRingEnd ℂ).comp (X.evalStalk h) := by
  subst hw
  have : X.evalStalk h' = X.evalStalk (h.conj.smul c.ne_zero) := rfl
  rw [this, X.evalStalk_smul h.conj c.ne_zero, X.evalStalk_conj h]

lemma evalAtPoint_conjPoint_germ (x : X.complexPoints ρ) {U : X.X.Opens} (hx : X.point x ∈ U)
    (hx' : X.point (X.conjPoint ρ x) ∈ U) (f : ringOn X.X U) :
    X.evalAtPoint (X.conjPoint ρ x) (germR hx' f) = starRingEnd ℂ (X.evalAtPoint x (germR hx f)) := by
  obtain ⟨c, hc⟩ := exists_rep_conj x.1
  have key : ∀ (q : X.X) (e : q = X.point x)
      (h' : IsOver ((starRingEnd ℂ).comp ρ) (CP.conj x.1).rep (X.ι.base q)) (hq : q ∈ U),
      X.evalStalk h' (germR hq f) = starRingEnd ℂ (X.evalAtPoint x (germR hx f)) := by
    intro q e h' hq
    subst e
    rw [X.evalStalk_eq_conj c hc (X.isOver_point x) h']
    rfl
  exact key _ (X.point_conjPoint x) (X.isOver_point _) hx'

end ProjScheme

end

end GroundTheory.Heights₂.Heights
end
