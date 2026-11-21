import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat

section
namespace GlobalTheory

namespace ScalarSnakeLength

variable {A : Type} [CommRing A]

lemma length_eq_ker_add_range {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (φ : M →ₗ[A] P) :
    Module.length A M =
      Module.length A (LinearMap.ker φ) + Module.length A (LinearMap.range φ) :=
  Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    Subtype.val_injective φ.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))

lemma length_mid {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (h : Function.Exact f g) :
    Module.length A N₂ =
      Module.length A (LinearMap.range f) + Module.length A (LinearMap.range g) := by
  rw [length_eq_ker_add_range g, LinearMap.exact_iff.mp h]

lemma length_of_injective {N₁ N₂ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (f : N₁ →ₗ[A] N₂) (hf : Function.Injective f) :
    Module.length A N₁ = Module.length A (LinearMap.range f) :=
  (LinearEquiv.ofInjective f hf).length_eq

lemma length_of_surjective {N₁ N₂ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (g : N₁ →ₗ[A] N₂) (hg : Function.Surjective g) :
    Module.length A (LinearMap.range g) = Module.length A N₂ := by
  rw [LinearMap.range_eq_top.mpr hg, Module.length_top]

variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]

def kerMap (f : M₁ →ₗ[A] M₂) (b : A) :
    LinearMap.ker (LinearMap.lsmul A M₁ b) →ₗ[A] LinearMap.ker (LinearMap.lsmul A M₂ b) :=
  f.restrict (fun x hx => by
    simp only [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [← map_smul, hx, map_zero])

def quotMap (f : M₁ →ₗ[A] M₂) (b : A) :
    (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) →ₗ[A]
      (M₂ ⧸ LinearMap.range (LinearMap.lsmul A M₂ b)) :=
  Submodule.mapQ _ _ f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp⟩)

end ScalarSnakeLength

end GlobalTheory

namespace GlobalTheory

namespace ScalarSnakeLength

variable {A : Type} [CommRing A]
variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]

lemma kerMap_injective (f : M₁ →ₗ[A] M₂) (hf : Function.Injective f) (b : A) :
    Function.Injective (kerMap f b) := fun x y hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))

lemma exact_kerMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (b : A) : Function.Exact (kerMap f b) (kerMap g b) := by
  intro x
  constructor
  · intro hx
    have hx' : g x.1 = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (hfg _).1 hx'
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show b • y = 0
    apply hf
    rw [map_smul, hy, map_zero]
    exact x.2
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((hfg _).2 ⟨y.1, rfl⟩)

lemma exact_quotMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (b : A) : Function.Exact (quotMap f b) (quotMap g b) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  constructor
  · intro hx
    have hx' : (LinearMap.range (LinearMap.lsmul A M₃ b)).mkQ (g x) = 0 := hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨w, hw⟩ := hx'
    obtain ⟨z, rfl⟩ := hg w
    have hw' : b • g z = g x := hw
    have h0 : g (x - b • z) = 0 := by rw [map_sub, map_smul, hw', sub_self]
    obtain ⟨y, hy⟩ := (hfg _).1 h0
    refine ⟨(LinearMap.range (LinearMap.lsmul A M₁ b)).mkQ y, ?_⟩
    show (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (f y) = _
    rw [hy, map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [← hy]
    show (LinearMap.range (LinearMap.lsmul A M₃ b)).mkQ (g (f y)) = 0
    rw [(hfg _).2 ⟨y, rfl⟩, map_zero]

lemma quotMap_surjective (g : M₂ →ₗ[A] M₃) (hg : Function.Surjective g) (b : A) :
    Function.Surjective (quotMap g b) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨y, rfl⟩ := hg x
  exact ⟨(LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ y, rfl⟩

noncomputable def delta (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    LinearMap.ker (LinearMap.lsmul A M₃ b) →ₗ[A] (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) :=
  SnakeLemma.δ' (LinearMap.lsmul A M₁ b) (LinearMap.lsmul A M₂ b) (LinearMap.lsmul A M₃ b)
    f g hfg f g hfg (by ext x; simp) (by ext x; simp)
    (LinearMap.ker (LinearMap.lsmul A M₃ b)).subtype (LinearMap.exact_subtype_ker_map _)
    (LinearMap.range (LinearMap.lsmul A M₁ b)).mkQ (LinearMap.exact_map_mkQ_range _)
    hg hf

lemma exact_kerMap_delta (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    Function.Exact (kerMap g b) (delta f g hf hg hfg b) :=
  SnakeLemma.exact_δ'_right _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.ker (LinearMap.lsmul A M₂ b)).subtype (LinearMap.exact_subtype_ker_map _)
    _ _ _ _ _ _ (kerMap g b) (by ext x; rfl) Subtype.val_injective

lemma exact_delta_quotMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    Function.Exact (delta f g hf hg hfg b) (quotMap f b) :=
  SnakeLemma.exact_δ'_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (LinearMap.exact_map_mkQ_range _)
    _ _ (quotMap f b) (by ext x; rfl) (Submodule.mkQ_surjective _)

end ScalarSnakeLength

theorem scalar_snake_length :
    ∀ (A : Type) [CommRing A] (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [AddCommGroup M₂]
      [AddCommGroup M₃] [Module A M₁] [Module A M₂] [Module A M₃] (f : M₁ →ₗ[A] M₂)
      (g : M₂ →ₗ[A] M₃), Function.Injective f → Function.Surjective g → Function.Exact f g →
      ∀ b : A,
        Module.length A (M₂ ⧸ LinearMap.range (LinearMap.lsmul A M₂ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₁ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₃ b)) =
          Module.length A (LinearMap.ker (LinearMap.lsmul A M₂ b)) +
            Module.length A (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) +
            Module.length A (M₃ ⧸ LinearMap.range (LinearMap.lsmul A M₃ b)) ∧
        Module.length A (LinearMap.ker (LinearMap.lsmul A M₂ b)) ≤
          Module.length A (LinearMap.ker (LinearMap.lsmul A M₁ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₃ b)) := by
  intro A _ M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg b
  open ScalarSnakeLength in
  have e1 := length_of_injective (kerMap f b) (kerMap_injective f hf b)
  have e2 := length_mid (kerMap f b) (kerMap g b) (exact_kerMap f g hf hfg b)
  have e3 := length_mid (kerMap g b) (delta f g hf hg hfg b) (exact_kerMap_delta f g hf hg hfg b)
  have e4 := length_mid (delta f g hf hg hfg b) (quotMap f b)
    (exact_delta_quotMap f g hf hg hfg b)
  have e5 := length_mid (quotMap f b) (quotMap g b) (exact_quotMap f g hg hfg b)
  have e6 := length_of_surjective (quotMap g b) (quotMap_surjective g hg b)
  rw [e1, e2, e3, e4, e5, ← e6]
  constructor
  · ac_rfl
  · exact add_le_add le_rfl le_self_add

end GlobalTheory
end

section
section
namespace GlobalTheory.HerbrandLength

open IsLocalRing

variable {A : Type} [CommRing A]

def Concl (b : A) (P : Finset (PrimeSpectrum A)) (M : Type) [AddCommGroup M] [Module A M] : Prop :=
  Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧
  Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) =
    Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b}))

theorem loc_exact (p : Ideal A) [p.IsPrime] {N M Q : Type} [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [AddCommGroup Q] [Module A Q] (f : N →ₗ[A] M) (g : M →ₗ[A] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl N) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
  Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f)
    (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)

theorem loc_zero_of_ann (p : Ideal A) [p.IsPrime] (M : Type) [AddCommGroup M] [Module A M]
    (s : A) (hs : s ∉ p) (hsM : ∀ x : M, s • x = 0) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) = 0 :=
  Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).2 fun x => ⟨s, hs, hsM x⟩)

theorem loc_quot_self (p : Ideal A) [hp : p.IsPrime] :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (A ⧸ p)) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (A ⧸ p))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ p.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring

theorem ker_eq_coker {M : Type} [AddCommGroup M] [Module A M] (φ : M →ₗ[A] M)
    (h : Module.length A M ≠ ⊤) :
    Module.length A (M ⧸ LinearMap.range φ) = Module.length A (LinearMap.ker φ) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.ker φ).subtype (LinearMap.ker φ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [φ.quotKerEquivRange.length_eq] at h1
  have hR : Module.length A (LinearMap.range φ) ≠ ⊤ :=
    ne_top_of_le_ne_top h (le_self_add.trans_eq h2.symm)
  exact WithTop.add_left_cancel hR (h2.symm.trans (h1.trans (add_comm _ _)))

theorem enat_cancel {c₂ k₁ k₂ k₃ s₁ s₃ : ℕ∞} (h₁ : k₁ ≠ ⊤) (h₃ : k₃ ≠ ⊤)
    (e : c₂ + k₁ + k₃ = k₂ + (k₁ + s₁) + (k₃ + s₃)) : c₂ = k₂ + (s₁ + s₃) := by
  have hne : k₁ + k₃ ≠ ⊤ := WithTop.add_ne_top.2 ⟨h₁, h₃⟩
  have h : c₂ + (k₁ + k₃) = k₂ + (s₁ + s₃) + (k₁ + k₃) := by
    rw [← add_assoc, e]
    ring
  exact WithTop.add_right_cancel hne h

theorem concl_ext {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃] (b : A) (P : Finset (PrimeSpectrum A))
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : Concl b P M₁) (h₃ : Concl b P M₃) : Concl b P M₂ := by
  obtain ⟨e, hle⟩ := GlobalTheory.scalar_snake_length A M₁ M₂ M₃ f g hf hg hfg b
  obtain ⟨k1, s1⟩ := h₁
  obtain ⟨k3, s3⟩ := h₃
  have hne := WithTop.add_ne_top.2 ⟨k1, k3⟩
  refine ⟨ne_top_of_le_ne_top hne hle, ?_⟩
  have hsum : ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₂) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) =
      (∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₁) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b}))) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M₃) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [loc_exact p.asIdeal f g hf hg hfg, add_mul]
  rw [hsum]
  rw [s1, s3] at e
  exact enat_cancel k1 k3 e

theorem concl_subsingleton (b : A) (P : Finset (PrimeSpectrum A)) (M : Type) [AddCommGroup M]
    [Module A M] [Subsingleton M] : Concl b P M := by
  have hk : Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) = 0 :=
    Module.length_eq_zero_iff.2 ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  have hc : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = 0 :=
    Module.length_eq_zero_iff.2 ((Submodule.mkQ_surjective _).subsingleton)
  refine ⟨by rw [hk]; exact ENat.zero_ne_top, ?_⟩
  rw [hk, hc, zero_add, eq_comm]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [loc_zero_of_ann p.asIdeal M 1 (Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one))
    (fun x => Subsingleton.elim _ _), zero_mul]

theorem concl_equiv {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (b : A) (P : Finset (PrimeSpectrum A)) (e : M ≃ₗ[A] N) (h : Concl b P M) : Concl b P N :=
  concl_ext (M₃ := PUnit) b P e.toLinearMap 0 e.injective (Function.surjective_to_subsingleton _)
    ((e.exact_zero_iff_surjective _).2 e.surjective) h (concl_subsingleton b P PUnit)

theorem ne_max [IsLocalRing A] (p : PrimeSpectrum A) (h : ringKrullDim (A ⧸ p.asIdeal) = 1) :
    p.asIdeal ≠ maximalIdeal A := by
  intro hpm
  letI := Ideal.Quotient.field (maximalIdeal A)
  have h0 : ringKrullDim (A ⧸ maximalIdeal A) = 0 := ringKrullDim_eq_zero_of_field (A ⧸ maximalIdeal A)
  rw [← hpm, h] at h0
  exact one_ne_zero h0

theorem eq_of_le [IsLocalRing A] (p q : PrimeSpectrum A) (hp : ringKrullDim (A ⧸ p.asIdeal) = 1)
    (hq : ringKrullDim (A ⧸ q.asIdeal) = 1) (hle : p.asIdeal ≤ q.asIdeal) : p = q := by
  by_contra hne
  have hlt : p.asIdeal < q.asIdeal := lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
  have hqm : q.asIdeal < maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) (ne_max q hq)
  let a : PrimeSpectrum.zeroLocus (R := A) p.asIdeal := ⟨p, fun _ h => h⟩
  let c : PrimeSpectrum.zeroLocus (R := A) p.asIdeal := ⟨q, fun _ h => hle h⟩
  let d : PrimeSpectrum.zeroLocus (R := A) p.asIdeal :=
    ⟨⟨maximalIdeal A, inferInstance⟩, fun _ h => (hle.trans hqm.le) h⟩
  have hac : a < c := Subtype.mk_lt_mk.2 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hlt)
  have hcd : c < d := Subtype.mk_lt_mk.2 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hqm)
  let s : LTSeries (PrimeSpectrum.zeroLocus (R := A) p.asIdeal) :=
    ⟨2, ![a, c, d], fun i => by fin_cases i <;> first | exact hac | exact hcd | simp [hac, hcd]⟩
  have hs := Order.LTSeries.length_le_krullDim s
  rw [← ringKrullDim_quotient, hp] at hs
  have h2 : s.length = 2 := rfl
  rw [h2] at hs
  exact absurd hs (by decide)

theorem concl_prime [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) (p : PrimeSpectrum A)
    (hpP : p ∈ P) : Concl b P (A ⧸ p.asIdeal) := by
  have hb : b ∉ p.asIdeal := (hP p hpP).2
  have hker : LinearMap.ker (LinearMap.lsmul A (A ⧸ p.asIdeal) b) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at hx
    exact (mul_eq_zero.1 hx).resolve_left (fun h => hb (Ideal.Quotient.eq_zero_iff_mem.1 h))
  have hrange : LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) b) =
      Submodule.map p.asIdeal.mkQ (Ideal.span {b}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨b * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b),
        by rw [LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul]⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      exact ⟨p.asIdeal.mkQ c, by rw [LinearMap.lsmul_apply, ← LinearMap.map_smul, smul_eq_mul, mul_comm]⟩
  have hcok : Module.length A ((A ⧸ p.asIdeal) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ p.asIdeal) b)) =
      Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) :=
    ((Submodule.quotEquivOfEq _ _ hrange).trans
      (Submodule.quotientQuotientEquivQuotientSup p.asIdeal (Ideal.span {b}))).length_eq
  have hk0 : Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ p.asIdeal) b)) = 0 := by
    rw [hker]; exact Module.length_eq_zero_iff.2 inferInstance
  refine ⟨by rw [hk0]; exact ENat.zero_ne_top, ?_⟩
  rw [hcok, hk0, zero_add, Finset.sum_eq_single p, loc_quot_self, one_mul]
  · intro q hq hqp
    have hnle : ¬ p.asIdeal ≤ q.asIdeal := fun h => hqp (eq_of_le p q (hP p hpP).1 (hP q hq).1 h).symm
    obtain ⟨s, hsp, hsq⟩ := SetLike.not_le_iff_exists.1 hnle
    rw [loc_zero_of_ann q.asIdeal _ s hsq (fun x => ?_), zero_mul]
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hsp
  · intro h; exact absurd hpP h

theorem concl_max [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) :
    Concl b P (A ⧸ maximalIdeal A) := by
  have hlen : Module.length A (A ⧸ maximalIdeal A) = 1 :=
    Module.length_eq_one_iff.2
      (isSimpleModule_iff_isCoatom.2 (inferInstance : (maximalIdeal A).IsMaximal).out)
  have hfin : Module.length A (A ⧸ maximalIdeal A) ≠ ⊤ := by rw [hlen]; exact ENat.one_ne_top
  refine ⟨ne_top_of_le_ne_top hfin
    (Module.length_le_of_injective (LinearMap.ker _).subtype (Submodule.injective_subtype _)), ?_⟩
  rw [ker_eq_coker _ hfin, Finset.sum_eq_zero, add_zero]
  intro p hp
  have hnle : ¬ maximalIdeal A ≤ p.asIdeal := fun h =>
    ne_max p (hP p hp).1 (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) h)
  obtain ⟨s, hsm, hsp⟩ := SetLike.not_le_iff_exists.1 hnle
  rw [loc_zero_of_ann p.asIdeal _ s hsp (fun x => ?_), zero_mul]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ hsm

end GlobalTheory.HerbrandLength

open GlobalTheory.HerbrandLength in

theorem GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
  intro A _ _ _ b P hP M _ _ hfin hM
  revert hM
  induction hfin using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => intro _; exact concl_subsingleton b P N
  | quotient N p e =>
    intro hN
    have hpN : p ∈ Module.support A N := by
      rw [e.support_eq, Module.mem_support_iff_of_finite]
      intro r hr
      have h1 := Module.mem_annihilator.1 hr 1
      rwa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at h1
    rcases hN p hpN with hpP | hpm
    · exact concl_equiv b P e.symm (concl_prime b P hP p hpP)
    · exact concl_equiv b P ((Submodule.quotEquivOfEq _ _ hpm).symm.trans e.symm) (concl_max b P hP)
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hN
    exact concl_ext b P f g hf hg hfg
      (h₁ fun q hq => hN q (Module.support_subset_of_injective f hf hq))
      (h₃ fun q hq => hN q (Module.support_subset_of_surjective g hg hq))
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_coker_lsmul_eq_length_ker_add_sum' : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A)), (∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M], (∀ p ∈ Module.support A M, p ∈ P ∨ p.asIdeal = IsLocalRing.maximalIdeal A) → Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧ Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) + ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) := by
  atlas_forward_decl GlobalTheory.length_coker_lsmul_eq_length_ker_add_sum
end

section
section
namespace GlobalTheory.ASwap

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def mulMap (a b c : A) (hc : a * b = c) :
    (A ⧸ Ideal.span {a}) →ₗ[A] (A ⧸ Ideal.span {c}) :=
  Submodule.mapQ (Ideal.span {a}) (Ideal.span {c}) (LinearMap.lsmul A A b) (by
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply, smul_eq_mul]
    exact Submodule.mem_span_singleton.mpr ⟨r, by rw [← hc]; ring⟩)

lemma mulMap_mk (a b c : A) (hc : a * b = c) (x : A) :
    mulMap a b c hc (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (b * x) := rfl

lemma mulMap_injective (a b c : A) (hb : b ≠ 0) (hc : a * b = c) :
    Function.Injective (mulMap a b c hc) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    change mulMap a b c hc (Ideal.Quotient.mk _ x) = 0 at hq
    rw [mulMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hq
    obtain ⟨r, hr⟩ := hq
    change Ideal.Quotient.mk _ x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨r, ?_⟩
    apply mul_left_cancel₀ hb
    rw [← hr, ← hc]; ring

lemma map_mulMap_ker (a b c : A) (hc : a * b = c) :
    (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)).map (mulMap a b c hc) =
      Submodule.map (Submodule.mkQ (Ideal.span {c})) (Ideal.span {a} ⊓ Ideal.span {b} : Submodule A A) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.lsmul_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      refine ⟨b * x, ⟨?_, ?_⟩, rfl⟩
      · have hq' : Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0 := hq
        exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
      · exact Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩
  · rintro ⟨t, ⟨hta, htb⟩, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp htb
    refine ⟨Ideal.Quotient.mk _ x, ?_, ?_⟩
    · change Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_comm]; exact hta
    · change Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b)
      rw [mul_comm]

noncomputable def kerEquiv (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ≃ₗ[A]
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) :=
  (Submodule.equivMapOfInjective _ (mulMap_injective a b (a * b) hb rfl) _).trans
    ((LinearEquiv.ofEq _ _ (by
        rw [map_mulMap_ker, map_mulMap_ker b a (a * b) (mul_comm b a), inf_comm])).trans
      (Submodule.equivMapOfInjective _ (mulMap_injective b a (a * b) ha (mul_comm b a)) _).symm)

lemma range_lsmul_eq (a b : A) :
    LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) =
      Submodule.map (Submodule.mkQ (Ideal.span {a})) (Ideal.span {b} : Submodule A A) := by
  ext z
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_map]
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H x => exact ⟨x * b, Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩, by
        change Ideal.Quotient.mk _ (x * b) = Ideal.Quotient.mk _ (b * x); rw [mul_comm]⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    exact ⟨Ideal.Quotient.mk _ x, by
        change Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b); rw [mul_comm]⟩

noncomputable def cokerEquiv (a b : A) :
    ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≃ₗ[A]
      A ⧸ (Ideal.span {a} ⊔ Ideal.span {b} : Submodule A A) :=
  (Submodule.quotEquivOfEq _ _ (range_lsmul_eq a b)).trans
    (Submodule.quotientQuotientEquivQuotientSup _ _)

end GlobalTheory.ASwap

theorem GlobalTheory.kernel_cokernel_length_swap :
    ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  intro A _ _ a b ha hb
  refine ⟨(GlobalTheory.ASwap.kerEquiv a b ha hb).length_eq, ?_⟩
  exact ((GlobalTheory.ASwap.cokerEquiv a b).trans ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans
    (GlobalTheory.ASwap.cokerEquiv b a).symm)).length_eq
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap : ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  atlas_forward_decl GlobalTheory.kernel_cokernel_length_swap
end

section
section
open IsLocalRing

namespace GlobalTheory.IntersectionSymm

theorem height_add_dim_quotient_le {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, hp⟩
  haveI : Nonempty (PrimeSpectrum R) := ⟨P⟩
  have h1 : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici P := by
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
    rfl
  have h2 : ringKrullDim (R ⧸ p) = (Order.coheight P : ℕ∞) := by
    rw [ringKrullDim_quotient, h1, Order.coheight_eq_krullDim_Ici]
  have h3 : p.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  rw [h2, h3, ← WithBot.coe_add]
  change _ ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) P

theorem arith (h : ℕ∞) (d : WithBot ℕ∞) (h1 : (h : WithBot ℕ∞) + d ≤ 2) (h2 : ¬ d ≤ 0) :
    h ≤ 1 ∧ (h = 1 → d = 1) := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h2
  | coe e =>
    have h1' : h + e ≤ 2 := by
      rw [← WithBot.coe_add, ← WithBot.coe_ofNat, WithBot.coe_le_coe] at h1; exact h1
    have h2' : ¬ e ≤ 0 := fun h => h2 (by exact_mod_cast h)
    induction e using ENat.recTopCoe with
    | top => simp at h1'
    | coe n =>
      induction h using ENat.recTopCoe with
      | top => simp at h1'
      | coe m =>
        have a1 : m + n ≤ 2 := by exact_mod_cast h1'
        have a2 : ¬ n ≤ 0 := fun h => h2' (by exact_mod_cast h)
        refine ⟨by exact_mod_cast (show m ≤ 1 by omega), fun hm => ?_⟩
        have : m = 1 := by exact_mod_cast hm
        have : n = 1 := by omega
        subst this; rfl

theorem not_dim_quotient_le_zero {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime]
    (hne : ¬ p.IsMaximal) : ¬ ringKrullDim (A ⧸ p) ≤ 0 := by
  intro h
  haveI : Ring.KrullDimLE 0 (A ⧸ p) := Ring.krullDimLE_iff.2 (by exact_mod_cast h)
  exact hne (Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain)

theorem dim_quotient_eq_one {A : Type} [CommRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (A ⧸ p) = 1 := by
  have h1 := height_add_dim_quotient_le p
  rw [hA] at h1
  have hne : ¬ p.IsMaximal := by
    intro hm
    have := maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← IsLocalRing.eq_maximalIdeal hm, hp, hA] at this
    exact absurd this (by decide)
  exact (arith _ _ h1 (not_dim_quotient_le_zero p hne)).2 hp

theorem height_one_or_eq_max {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (p : Ideal A) [hp : p.IsPrime] (h0 : p ≠ ⊥) :
    p.height = 1 ∨ p = maximalIdeal A := by
  by_cases hm : p = maximalIdeal A
  · exact Or.inr hm
  left
  have hne : ¬ p.IsMaximal := fun h => hm (IsLocalRing.eq_maximalIdeal h)
  have h1 := height_add_dim_quotient_le p
  rw [hA] at h1
  have hle := (arith _ _ h1 (not_dim_quotient_le_zero p hne)).1
  have hz : p.height ≠ 0 := by
    intro hz
    rw [Ideal.height_eq_zero_iff] at hz
    exact h0 (le_bot_iff.1 (hz.2 ⟨Ideal.bot_prime, bot_le⟩ bot_le))
  exact le_antisymm hle (ENat.one_le_iff_ne_zero.2 hz)

end GlobalTheory.IntersectionSymm

namespace GlobalTheory.IntersectionSymm

theorem length_localized_quotient {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (A ⧸ Ideal.span {a})) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) a}) := by
  let f := Algebra.linearMap A (Localization.AtPrime p)
  let M' : Submodule A A := Ideal.span {a}
  let g := M'.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl f
  let e0 := IsLocalizedModule.iso p.primeCompl g
  let e := e0.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
  rw [e.length_eq]
  have h : Submodule.localized' (Localization.AtPrime p) p.primeCompl f M' =
      Ideal.span {algebraMap A (Localization.AtPrime p) a} := by
    rw [Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]
  rw [h]

theorem length_quotient_sup {A : Type} [CommRing A] (p : Ideal A) (b : A) :
    Module.length A (A ⧸ (p ⊔ Ideal.span {b})) =
      Module.length (A ⧸ p) ((A ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p b}) := by
  rw [← (DoubleQuot.quotQuotEquivQuotSupₐ A p (Ideal.span {b})).toLinearEquiv.length_eq,
    Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk]
  exact Module.length_eq_of_surjective (S := A) (R := A ⧸ p) Ideal.Quotient.mk_surjective

theorem length_localized_ne_top {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) (a : A) (ha : a ≠ 0) :
    Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) a}) ≠ ⊤ := by
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]
    rfl
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  apply mem_nonZeroDivisors_of_ne_zero
  exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _
    (Ideal.primeCompl_le_nonZeroDivisors p) (mem_nonZeroDivisors_of_ne_zero ha)

theorem length_quotient_ne_top {A : Type} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hd : ringKrullDim (A ⧸ p) = 1) (b : A) (hb : b ∉ p) :
    Module.length (A ⧸ p) ((A ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p b}) ≠ ⊤ := by
  haveI : Ring.KrullDimLE 1 (A ⧸ p) := by
    rw [Ring.krullDimLE_iff, hd]
    rfl
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  apply mem_nonZeroDivisors_of_ne_zero
  rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.IntersectionSymm

namespace GlobalTheory.IntersectionSymm

theorem support_cases {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a : A) (ha : a ≠ 0) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) :
    ∀ p ∈ Module.support A (A ⧸ Ideal.span {a}), p ∈ P ∨ p.asIdeal = maximalIdeal A := by
  intro p hp
  rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hp
  have hap : a ∈ p.asIdeal := hp (Ideal.subset_span rfl)
  have h0 : p.asIdeal ≠ ⊥ := fun h => ha (by rw [h] at hap; exact (Submodule.mem_bot A).1 hap)
  rcases height_one_or_eq_max hA p.asIdeal h0 with h | h
  · exact Or.inl ((hP p).2 ⟨h, hap⟩)
  · exact Or.inr h

theorem side {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (P Q : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal)
    (hQ : ∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) (hdis : Disjoint P Q) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ ∧
    Module.length A ((A ⧸ Ideal.span {a}) ⧸
        LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸
          Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
        Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal b}) := by
  have hmem : ∀ p ∈ P, p.asIdeal.height = 1 ∧ a ∈ p.asIdeal ∧ b ∉ p.asIdeal := by
    intro p hp
    obtain ⟨h1, h2⟩ := (hP p).1 hp
    exact ⟨h1, h2, fun hb => Finset.disjoint_left.1 hdis hp ((hQ p).2 ⟨h1, hb⟩)⟩
  have key := GlobalTheory.T.length_coker_lsmul_eq_length_ker_add_sum' A b P
    (fun p hp => ⟨dim_quotient_eq_one hA p.asIdeal (hmem p hp).1, (hmem p hp).2.2⟩)
    (A ⧸ Ideal.span {a}) (support_cases hA a ha P hP)
  refine ⟨key.1, key.2.trans ?_⟩
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [length_localized_quotient, length_quotient_sup]

theorem terms_ne_top {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (a b : A) (ha : a ≠ 0) (P Q : Finset (PrimeSpectrum A))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal)
    (hQ : ∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) (hdis : Disjoint P Q) :
    ∀ p ∈ P, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸
          Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
        Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal b}) ≠ ⊤ := by
  intro p hp
  obtain ⟨h1, _⟩ := (hP p).1 hp
  have hb : b ∉ p.asIdeal := fun hb => Finset.disjoint_left.1 hdis hp ((hQ p).2 ⟨h1, hb⟩)
  exact WithTop.mul_ne_top (length_localized_ne_top p.asIdeal h1 a ha)
    (length_quotient_ne_top p.asIdeal (dim_quotient_eq_one hA p.asIdeal h1) b hb)

theorem toNat_sum_mul {ι : Type} (S : Finset ι) (f g : ι → ℕ∞) (h : ∀ i ∈ S, f i * g i ≠ ⊤) :
    ∑ i ∈ S, (f i).toNat * (g i).toNat = (∑ i ∈ S, f i * g i).toNat := by
  rw [ENat.toNat_sum h]
  exact Finset.sum_congr rfl fun i _ => (ENat.toNat_mul _ _).symm

theorem intersection_symm : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ringKrullDim A = 2 → ∀ (a b : A), a ≠ 0 → b ≠ 0 → ∀ (P Q : Finset (PrimeSpectrum A)), (∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) → (∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) → Disjoint P Q → ∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal b})).toNat = ∑ p ∈ Q, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) b})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal a})).toNat := by
  intro A _ _ _ _ hA a b ha hb P Q hP hQ hdis
  obtain ⟨hK, hC⟩ := side hA a b ha P Q hP hQ hdis
  obtain ⟨_, hC'⟩ := side hA b a hb Q P hQ hP hdis.symm
  obtain ⟨hk, hc⟩ := GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap A a b ha hb
  have hS := hC.symm.trans (hc.trans hC')
  rw [← hk] at hS
  have hS' := WithTop.add_left_cancel hK hS
  refine (toNat_sum_mul P _ _ (terms_ne_top hA a b ha P Q hP hQ hdis)).trans
    ((congrArg ENat.toNat hS').trans
      (toNat_sum_mul Q _ _ (terms_ne_top hA b a hb Q P hQ hP hdis.symm)).symm)

end GlobalTheory.IntersectionSymm
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_sum_height_one_disjoint_divisors : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ringKrullDim A = 2 → ∀ (a b : A), a ≠ 0 → b ≠ 0 → ∀ (P Q : Finset (PrimeSpectrum A)), (∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ a ∈ p.asIdeal) → (∀ p, p ∈ Q ↔ p.asIdeal.height = 1 ∧ b ∈ p.asIdeal) → Disjoint P Q → ∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal b})).toNat = ∑ p ∈ Q, (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) b})).toNat * (Module.length (A ⧸ p.asIdeal) ((A ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal a})).toNat := by
  atlas_forward_decl GlobalTheory.IntersectionSymm.intersection_symm
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.CycLoc

theorem length_quot_equiv (R S : Type) [CommRing R] [CommRing S] (e : R ≃+* S) (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {e a}) := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  rw [← Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e a}) e.surjective]
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) f (by
    rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq

theorem finite_height_one (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (a : R) (ha : a ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a})).preimage
    (f := PrimeSpectrum.asIdeal) fun _ _ _ _ h => PrimeSpectrum.ext h).subset ?_
  rintro p ⟨hp, hap⟩
  refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hap⟩, fun q hq hqp => ?_⟩
  by_contra hn
  have := hq.1
  have h1 : q < p.asIdeal := lt_of_le_not_ge hqp hn
  have h0 : (⊥ : Ideal R) < q := bot_lt_iff_ne_bot.2 fun h =>
    ha (by simpa [h] using (Ideal.span_singleton_le_iff_mem _).1 hq.2)
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  rw [hp] at e1
  have : (⊥ : Ideal R).height + 1 + 1 ≤ 1 := (add_le_add_left e0 1).trans e1
  rw [Ideal.height_bot] at this
  exact absurd this (by decide)

theorem stalk_equiv (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x p ∈ U) (hx : x ∈ U) (s : Γ(X, U)),
        e (X.presheaf.germ U _ hq s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal) (X.presheaf.germ U x hx s) := by
  let y : Spec (X.presheaf.stalk x) := p
  have := GlobalTheory.LocalRingGeneralisation.isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  refine Eq.trans ?_ h2
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

theorem specializes_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨p, rfl⟩

theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨e, -⟩ := stalk_equiv X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

theorem mem_nonzeroLocus_iff_notMem {X : Scheme.{0}} {A : LB X} (s : A.Sec) {i : A.ι} {x : X} (hi : x ∈ A.U i)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ nonzeroLocus s ↔ X.presheaf.germ _ x hi (s.f i) ∉ p.asIdeal := by
  have hzi : X.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk X x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv X x p
  rw [Cartier.mem_nonzeroLocus_iff s i hzi, Scheme.mem_basicOpen _ _ _ hzi, ← MulEquiv.isUnit_map e, he _ hzi hi,
    IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal, Ideal.mem_primeCompl_iff]

theorem ker_stalkMap_clo (X : Scheme.{0}) (z : X) (w : clo z) (p : PrimeSpectrum (X.presheaf.stalk (cloι z w)))
    (hp : X.fromSpecStalk (cloι z w) p = z) : RingHom.ker ((cloι z).stalkMap w).hom = p.asIdeal := by
  let g : PrimeSpectrum ((clo z).presheaf.stalk w) := ⟨⊥, Ideal.isPrime_bot⟩
  have hg : (clo z).fromSpecStalk w g = genericPoint (clo z) := by
    have h := coheight_fromSpecStalk (clo z) w g
    rw [show g.asIdeal.height = 0 from Ideal.height_bot, Order.coheight_eq_zero] at h
    exact ((genericPoint_specializes _).antisymm (h (show _ ≤ genericPoint (clo z) from genericPoint_specializes _))).eq.symm
  have h : X.fromSpecStalk (cloι z w) (Spec.map ((cloι z).stalkMap w) g) = cloι z ((clo z).fromSpecStalk w g) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun f => f g)
      (Scheme.SpecMap_stalkMap_fromSpecStalk (cloι z) (x := w))).trans (Scheme.Hom.comp_apply _ _ _))
  rw [hg, cloι_genericPoint] at h
  have h' := (X.fromSpecStalk (cloι z w)).isEmbedding.injective (h.trans hp.symm)
  exact congrArg PrimeSpectrum.asIdeal h'

theorem germ_secPull {X V : Scheme.{0}} {L : LB X} (s : L.Sec) (b : V ⟶ X) (v : V) (i : L.ι) (hi : b v ∈ L.U i)
    (hv : v ∈ (L.pull b).U fun _ => i) :
    V.presheaf.germ _ v hv ((GlobalTheory.secPull s b).f fun _ => i) = b.stalkMap v (X.presheaf.germ _ _ hi (s.f i)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem coheight_one_iff (hq : IsAmb q) {z : Y} (w : clo z) (hz : Order.coheight z = 1) :
    Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2 := by
  have hB := GlobalTheory.MixHt.hasDim_basic k Y q hq
  obtain ⟨m, hm⟩ := hB.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint Y)
  have hY : topologicalKrullDim Y = d := (hB.2.2.2.2.2 Y d).1 hd
  cases d with
  | zero =>
    obtain ⟨d', -, hd'⟩ := hm z
    have := GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k Y q hq 0 hY z d' hd'
    rw [hz] at this
    simp at this
  | succ e => exact ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hY).2 z w hz).2

theorem germ_ne_zero {A : LB Y} {s : A.Sec} (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y} (hi : x ∈ A.U i) :
    Y.presheaf.germ _ x hi (s.f i) ≠ 0 := fun h0 =>
  fnOf_sec_ne_zero hs (gen_mem hi) ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))

variable [IsLocallyNoetherian Y]

theorem mult_eq {A : LB Y} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y}
    (hi : x ∈ A.U i) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1) :
    (divOfSec hA s hs).mult (Y.fromSpecStalk x p) = (Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
        (Y.presheaf.germ _ x hi (s.f i))})).toNat := by
  have hzi : Y.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk Y x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv Y x p
  rw [mult_divOfSec ((coheight_fromSpecStalk Y x p).trans hp) hzi, length_quot_equiv _ _ e, he _ hzi hi]

theorem resCyc_eq (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) {j : B.ι} {x : Y} (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1)
    (ht : Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) {z : Y} (hz : Y.fromSpecStalk x p = z) :
    resCyc hB t (Set.indicator {x} 1) z = (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
      ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat := by
  have hzx : z ⤳ x := hz ▸ specializes_fromSpecStalk Y x p
  have hz1 : Order.coheight z = 1 := hz ▸ (coheight_fromSpecStalk Y x p).trans hp
  have hzt : z ∈ nonzeroLocus t := hz ▸ (mem_nonzeroLocus_iff_notMem t hj p).2 ht
  obtain ⟨w, rfl⟩ : x ∈ Set.range (cloι z) :=
    hzx.mem_closed (cloι z).isClosedEmbedding.isClosed_range ⟨_, cloι_genericPoint z⟩
  have h : genericPoint (clo z) ∈ nonzeroLocus (GlobalTheory.secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rwa [cloι_genericPoint]
  have hw : w ∈ (B.pull (cloι z)).U fun _ => j := Set.mem_iInter.2 fun _ => hj
  have hk := ker_stalkMap_clo Y z w p hz
  let e : (Y.presheaf.stalk (cloι z w) ⧸ p.asIdeal) ≃+* (clo z).presheaf.stalk w :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective ((cloι z).stalkMap_surjective w))
  rw [resCyc, dif_pos h, finsum_eq_single _ w fun w' hw' => by
    rw [Set.indicator_of_notMem (s := {cloι z w}) (a := cloι z w')
      (fun e => hw' ((cloι z).isClosedEmbedding.injective (Set.mem_singleton_iff.1 e))), mul_zero],
    Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one,
    mult_divOfSec ((coheight_one_iff hq w hz1).2 hx) hw, germ_secPull t _ w j hj, length_quot_equiv _ _ e, Int.cast_natCast]
  rfl

theorem of_term_ne_zero (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x z : Y}
    (h : ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z ≠ 0) :
    Order.coheight x = 2 ∧ Order.coheight z = 1 ∧ z ∉ nonzeroLocus s ∧ z ⤳ x := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have h1' : (divOfSec hA s hs).mult z ≠ 0 := by exact_mod_cast h1
  have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h1'
  rw [resCyc] at h2
  split_ifs at h2 with h3
  · obtain ⟨w, hw⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero h2)
    obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 hw
    have h6 : cloι z w = x := Set.mem_singleton_iff.1 (Set.mem_of_indicator_ne_zero h5)
    have h7 := CartierDiv.coheight_eq_one_of_mult_ne_zero (Int.cast_ne_zero.1 h4)
    refine ⟨h6 ▸ (coheight_one_iff hq w hz).1 h7, hz,
      fun h => notMem_supp_divOfSec.2 h (CartierDiv.mem_supp_of_mult_ne_zero h1'), ?_⟩
    have := (genericPoint_specializes w).map (cloι z).continuous
    rwa [cloι_genericPoint, h6] at this
  · exact absurd rfl h2

theorem finsum_eq (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x : Y} {i : A.ι} {j : B.ι} (hi : x ∈ A.U i) (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (P : Finset (PrimeSpectrum (Y.presheaf.stalk x)))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal)
    (hb : ∀ p ∈ P, Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) :
    ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z =
      ((∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
          (Y.presheaf.germ _ x hi (s.f i))})).toNat * (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
        ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat : ℕ) : ℝ) := by
  classical
  let ι : PrimeSpectrum (Y.presheaf.stalk x) → Y := fun p => Y.fromSpecStalk x p
  have hι : Function.Injective ι := (Y.fromSpecStalk x).isEmbedding.injective
  rw [finsum_eq_sum_of_support_subset (s := P.image ι), Finset.sum_image fun _ _ _ _ h => hι h, Nat.cast_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [resCyc_eq hq hB t hj hx p ((hP p).1 hp).1 (hb p hp) rfl, mult_eq hA s hs hi p ((hP p).1 hp).1,
      Int.cast_natCast, Nat.cast_mul]
  · intro z hz
    obtain ⟨-, h1, h2, h3⟩ := of_term_ne_zero hq hA hB s t hs hz
    obtain ⟨p, rfl⟩ := (Scheme.range_fromSpecStalk (x := x)).ge h3
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hP p).2 ⟨(coheight_fromSpecStalk Y x p).symm.trans h1,
      not_not.1 (mt (mem_nonzeroLocus_iff_notMem s hi p).2 h2)⟩, rfl⟩)

end GlobalTheory.MixHt.CycLoc

namespace GlobalTheory.MixHt

open CycLoc in

theorem finsum_mult_resCyc_indicator_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ x : Y, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst x
  by_cases hx : Order.coheight x = 2
  swap
  · rw [finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hA hB s t hs h).1,
      finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hB hA t s ht h).1]
  obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hA x
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB x
  have ha := germ_ne_zero hs hi
  have hb := germ_ne_zero ht hj
  have hP := fun p => (finite_height_one _ _ ha).mem_toFinset (a := p)
  have hQ := fun p => (finite_height_one _ _ hb).mem_toFinset (a := p)
  have key (p : PrimeSpectrum (Y.presheaf.stalk x)) (h1 : p.asIdeal.height = 1)
      (h2 : Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal) (h3 : Y.presheaf.germ _ x hj (t.f j) ∈ p.asIdeal) : False :=
    (hst _ ((coheight_fromSpecStalk Y x p).trans h1)).elim
      (fun h => (mem_nonzeroLocus_iff_notMem s hi p).1 h h2) fun h => (mem_nonzeroLocus_iff_notMem t hj p).1 h h3
  rw [finsum_eq hq hA hB s t hs hi hj hx _ hP fun p hp => key p ((hP p).1 hp).1 ((hP p).1 hp).2,
    finsum_eq hq hB hA t s ht hj hi hx _ hQ fun p hp h => key p ((hQ p).1 hp).1 h ((hQ p).1 hp).2]
  refine congrArg _ (GlobalTheory.T.length_sum_height_one_disjoint_divisors _ ?_ _ _ ha hb _ _ hP hQ (Finset.disjoint_left.2 fun p hp hp' =>
    key p ((hP p).1 hp).1 ((hP p).1 hp).2 ((hQ p).1 hp').2))
  rw [ringKrullDim_stalk_eq_coheight, hx]
  rfl

end GlobalTheory.MixHt
end
end
