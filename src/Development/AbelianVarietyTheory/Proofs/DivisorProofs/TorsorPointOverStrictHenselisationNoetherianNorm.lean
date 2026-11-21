import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEnlargeGoodAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatAlgHomEtaleHeightOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemIntegralClosureOverGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleOfGaloisDescentHartogsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EtaleFiniteStrictHenselianSplit

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictHenselisation_enlarge_good_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.enlarge_good) | (exact GlobalTheory.KeyOriginEnlarge.enlarge_good) | (intros; apply GlobalTheory.KeyOriginEnlarge.enlarge_good  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem hart_of_flat : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B], GlobalTheory.GoodEtale.Hart A B B := by
  intro A _ _ _ _ B _ _ _ a ha m hm
  classical
  let I : Ideal A := Ideal.comap (algebraMap A B) ((Ideal.span {algebraMap A B a}).colon {m})
  have hI : ∀ u, u ∈ I ↔ ∃ m' : B, algebraMap A B u * m = algebraMap A B a * m' := by
    intro u
    simp only [I, Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc, mul_comm]⟩
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  have hm' : ∀ s : S, ∃ m' : B, algebraMap A B s * m = algebraMap A B a * m' := fun s =>
    (hI s).1 (hS ▸ Submodule.subset_span s.2)
  choose m' hm'' using hm'
  let f : (S → A) →ₗ[A] A × (S → A) :=
    LinearMap.prod (∑ s : S, (LinearMap.proj s).smulRight (s : A)) (a • LinearMap.id)
  let x : A × (S → A) →ₗ[A] B := (LinearMap.fst A A (S → A)).smulRight m -
    ∑ s : S, ((LinearMap.proj s).comp (LinearMap.snd A A (S → A))).smulRight (m' s)
  have hxf : x ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro c
    have e : ∀ s : S, (c s * s) • m = (a * c s) • m' s := by
      intro s
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, mul_assoc, hm'' s]; ring
    simp [x, f, Finset.sum_smul, e]
  obtain ⟨k, α, y, hxy, hαf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  set v := α ((1 : A), (0 : S → A)) with hvdef
  have hsv : ∀ s : S, ∀ j, (s : A) * v j ∈ Ideal.span {a} := by
    intro s j
    have e : f (Pi.single s 1) = (s : A) • ((1 : A), (0 : S → A)) + a • ((0 : A), Pi.single s 1) := by
      ext t
      · simp [f, Pi.single_apply]
      · simp [f]
    have h0 : α (f (Pi.single s 1)) = 0 := by
      simpa using congrArg (fun g => g (Pi.single s 1)) hαf
    rw [e, map_add, map_smul, map_smul] at h0
    have h1 := congrArg (fun w => w j) h0
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    rw [Ideal.mem_span_singleton']
    exact ⟨-(α ((0 : A), Pi.single s 1)) j, by rw [← hvdef] at h1; linear_combination -h1⟩
  have hv : ∀ j, v j ∈ Ideal.span {a} := by
    intro j
    apply GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one
    intro q hq h1
    obtain ⟨u, hu, m'', h⟩ := hm q hq h1
    refine ⟨u, hu, ?_⟩
    have huI : u ∈ I := (hI u).2 ⟨m'', by simpa [smul_eq_mul] using h⟩
    have hle : I ≤ (Ideal.span {a}).colon {v j} := by
      rw [← hS, Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
      exact hsv ⟨s, hs⟩ j
    have := hle huI
    rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this
  choose z hz using fun j => Ideal.mem_span_singleton'.mp (hv j)
  refine ⟨y (Finsupp.equivFunOnFinite.symm z), ?_⟩
  have hv' : v = a • Finsupp.equivFunOnFinite.symm z := by
    ext j; simp [← hz j, mul_comm]
  have hmx : m = x ((1 : A), (0 : S → A)) := by simp [x]
  rw [hmx, hxy, LinearMap.comp_apply, ← hvdef, hv', map_smul, Algebra.smul_def, smul_eq_mul]

end GlobalTheory.GoodEtale
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHartogsPropertyHeightOnePrimes_of_flat : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B], GlobalTheory.GoodEtale.Hart A B B := by
  first | (exact @GlobalTheory.GoodEtale.hart_of_flat) | (exact GlobalTheory.GoodEtale.hart_of_flat) | (intros; apply GlobalTheory.GoodEtale.hart_of_flat  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleBase

theorem flat_noetherian_nzd_intClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    Module.Flat A (Localization.AtPrime QA) ∧ IsNoetherianRing (Localization.AtPrime QA) ∧
      algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X ∈ nonZeroDivisors (Localization.AtPrime QA) ∧
      ∀ f : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA), IsIntegral (Localization.AtPrime QA) f →
        ∃ r : Localization.AtPrime QA, algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r = f := by
  intro A _ _ _ _ _ _ EA _ _ _ _ _ QA _ _ ρ _ _
  set R := Localization.AtPrime QA
  haveI : Algebra.Smooth A (Polynomial A) := Algebra.Smooth.mk
  haveI : Algebra.Smooth A EA := Algebra.Smooth.comp A (Polynomial A) EA
  haveI : Module.Flat EA R := IsLocalization.flat R QA.primeCompl
  haveI : Module.Flat A EA := Algebra.Smooth.flat A EA
  haveI : Module.Flat (Polynomial A) EA := Algebra.Smooth.flat (Polynomial A) EA
  have hflat : Module.Flat A R := Module.Flat.trans A EA R
  refine ⟨hflat, ?_, ?_, ?_⟩
  · haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
    exact IsLocalization.isNoetherianRing QA.primeCompl R inferInstance
  · haveI : Module.Flat (Polynomial A) R := Module.Flat.trans (Polynomial A) EA R
    have hX : (Polynomial.X : Polynomial A) ∈ nonZeroDivisors (Polynomial A) :=
      Polynomial.monic_X.mem_nonZeroDivisors
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hX
    have h1 : ∀ z : R, algebraMap (Polynomial A) R Polynomial.X * z = 0 → z = 0 := by
      intro z hz
      apply hreg
      simp only [Algebra.smul_def, smul_zero, mul_zero]
      exact hz
    exact ⟨h1, fun z hz => h1 z (by rw [mul_comm]; exact hz)⟩
  · intro f hf
    set K := FractionRing A
    letI : Algebra K (R ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
    haveI : IsScalarTower A K (R ⊗[A] K) := inferInstance
    haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (R ⊗[A] K) :=
      (Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) K).2 inferInstance
    let e : GlobalTheory.LocAcyc.GenFib A R ≃ₐ[R] R ⊗[A] K :=
      IsLocalization.algEquiv (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) _ _
    have H1 : Function.Bijective (TensorProduct.toIntegralClosure A EA K) :=
      TensorProduct.toIntegralClosure_bijective_of_smooth
    have H2 : Function.Bijective (TensorProduct.toIntegralClosure EA R (EA ⊗[A] K)) :=
      TensorProduct.toIntegralClosure_bijective_of_isLocalization QA.primeCompl
    have H : Function.Bijective (TensorProduct.toIntegralClosure A R K) :=
      TensorProduct.toIntegralClosure_bijective_of_tower H1 H2
    have hf' : IsIntegral R (e f) := hf.map e.toAlgHom
    obtain ⟨y, hy⟩ := H.2 ⟨e f, hf'⟩
    have hy' : (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = e f := congrArg Subtype.val hy
    have key : ∀ y : R ⊗[A] integralClosure A K, ∃ b : R,
        (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = b ⊗ₜ[A] (1 : K) := by
      intro y
      induction y with
      | zero => exact ⟨0, by simp⟩
      | tmul b c =>
        obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
        refine ⟨r • b, ?_⟩
        rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
        rfl
      | add u v hu hv =>
        obtain ⟨a, ha⟩ := hu
        obtain ⟨b, hb⟩ := hv
        exact ⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
    obtain ⟨b, hb⟩ := key y
    refine ⟨b, ?_⟩
    apply e.injective
    rw [AlgEquiv.commutes, ← hy', hb]
    rfl

end GlobalTheory.GoodEtaleBase
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibreBase_flat_noetherian_intClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    Module.Flat A (Localization.AtPrime QA) ∧ IsNoetherianRing (Localization.AtPrime QA) ∧
      algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X ∈ nonZeroDivisors (Localization.AtPrime QA) ∧
      ∀ f : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA), IsIntegral (Localization.AtPrime QA) f →
        ∃ r : Localization.AtPrime QA, algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r = f := by
  first | (exact @GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed) | (exact GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed) | (intros; apply GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.TorsorTrace

theorem injective_trace_galoisData : ∀ (F D : Type) [CommRing F] [CommRing D] [Algebra F D] (q : ℕ) [NeZero q]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[F] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor F D q act →
    Function.Injective (algebraMap F D) ∧
    (∃ τ : D →ₗ[F] F, ∀ d : D, algebraMap F D (τ d) = ∑ g, act g d) ∧
    ∃ (n : ℕ) (x y : Fin n → D), ∀ g, ∑ i, x i * act g (y i) = if g = 1 then 1 else 0 := by
  intro F D _ _ _ q _ act h
  obtain ⟨_, _, hff, hbij⟩ := h
  have hinj : Function.Injective (algebraMap F D) := FaithfulSMul.algebraMap_injective F D
  refine ⟨hinj, ?_, ?_⟩
  · have hex : ∀ d : D, ∃ c : F, algebraMap F D c = ∑ g, act g d := by
      intro d
      have hfix : ∀ k, act k (∑ g, act g d) = ∑ g, act g d := by
        intro k
        rw [map_sum]
        refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
        intro g
        simp [map_mul]
      have h1 : (∑ g, act g d) ⊗ₜ[F] (1 : D) = (1 : D) ⊗ₜ[F] (∑ g, act g d) := by
        apply hbij.1
        rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
          map_one, map_one, mul_one, one_mul]
        funext k
        exact (hfix k).symm
      have := (Algebra.IsEffective.of_faithfullyFlat F D (∑ g, act g d)).1 (by
        rw [Algebra.TensorProduct.includeLeftSubRight_apply, h1, sub_self])
      obtain ⟨c, hc⟩ := this
      exact ⟨c, hc⟩
    choose t ht using hex
    refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩
    · intro a b
      apply hinj
      simp [ht, Finset.sum_add_distrib]
    · intro a b
      apply hinj
      rw [RingHom.id_apply, smul_eq_mul, map_mul, ht, ht, ← Algebra.smul_def, Finset.smul_sum]
      simp
  · obtain ⟨z, hz⟩ := hbij.2 (fun g => if g = 1 then 1 else 0)
    obtain ⟨n, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    refine ⟨n, x, y, fun g => ?_⟩
    have := congrFun hz g
    rw [map_sum, Finset.sum_apply] at this
    exact this

end GlobalTheory.TorsorTrace
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.ClosureHartogs

theorem closure_hart : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (τ : D →ₗ[GlobalTheory.LocAcyc.GenFib A R] GlobalTheory.LocAcyc.GenFib A R),
      (∀ c ∈ GlobalTheory.KeyOriginNoeth.closure A R D, ∃ r : R, algebraMap R _ r = τ c) →
    ∀ (a₀ : A), a₀ ≠ 0 → ∀ (n : ℕ) (x y : Fin n → D),
      (∀ i, y i ∈ GlobalTheory.KeyOriginNoeth.closure A R D) →
      (∀ d : D, ∑ i, x i * algebraMap _ D (τ (y i * d)) =
        GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ hHR hinj D _ _ τ hτC a₀ ha₀ n x y hy hid
  set F := GlobalTheory.LocAcyc.GenFib A R
  set C := GlobalTheory.KeyOriginNoeth.closure A R D
  letI : Algebra R D := (GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  have hbase : ∀ r : R, GlobalTheory.KeyOriginNoeth.baseHom A R D r = algebraMap F D (algebraMap R F r) :=
    fun r => rfl
  have hmemC : ∀ z : D, z ∈ C ↔ IsIntegral R z := fun z => Iff.rfl
  have hsmulC : ∀ (r : R) (c : C), ((r • c : C) : D) = GlobalTheory.KeyOriginNoeth.baseHom A R D r * c :=
    fun r c => rfl
  have hτm : ∀ (f : F) (w : D), τ (algebraMap F D f * w) = f * τ w := by
    intro f w; rw [← Algebra.smul_def, τ.map_smul, smul_eq_mul]

  have hunit : ∀ a : A, a ≠ 0 → IsUnit (algebraMap R F (algebraMap A R a)) := by
    intro a ha
    exact IsLocalization.map_units F
      (⟨algebraMap A R a, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ :
        nonZeroDivisors A)⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))

  let N : Submodule R D :=
    { carrier := {d | ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z)}
      add_mem' := by
        intro d₁ d₂ h₁ h₂ z hz
        obtain ⟨r₁, e₁⟩ := h₁ z hz
        obtain ⟨r₂, e₂⟩ := h₂ z hz
        exact ⟨r₁ + r₂, by rw [map_add, e₁, e₂, add_mul, map_add]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro r d h z hz
        obtain ⟨r₁, e₁⟩ := h z hz
        refine ⟨r * r₁, ?_⟩
        rw [Algebra.smul_def, mul_assoc]
        change _ = τ (algebraMap F D (algebraMap R F r) * (d * z))
        rw [hτm, ← e₁, map_mul] }
  have hmemN : ∀ d, d ∈ N ↔ ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z) := fun d => Iff.rfl
  have h1N : (1 : D) ∈ N := by
    intro z hz
    simpa using hτC z hz

  obtain ⟨c₀, hc₀⟩ := hunit a₀ ha₀
  let S : Submodule R D := Submodule.span R (Set.range fun i => algebraMap F D (↑c₀⁻¹ : F) * x i)
  have hNS : N ≤ S := by
    intro d hd
    have hr : ∀ i, ∃ r : R, algebraMap R F r = τ (y i * d) := by
      intro i
      obtain ⟨r, e⟩ := hd (y i) (hy i)
      exact ⟨r, by rw [e, mul_comm]⟩
    choose r hr using hr
    have hd' : d = ∑ i, r i • (algebraMap F D (↑c₀⁻¹ : F) * x i) := by
      have h := hid d
      have h2 : d = algebraMap F D (↑c₀⁻¹ : F) *
          (GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) := by
        rw [hbase, ← mul_assoc, ← map_mul, ← hc₀, Units.inv_mul, map_one, one_mul]
      rw [h2, ← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, ← hr i]
      change _ = algebraMap F D (algebraMap R F (r i)) * _
      ring
    rw [hd']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSnoeth : IsNoetherian R S :=
    isNoetherian_of_fg_of_noetherian S (Submodule.fg_span (Set.finite_range _))

  intro a ha m hm
  obtain ⟨c, hc⟩ := hunit a ha
  set ξ : D := algebraMap F D (↑c⁻¹ : F) * (m : D) with hξ

  have hξN : ∀ d ∈ N, ξ * d ∈ N := by
    intro d hd z hz
    have hmz : (m : D) * z ∈ C := C.mul_mem m.2 hz
    obtain ⟨r₀, e₀⟩ := hd _ hmz
    have hdiv : ∃ r'' : R, r₀ = algebraMap A R a • r'' := by
      apply hHR a ha r₀
      intro p hp hph
      obtain ⟨u, hu, m', hm'⟩ := hm p hp hph
      have hm'z : (m' : D) * z ∈ C := C.mul_mem m'.2 hz
      obtain ⟨r', e'⟩ := hd _ hm'z
      refine ⟨u, hu, r', ?_⟩
      apply hinj
      have hv := congrArg Subtype.val hm'
      rw [hsmulC, hsmulC, hbase, hbase] at hv
      rw [smul_eq_mul, smul_eq_mul, map_mul, map_mul, e₀, e', ← hτm, ← hτm]
      congr 1
      linear_combination (d * z) * hv
    obtain ⟨r'', e''⟩ := hdiv
    refine ⟨r'', ?_⟩
    have : ξ * d * z = algebraMap F D (↑c⁻¹ : F) * (d * ((m : D) * z)) := by
      rw [hξ]; ring
    rw [this, hτm, ← e₀, e'', smul_eq_mul, map_mul, ← hc, ← mul_assoc, Units.inv_mul, one_mul]
  have hpow : ∀ k : ℕ, ξ ^ k ∈ N := by
    intro k
    induction k with
    | zero => simpa using h1N
    | succ k ih => rw [pow_succ']; exact hξN _ ih
  have hadj : Subalgebra.toSubmodule (Algebra.adjoin R {ξ}) ≤ S := by
    rw [Algebra.adjoin_eq_span]
    refine le_trans ?_ hNS
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hw
    exact hpow k
  have hfg : (Subalgebra.toSubmodule (Algebra.adjoin R {ξ})).FG :=
    isNoetherian_submodule.mp hSnoeth _ hadj
  have hξC : ξ ∈ C :=
    (hmemC ξ).mpr (IsIntegral.of_mem_of_fg _ hfg ξ (Algebra.self_mem_adjoin_singleton R ξ))
  refine ⟨⟨ξ, hξC⟩, Subtype.ext ?_⟩
  rw [hsmulC, hbase]
  change (m : D) = algebraMap F D (algebraMap R F (algebraMap A R a)) * ξ
  rw [hξ, ← mul_assoc, ← map_mul, ← hc, Units.mul_inv, map_one, one_mul]

end GlobalTheory.ClosureHartogs
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosureOverGenericFibre_hartogs : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (τ : D →ₗ[GlobalTheory.LocAcyc.GenFib A R] GlobalTheory.LocAcyc.GenFib A R),
      (∀ c ∈ GlobalTheory.KeyOriginNoeth.closure A R D, ∃ r : R, algebraMap R _ r = τ c) →
    ∀ (a₀ : A), a₀ ≠ 0 → ∀ (n : ℕ) (x y : Fin n → D),
      (∀ i, y i ∈ GlobalTheory.KeyOriginNoeth.closure A R D) →
      (∀ d : D, ∑ i, x i * algebraMap _ D (τ (y i * d)) =
        GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.ClosureHartogs.closure_hart) | (exact GlobalTheory.ClosureHartogs.closure_hart) | (intros; apply GlobalTheory.ClosureHartogs.closure_hart  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_mem_integralClosureOverGenericFibre : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] (s : Finset D),
    ∃ a : A, a ≠ 0 ∧ ∀ d ∈ s,
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) * d ∈ GlobalTheory.KeyOriginNoeth.closure A R D := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure) | (exact GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ClosureData

open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth

section
variable (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]

theorem algebraMap_mem_nonZeroDivisors [Module.Flat A R] {a : A} (ha : a ≠ 0) :
    algebraMap A R a ∈ nonZeroDivisors R := by
  have h : IsSMulRegular R a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx => h ?_
  simp only [Algebra.smul_def, smul_zero]
  rw [mul_comm, mul_zero]; exact hx

theorem genFib_injective [Module.Flat A R] : Function.Injective (algebraMap R (GenFib A R)) := by
  apply IsLocalization.injective (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  rintro _ ⟨a, ha, rfl⟩
  exact algebraMap_mem_nonZeroDivisors A R (nonZeroDivisors.ne_zero ha)

theorem isUnit_genFib {a : A} (ha : a ≠ 0) :
    IsUnit (algebraMap R (GenFib A R) (algebraMap A R a)) :=
  IsLocalization.map_units (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (GenFib A R)
    ⟨algebraMap A R a, ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩⟩
end

section
variable {A R D : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
  [Algebra (GenFib A R) D]

theorem baseHom_apply (r : R) :
    baseHom A R D r = algebraMap (GenFib A R) D (algebraMap R (GenFib A R) r) := rfl

theorem map_mem (σ : D →ₐ[GenFib A R] D) {d : D} (hd : d ∈ closure A R D) :
    σ d ∈ closure A R D := by
  letI := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact IsIntegral.map (σ.restrictScalars R) (show IsIntegral R d from hd)

def restr (σ : D ≃ₐ[GenFib A R] D) :
    letI := closureAlg A R D
    closure A R D ≃ₐ[R] closure A R D :=
  letI := closureAlg A R D
  { toFun := fun c => ⟨σ c.1, map_mem σ.toAlgHom c.2⟩
    invFun := fun c => ⟨σ.symm c.1, map_mem σ.symm.toAlgHom c.2⟩
    left_inv := fun c => Subtype.ext (σ.symm_apply_apply (c : D))
    right_inv := fun c => Subtype.ext (σ.apply_symm_apply (c : D))
    map_mul' := fun c c' => Subtype.ext (map_mul σ (c : D) (c' : D))
    map_add' := fun c c' => Subtype.ext (map_add σ (c : D) (c' : D))
    commutes' := fun r => Subtype.ext (σ.commutes (algebraMap R (GenFib A R) r)) }

@[simp] theorem restr_coe (σ : D ≃ₐ[GenFib A R] D) (c : closure A R D) :
    ((letI := closureAlg A R D; restr σ c : closure A R D) : D) = σ c := rfl

end

section
variable {A R D : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
  [Algebra (GenFib A R) D]

theorem trace_mem (hIC : ∀ f : GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GenFib A R) r = f)
    (hinj : Function.Injective (algebraMap (GenFib A R) D))
    (τ : D →ₗ[GenFib A R] GenFib A R) (q : ℕ) [NeZero q]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[GenFib A R] D))
    (hτ : ∀ d, algebraMap _ D (τ d) = ∑ g, act g d) {c : D} (hc : c ∈ closure A R D) :
    ∃ r : R, algebraMap R (GenFib A R) r = τ c := by
  apply hIC
  letI := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R (GenFib A R) D) hinj]
  show IsIntegral R (algebraMap (GenFib A R) D (τ c))
  rw [hτ]
  exact (sum_mem fun g _ => map_mem (act g).toAlgHom hc : ∑ g, act g c ∈ GlobalTheory.KeyOriginNoeth.closure A R D)

theorem smul_coe (r : R) (c : closure A R D) :
    ((letI := closureAlg A R D; r • c : closure A R D) : D) =
      algebraMap R (GenFib A R) r • (c : D) := by
  letI := closureAlg A R D
  rw [Algebra.smul_def, Algebra.smul_def]; rfl

end

theorem closureData : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [Nontrivial R] [Module.Flat A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    (∀ f : GlobalTheory.LocAcyc.GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r = f) →
    ∀ (q : ℕ) [NeZero q] (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] D)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) D q act →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∃ (act' : Multiplicative (ZMod q) →* (GlobalTheory.KeyOriginNoeth.closure A R D ≃ₐ[R] GlobalTheory.KeyOriginNoeth.closure A R D))
      (T : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] R),
      (∀ c, algebraMap R _ (T c) = ∑ g, act' g c) ∧
      (∃ a : A, a ≠ 0 ∧ ∃ (n : ℕ) (x y : Fin n → GlobalTheory.KeyOriginNoeth.closure A R D),
        ∀ g, ∑ i, x i * act' g (y i) = if g = 1 then algebraMap R _ (algebraMap A R a) else 0) ∧
      GlobalTheory.GoodEtale.TorsionFreeOver A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Algebra.IsIntegral R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Nontrivial (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ _ _ _ hHart hIC q _ D _ _ act hT
  classical
  letI := closureAlg A R D
  obtain ⟨hinj, ⟨τ, hτ⟩, n, x, y, hxy⟩ := GlobalTheory.TorsorTrace.injective_trace_galoisData _ D q act hT
  have hRinj := genFib_injective A R
  have htr : ∀ c ∈ closure A R D, ∃ r : R, algebraMap R (GenFib A R) r = τ c :=
    fun c hc => trace_mem hIC hinj τ q act hτ hc
  haveI : Module.Finite (GenFib A R) D := hT.1
  obtain ⟨a, ha, hmem⟩ := GlobalTheory.T.exists_mul_mem_integralClosureOverGenericFibre A R D (Finset.univ.image x ∪ Finset.univ.image y)
  set b := baseHom A R D (algebraMap A R a) with hbdef
  have hb : ∀ g, act g b = b := fun g => (act g).commutes _
  let x' : Fin n → closure A R D := fun i => ⟨b * x i, hmem _ (by simp)⟩
  let y' : Fin n → closure A R D := fun i => ⟨b * y i, hmem _ (by simp)⟩
  let act' : Multiplicative (ZMod q) →* (closure A R D ≃ₐ[R] closure A R D) :=
    { toFun := fun g => restr (act g)
      map_one' := by ext c; simp
      map_mul' := fun g h => by ext c; simp [map_mul] }
  have hact' : ∀ g c, ((act' g c : closure A R D) : D) = act g c := fun _ _ => rfl
  let Tf : closure A R D → R := fun c => Classical.choose (htr c c.2)
  have hT' : ∀ c, algebraMap R (GenFib A R) (Tf c) = τ c := fun c => Classical.choose_spec (htr c c.2)
  let T : closure A R D →ₗ[R] R :=
    { toFun := Tf
      map_add' := fun c c' => hRinj (by simp [hT'])
      map_smul' := fun r c => hRinj (by
        rw [hT', smul_coe, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul, map_mul, hT']) }
  have key : ∀ g, ∑ i, (x' i : D) * act g (y' i) = b * b * ∑ i, x i * act g (y i) := by
    intro g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show b * x i * act g (b * y i) = _
    rw [map_mul, hb]; ring
  have h1 : ∀ g, ∑ i, (x' i : D) * act g (y' i) = if g = 1 then b * b else 0 := by
    intro g; rw [key, hxy]; split_ifs <;> simp
  have hbb : b * b = baseHom A R D (algebraMap A R (a * a)) := by simp [hbdef, map_mul]
  refine ⟨act', T, ?_, ⟨a * a, mul_ne_zero ha ha, n, x', y', ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro c
    apply Subtype.ext
    show baseHom A R D (Tf c) = _
    rw [baseHom_apply, hT', hτ]
    simp [hact']
  · intro g
    apply Subtype.ext
    split_ifs with hg
    · simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, hact']
      rw [h1, if_pos hg, hbb]
      rfl
    · simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, hact']
      rw [h1, if_neg hg]
      rfl
  · intro a' ha' c hc
    apply Subtype.ext
    have h1 := congrArg Subtype.val hc
    rw [smul_coe, Algebra.smul_def] at h1
    simpa using ((isUnit_genFib A R ha').map (algebraMap (GenFib A R) D)).mul_right_eq_zero.mp h1
  · refine GlobalTheory.T.integralClosureOverGenericFibre_hartogs A R hHart hRinj D τ htr (a * a) (mul_ne_zero ha ha) n
      (fun i => (x' i : D)) (fun i => (y' i : D)) (fun i => (y' i).2) ?_
    intro d
    have e1 : ∀ i, algebraMap (GenFib A R) D (τ ((y' i : D) * d)) = ∑ g, act g (y' i) * act g d := by
      intro i; rw [hτ]; simp [map_mul]
    simp only [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∀ g, ∑ i, (x' i : D) * (act g (y' i) * act g d) =
        (if g = 1 then b * b else 0) * act g d := by
      intro g
      rw [← h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl fun g _ => e2 g]
    simp [hbb]
  · refine ⟨fun c => ?_⟩
    letI := (baseHom A R D).toAlgebra
    let f : closure A R D →ₐ[R] D := { (closure A R D).subtype with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).mp c.2
  · haveI : Nontrivial (GenFib A R) := hRinj.nontrivial
    haveI : Nontrivial D := hinj.nontrivial
    exact ⟨⟨0, 1, fun h => zero_ne_one (α := D) (by simpa using congrArg Subtype.val h)⟩⟩

end GlobalTheory.ClosureData
end
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_zmodTorsor_genericFibre_data : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [Nontrivial R] [Module.Flat A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    (∀ f : GlobalTheory.LocAcyc.GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r = f) →
    ∀ (q : ℕ) [NeZero q] (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] D)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) D q act →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∃ (act' : Multiplicative (ZMod q) →* (GlobalTheory.KeyOriginNoeth.closure A R D ≃ₐ[R] GlobalTheory.KeyOriginNoeth.closure A R D))
      (T : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] R),
      (∀ c, algebraMap R _ (T c) = ∑ g, act' g c) ∧
      (∃ a : A, a ≠ 0 ∧ ∃ (n : ℕ) (x y : Fin n → GlobalTheory.KeyOriginNoeth.closure A R D),
        ∀ g, ∑ i, x i * act' g (y i) = if g = 1 then algebraMap R _ (algebraMap A R a) else 0) ∧
      GlobalTheory.GoodEtale.TorsionFreeOver A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Algebra.IsIntegral R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Nontrivial (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.ClosureData.closureData) | (exact GlobalTheory.ClosureData.closureData) | (intros; apply GlobalTheory.ClosureData.closureData  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

theorem GlobalTheory.GoodEtale.closure_finiteEtale : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    ∀ (q : ℕ), 0 < q → IsUnit (q : A) →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
      GlobalTheory.KeyOriginNoeth.Good A (Localization.AtPrime QA) DA ρ →
      GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A (Localization.AtPrime QA) DA := by
  intro A _ _ _ _ _ _ EA _ _ _ _ _ QA _ hQA ρ hρ hker q hq hqu DA _ _ actA htor hgood
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨hflat, hnoeth, ht, hic⟩ := GlobalTheory.T.genericFibreBase_flat_noetherian_intClosed A EA QA hQA ρ hρ hker
  haveI := hflat
  haveI := hnoeth
  have hHR := GlobalTheory.T.hasHartogsPropertyHeightOnePrimes_of_flat A (Localization.AtPrime QA)
  obtain ⟨act', T, hT, ⟨a, ha, n, x, y, hxy⟩, htf, hHC, hint, hnt⟩ :=
    GlobalTheory.T.integralClosure_zmodTorsor_genericFibre_data A (Localization.AtPrime QA) hHR hic q DA actA htor
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A (Localization.AtPrime QA) DA
  obtain ⟨hEt, s, hs⟩ := hgood
  obtain ⟨O, _, _, hO, hσ⟩ := GlobalTheory.T.exists_faithfullyFlat_algHom_etale_height_one A (Localization.AtPrime QA) (GlobalTheory.KeyOriginNoeth.closure A _ DA)
    ρ hρ _ hker ht hint (fun P _ h => hEt P h) ⟨s, hs⟩
  obtain ⟨hfin, het⟩ := GlobalTheory.T.finiteEtale_of_galois_descent_hartogs A (Localization.AtPrime QA) (GlobalTheory.KeyOriginNoeth.closure A _ DA) O
    (Multiplicative (ZMod q)) act' T hT a ha n x y hxy htf hHC (fun P _ h => hEt P h) hσ
  exact ⟨hfin, het, hnt⟩
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_finiteEtale_originKeyLemma_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    ∀ (q : ℕ), 0 < q → IsUnit (q : A) →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
      GlobalTheory.KeyOriginNoeth.Good A (Localization.AtPrime QA) DA ρ →
      GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A (Localization.AtPrime QA) DA := by
  first | (exact @GlobalTheory.GoodEtale.closure_finiteEtale) | (exact GlobalTheory.GoodEtale.closure_finiteEtale) | (intros; apply GlobalTheory.GoodEtale.closure_finiteEtale  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

open IsLocalRing Polynomial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale :
    ∀ (A R O B : Type) [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] [CommRing B]
    (j : R →+* O) (β : O →+* B) (ψ : _root_.GlobalTheory.LocAcyc.GenFib A R →+* B),
    ψ.comp (algebraMap R (_root_.GlobalTheory.LocAcyc.GenFib A R)) = β.comp j →
    ∀ (D : Type) [CommRing D] [Algebra (_root_.GlobalTheory.LocAcyc.GenFib A R) D],
      Module.Finite (_root_.GlobalTheory.LocAcyc.GenFib A R) D → _root_.GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A R D →
      ∃ σ : D →+* B, σ.comp (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D) = ψ := by
  intro A R O B _ _ _ _ _ _ _ _ _ _ j β ψ hψ D _ _ hfin hE
  letI : Algebra R D := (_root_.GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI : Algebra R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) :=
    _root_.GlobalTheory.KeyOriginNoeth.closureAlg A R D
  obtain ⟨hEfin, hEet, hEnt⟩ := hE
  haveI := hEfin
  haveI := hEet
  haveI := hEnt
  haveI := hfin
  letI : Algebra R O := j.toAlgebra
  haveI : Module.Free R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) := Module.free_of_flat_of_isLocalRing
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := _root_.GlobalTheory.KeyOriginNoeth.closure A R D)
    ⟨RingHom.ker (algebraMap R (ResidueField O)), RingHom.ker_isPrime _⟩
  have hq' : Ideal.comap (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D)) q.asIdeal =
      RingHom.ker (algebraMap R (ResidueField O)) := congrArg PrimeSpectrum.asIdeal hq
  obtain ⟨φ₀⟩ := _root_.GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed q.asIdeal hq'
  obtain ⟨φ, -⟩ := (_root_.GlobalTheory.EtaleHensel.bijective_residue_comp R
    (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) O).2 φ₀
  letI : Algebra (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) D :=
    (_root_.GlobalTheory.KeyOriginNoeth.closure A R D).subtype.toAlgebra
  haveI : IsScalarTower R (_root_.GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq' rfl
  have hloc : IsLocalization ((Algebra.algebraMapSubmonoid R (nonZeroDivisors A)).map
      (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D))) D := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩⟩
      exact (IsLocalization.map_units (_root_.GlobalTheory.LocAcyc.GenFib A R) ⟨s, hs⟩).map
        (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D)
    · intro d
      obtain ⟨⟨m, hm⟩, hmint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) d
        (Algebra.IsIntegral.isIntegral (R := _root_.GlobalTheory.LocAcyc.GenFib A R) d)
      refine ⟨⟨⟨m • d, hmint⟩, ⟨algebraMap R _ m, m, hm, rfl⟩⟩, ?_⟩
      show d * algebraMap R D m = m • d
      rw [Algebra.smul_def, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [Subtype.ext hxy]⟩
  have hσ : ∀ r : R, β (φ (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) r)) =
      ψ (algebraMap R (_root_.GlobalTheory.LocAcyc.GenFib A R) r) := by
    intro r
    rw [φ.commutes]
    exact (RingHom.congr_fun hψ r).symm
  have hunits : ∀ y : (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)).map
      (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D)), IsUnit ((β.comp φ.toRingHom) y) := by
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    show IsUnit (β (φ (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) s)))
    rw [hσ]
    exact (IsLocalization.map_units (_root_.GlobalTheory.LocAcyc.GenFib A R) ⟨s, hs⟩).map ψ
  refine ⟨IsLocalization.lift (S := D) hunits, ?_⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  ext r
  have hr : algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A R) D (algebraMap R _ r) =
      algebraMap (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) D
        (algebraMap R (_root_.GlobalTheory.KeyOriginNoeth.closure A R D) r) := rfl
  simp only [RingHom.comp_apply]
  rw [hr, IsLocalization.lift_eq]
  exact hσ r

end GlobalTheory.KeyOriginNoeth
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian : ∀ (A R O B : Type) [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing O] [IsLocalRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] [CommRing B]
    (j : R →+* O) (β : O →+* B) (ψ : GlobalTheory.LocAcyc.GenFib A R →+* B),
    ψ.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = β.comp j →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D],
      Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D → GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A R D →
      ∃ σ : D →+* B, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D) = ψ := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale) | (exact GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_point_of_closureFiniteEtale  <;> assumption)
end

section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginNoeth

theorem torsor_point_of_essFiniteType : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  obtain ⟨A', _, _, _, _, _, _, EA', _, _, _, _, _, QA', _, hQ', hq', ρ', hρ1, hρ2, jA', ψA', hψ', DA', _, _,
    actA', htor', hgood', β, h, hβ1, hβ2⟩ :=
    GlobalTheory.T.strictHenselisation_enlarge_good_at_origin T O hT P φ hφ hsh hP q hq0 hqT A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htor
  have hce := GlobalTheory.T.integralClosure_finiteEtale_originKeyLemma_essFiniteType A' EA' QA' hQ' ρ' hρ1 hρ2 q hq0 hq' DA' actA' htor' hgood'
  haveI : HenselianLocalRing O := hsh.1
  haveI : IsSepClosed (ResidueField O) := hsh.2.1
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian A' (Localization.AtPrime QA') O (GlobalTheory.LocAcyc.GenFib T O) jA'
    (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)) ψA' hψ' DA' htor'.1 hce
  refine ⟨σ'.comp h, ?_⟩
  rw [RingHom.comp_assoc, hβ2, ← RingHom.comp_assoc, hσ', hβ1]

end GlobalTheory.KeyOriginNoeth
end
