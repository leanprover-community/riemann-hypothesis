import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfEtaleOfIsIndEtale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealExtensionPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

section
open IsLocalRing Polynomial

namespace GlobalTheory.NormalStrictHens

theorem exists_mem_finset {S : Type} [CommRing S] {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R) (hcov : ∀ x : S, ∃ i, x ∈ R i)
    (s : Finset S) : ∃ i, ∀ x ∈ s, x ∈ R i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert x s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hmono hjk hj
    · exact hmono hik (hi y hy)

theorem isDomain_of_directed {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i)) : IsDomain S := by
  classical
  haveI : NoZeroDivisors S := ⟨fun {x y} hxy => by
    obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov {x, y}
    haveI := hdom k
    have hx : x ∈ R k := hk x (by simp)
    have hy : y ∈ R k := hk y (by simp)
    have h : (⟨x, hx⟩ : R k) * ⟨y, hy⟩ = 0 := Subtype.ext hxy
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)⟩
  exact NoZeroDivisors.to_isDomain S

theorem isIntegrallyClosed_of_directed {S : Type} [CommRing S] [IsDomain S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i))
    (hic : ∀ i, IsIntegrallyClosed (R i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨f, hfm, hf⟩ := hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors S) x
  obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov (insert a (insert (b : S) f.coeffs))
  haveI := hdom k
  haveI := hic k
  have ha : a ∈ R k := hk a (by simp)
  have hb : (b : S) ∈ R k := hk b (by simp)
  have hcf : (f.coeffs : Set S) ⊆ R k := fun c hc =>
    hk c (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
  have hgm : (f.toSubring (R k) hcf).Monic := (monic_toSubring f (R k) hcf).2 hfm
  have hgf : (f.toSubring (R k) hcf).map (R k).subtype = f := map_toSubring f (R k) hcf
  have hinj : Function.Injective ((algebraMap S (FractionRing S)).comp (R k).subtype) :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (R k) →+* FractionRing S := IsFractionRing.lift hinj
  have hφ : ∀ r : R k, φ (algebraMap (R k) (FractionRing (R k)) r) = algebraMap S (FractionRing S) r :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  have hb0 : (⟨b, hb⟩ : R k) ∈ nonZeroDivisors (R k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero b (congrArg Subtype.val h)
  have hφy : φ (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) =
      IsLocalization.mk' (FractionRing S) a b := by
    rw [IsFractionRing.lift_mk', IsFractionRing.mk'_eq_div]
    rfl
  have hcomp : φ.comp (algebraMap (R k) (FractionRing (R k))) =
      (algebraMap S (FractionRing S)).comp (R k).subtype := by
    ext r
    exact hφ r
  have hy : IsIntegral (R k) (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) := by
    refine ⟨f.toSubring (R k) hcf, hgm, ?_⟩
    apply φ.injective
    rw [map_zero, hom_eval₂, hφy, hcomp, ← eval₂_map, hgf]
    exact hf
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (R k))).1 inferInstance hy
  refine ⟨c, ?_⟩
  rw [← hφ, hc, hφy]

end GlobalTheory.NormalStrictHens

namespace GlobalTheory

open GlobalTheory.NormalStrictHens in

theorem exists_strictlyHenselian_normal_between : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  intro T _ _ _ hT A _ _ _ _ _ i hi
  haveI := hi
  obtain ⟨hThens, hTac, -⟩ :=
    GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  haveI := hThens
  haveI := hTac
  obtain ⟨S, _, _, _, hloc, hsc, -, hmax, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation A (SeparableClosure (ResidueField A))
  haveI := hsc
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S) :=
    GlobalTheory.StrictHensUnion.indEtale_of_directed_union A S ι Si hmono hcov fun k => by
      obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
      exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
        (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale A B q.primeCompl)
  have hsh : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap A S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  haveI : IsNoetherianRing S := GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt A S hind
  have hdi : ∀ k, IsDomain (Si k).toSubring ∧ IsIntegrallyClosed (Si k).toSubring := fun k => by
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
    obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A B q
    let e' : Localization.AtPrime q ≃+* (Si k).toSubring :=
      e.toRingEquiv.trans
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl }
    exact ⟨e'.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e'⟩
  have hmono' : Monotone fun k => (Si k).toSubring := fun _ _ h => hmono h
  haveI : IsDomain S := isDomain_of_directed _ hmono' hcov fun k => (hdi k).1
  have hic : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_directed _ hmono' hcov (fun k => (hdi k).1) fun k => (hdi k).2
  obtain ⟨α, hα⟩ :=
    GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation (algebraMap A S) hsh i
  have hle : maximalIdeal S ≤ (maximalIdeal T).comap α := by
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hα]
    intro a ha
    exact map_nonunit i a ha
  refine ⟨S, inferInstance, inferInstance, inferInstance, hsc, inferInstance, hic,
    algebraMap A S, α, hα, ⟨fun s hs => ?_⟩⟩
  by_contra h
  exact (mem_maximalIdeal _).1 (hle ((mem_maximalIdeal s).2 h)) hs

end GlobalTheory
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  first | (exact @GlobalTheory.exists_strictlyHenselian_normal_between) | (exact GlobalTheory.exists_strictlyHenselian_normal_between) | (intros; apply GlobalTheory.exists_strictlyHenselian_normal_between  <;> assumption)
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localStage_tensor_polynomial_origin : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  first | (exact @GlobalTheory.LocalStage.localStage) | (exact GlobalTheory.LocalStage.localStage) | (intros; apply GlobalTheory.LocalStage.localStage  <;> assumption)
end

section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GoodStageOrigin

theorem local_props (A' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    (E : Type) [CommRing E] [Algebra (Polynomial A') E] [Algebra.Etale (Polynomial A') E]
    (Q : Ideal E) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) ∧
      IsIntegrallyClosed (Localization.AtPrime Q) ∧
      (letI : Algebra A' (Localization.AtPrime Q) :=
        ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
       Module.Flat A' (Localization.AtPrime Q)) := by
  haveI : IsIntegrallyClosed (Polynomial A') := by
    haveI := GlobalTheory.isIntegrallyClosed_mvPolynomial_fin A' 1
    exact IsIntegrallyClosed.of_equiv
      ((MvPolynomial.renameEquiv A' (Equiv.equivPUnit.{1, 1} (Fin 1))).trans (MvPolynomial.pUnitAlgEquiv.{0, 0} A')).toRingEquiv
  obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A') E Q
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing (Polynomial A') E
  refine ⟨h1, IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance, h2, ?_⟩
  letI : Algebra A' (Localization.AtPrime Q) :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
  haveI : IsScalarTower A' (Polynomial A') (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat (Polynomial A') E := inferInstance
  haveI : Module.Flat E (Localization.AtPrime Q) := IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) := Module.Flat.trans (Polynomial A') E _
  exact Module.Flat.trans A' (Polynomial A') _

theorem good_stage : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA sA hsA
  have hO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T := by
    haveI : IsLocalHom φ := hsh.2.2.1
    rw [← hφ, ← Ideal.comap_comap, GlobalTheory.comap_maximalIdeal_of_localHom_strictHens φ, ← hP]
    first
      | exact Localization.AtPrime.comap_maximalIdeal (Localization.AtPrime P) P
      | exact Localization.AtPrime.comap_maximalIdeal
      | simpa [Ideal.under] using Localization.AtPrime.comap_maximalIdeal (Localization.AtPrime P) P
  obtain ⟨A', _, _, _, _, _, _, ι, α, hια, hα⟩ := GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal T hT A i hil
  obtain ⟨E', _, _, _, Q', _, hQ', β, γ, h1, h2, h3⟩ :=
    GlobalTheory.T.exists_localStage_tensor_polynomial_origin T O hO A i hil EA QA hQA jA hjA A' ι α hια hα
  obtain ⟨hd, hn, hic, hfl⟩ := local_props A' E' Q'
  letI alg : Algebra A' (Localization.AtPrime Q') :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).toAlgebra
  refine ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, Localization.AtPrime Q',
    inferInstance, hd, inferInstance, hn, hic, alg, hfl, ι, α, β, γ, ?_, h2, h3, ?_, ?_⟩
  · have e : algebraMap A (Localization.AtPrime QA) =
        (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C := by
      rw [IsScalarTower.algebraMap_eq A EA (Localization.AtPrime QA),
        IsScalarTower.algebraMap_eq A (Polynomial A) EA, Polynomial.algebraMap_eq,
        IsScalarTower.algebraMap_eq (Polynomial A) EA (Localization.AtPrime QA)]
      rfl
    rw [e]
    exact h1
  · intro h
    apply hsA
    apply hi
    rw [map_zero, ← hια, RingHom.comp_apply, h, map_zero]
  · intro 𝔭 _ _ _
    exact GlobalTheory.T.origin_ideal_extension_prime A' 𝔭 E' Q' hQ'

end GlobalTheory.GoodStageOrigin
end
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  first | (exact @GlobalTheory.GoodStageOrigin.good_stage) | (exact GlobalTheory.GoodStageOrigin.good_stage) | (intros; apply GlobalTheory.GoodStageOrigin.good_stage <;> assumption)
end

section
open IsLocalRing

namespace GlobalTheory

theorem exists_mem_submonoid_dvd_mul_of_forall_height_eq_one :
    ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  intro B _ _ _ _ S _ x y hy h
  by_contra! hS
  set M := B ⧸ Ideal.span {y}
  set N : Submodule B M := B ∙ (Ideal.Quotient.mk (Ideal.span {y}) x)
  have hmem : ∀ r : B, r ∈ Module.annihilator B N ↔ y ∣ r * x := by
    intro r
    change r ∈ Submodule.annihilator N ↔ _
    rw [Submodule.mem_annihilator_span_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  set I := Module.annihilator B N
  have hdisj : Disjoint (S : Set B) (I : Set B) := by
    rw [Set.disjoint_left]
    intro u hu huI
    exact hS u hu ((hmem u).mp huI)
  obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint I S hdisj.symm
  obtain ⟨P', hP'min, hP'P⟩ := Ideal.exists_minimalPrimes_le hIP
  have hass : P' ∈ associatedPrimes B N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B N hP'min
  have hass' : P' ∈ associatedPrimes B M :=
    associatedPrimes.subset_of_injective Subtype.val_injective (f := N.subtype) hass
  obtain ⟨hpr, h1, hyP⟩ := (mem_associatedPrimes_iff_height_eq_one hy).mp hass'
  obtain ⟨t, htQ, ht⟩ := h P' hpr h1 hyP (hPS.symm.mono_right hP'P)
  exact htQ (hP'min.1.2 ((hmem t).mpr ht))

end GlobalTheory
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one : ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  first | (exact @GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (exact GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (intros; apply GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one <;> assumption)
end

section
open IsLocalRing

namespace GlobalTheory

theorem exists_notMem_dvd_mul_of_algebraMap_dvd {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]
    {a b : B}
    (h : algebraMap B (Localization.AtPrime Q) a ∣ algebraMap B (Localization.AtPrime Q) b) :
    ∃ t ∉ Q, a ∣ t * b := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalization.surj Q.primeCompl y
  have e : algebraMap B (Localization.AtPrime Q) (b * s) =
      algebraMap B (Localization.AtPrime Q) (a * z) := by
    rw [map_mul, map_mul, hy, mul_assoc, hs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists Q.primeCompl _).mp e
  refine ⟨c * s, Q.primeCompl.mul_mem c.2 s.2, c * z, ?_⟩
  linear_combination hc

theorem exists_locally_associated_algebraMap_of_height_eq_one (A' B' : Type) [CommRing A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    (𝔭 : Ideal A') (hQ : (𝔭.map (algebraMap A' B')).IsPrime)
    (h1 : (𝔭.map (algebraMap A' B')).height = 1) (c : B') (hc : c ≠ 0) :
    ∃ j : A', (∃ t ∉ 𝔭.map (algebraMap A' B'), c ∣ t * algebraMap A' B' j) ∧
      (∃ t ∉ 𝔭.map (algebraMap A' B'), algebraMap A' B' j ∣ t * c) := by
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime (𝔭.map (algebraMap A' B'))) :=
    isDiscreteValuationRing_of_height_eq_one _ h1 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (𝔭.map (algebraMap A' B')))
  have hm : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  obtain ⟨p, hp𝔭, hp⟩ : ∃ p ∈ 𝔭, ¬ ϖ ^ 2 ∣
      algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (algebraMap A' B' p) := by
    by_contra! H
    have hle : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) ≤
        Ideal.span {ϖ ^ 2} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact H q hq
    have hmem : ϖ ∈ Ideal.span {ϖ ^ 2} := hle (hm ▸ Ideal.mem_span_singleton_self ϖ)
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨r, ?_⟩
    apply mul_left_cancel₀ hϖ.ne_zero
    rw [mul_one]
    linear_combination -hr
  have hxm : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (algebraMap A' B' p) ∈ maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hp𝔭)
  have hx0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (algebraMap A' B' p) ≠ 0 := fun h => hp (h ▸ dvd_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hn : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at hu
      exact (mem_maximalIdeal _).mp hxm (hu ▸ u.isUnit)
    · rfl
    · exfalso
      apply hp
      rw [hu]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  subst hn
  have hc0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c ≠ 0 := by
    intro h
    apply hc
    apply IsLocalization.injective (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (𝔭.map (algebraMap A' B')).primeCompl_le_nonZeroDivisors
    rw [h, map_zero]
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hass : Associated (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c)
      (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
        (algebraMap A' B' (p ^ m))) := by
    rw [map_pow, map_pow, hu, hv, pow_one, mul_pow]
    exact (associated_unit_mul_left _ _ v.isUnit).trans
      (associated_unit_mul_left _ _ (u.isUnit.pow m)).symm
  exact ⟨p ^ m, exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.dvd,
    exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.symm.dvd⟩

end GlobalTheory
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_prime_associate : ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [IsDomain B'] [IsNoetherianRing B']
    [IsIntegrallyClosed B'] [Algebra A' B'] (𝔭 : Ideal A'), (𝔭.map (algebraMap A' B')).IsPrime →
    (𝔭.map (algebraMap A' B')).height = 1 → ∀ c : B', c ≠ 0 →
    ∃ j : A', (∃ t ∉ 𝔭.map (algebraMap A' B'), c ∣ t * algebraMap A' B' j) ∧
      (∃ t ∉ 𝔭.map (algebraMap A' B'), algebraMap A' B' j ∣ t * c) := by
  first | (exact @GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one) | (exact GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one) | (intros; apply GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one <;> assumption)
end

section
open IsLocalRing Polynomial

namespace GlobalTheory.DivDescent

theorem colonStep : ∀ (A' B' : Type) [CommRing A'] [IsNoetherianRing A'] [CommRing B'] [Algebra A' B']
    [Module.Flat A' B'] (b c : B') (s : A'), b * c = algebraMap A' B' s →
    (∀ x : A', (∀ j : A', c ∣ algebraMap A' B' j → ∃ a : A', x * j = s * a) →
      b ∣ algebraMap A' B' x) →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  intro A' B' _ _ _ _ _ b c s hbc h
  have hφ : (algebraMap A' B').Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hle : (Ideal.span {s}).colon (((Ideal.span {c}).comap (algebraMap A' B') : Ideal A') : Set A') ≤
      (Ideal.span {b}).comap (algebraMap A' B') := by
    intro x hx
    rw [Submodule.mem_colon] at hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply h x
    intro j hj
    have := hx j (by rw [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_span_singleton]; exact hj)
    rw [smul_eq_mul, Ideal.mem_span_singleton] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by rw [ha]⟩
  refine Ideal.map_mono hle ?_
  rw [GlobalTheory.ideal_map_colon_eq_of_flat (algebraMap A' B') hφ, Submodule.mem_colon]
  intro y hy
  have hy' : y ∈ Ideal.span {c} := Ideal.map_comap_le hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.1 hy'
  rw [Ideal.map_span, Set.image_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  exact ⟨z, by rw [← hbc, mul_assoc]⟩

theorem primeDescent : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [CommRing B']
    [IsDomain B'] [IsNoetherianRing B'] [Algebra A' B'] [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ Q : Ideal B', Q.IsPrime → Q.height = 1 → algebraMap A' B' s ∈ Q →
    (Q.comap (algebraMap A' B')).height = 1 ∧
      (Q.comap (algebraMap A' B')).map (algebraMap A' B') = Q := by
  intro A' B' _ _ _ _ _ _ _ _ s hs hpr Q hQ hQ1 hsQ
  haveI : Algebra.HasGoingDown A' B' := Algebra.HasGoingDown.of_flat
  haveI hPp : (Q.comap (algebraMap A' B')).IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver (Q.comap (algebraMap A' B')) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.comap (algebraMap A' B')) Q
  have hle1 : (Q.comap (algebraMap A' B')).height ≤ 1 := by rw [← hQ1, h]; exact le_self_add
  have h1 : (Q.comap (algebraMap A' B')).height = 1 := by
    refine le_antisymm hle1 ?_
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hb
    have : s ∈ Q.comap (algebraMap A' B') := hsQ
    rw [hb, Ideal.mem_bot] at this
    exact hs this
  refine ⟨h1, ?_⟩
  haveI hP : ((Q.comap (algebraMap A' B')).map (algebraMap A' B')).IsPrime := hpr _ hPp h1 hsQ
  have hle : (Q.comap (algebraMap A' B')).map (algebraMap A' B') ≤ Q := Ideal.map_comap_le
  by_contra hne
  have hlt := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hQ1] at hlt
  have h0 : ((Q.comap (algebraMap A' B')).map (algebraMap A' B')).height = 0 :=
    ENat.lt_one_iff_eq_zero.mp hlt
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  have hm : algebraMap A' B' s ∈ (Q.comap (algebraMap A' B')).map (algebraMap A' B') :=
    Ideal.mem_map_of_mem _ hsQ
  rw [h0, Ideal.mem_bot] at hm
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B')
    (mem_nonZeroDivisors_of_ne_zero hs)
  have h2 : s • (1 : B') = s • (0 : B') := by
    rw [Algebra.smul_def, mul_one, smul_zero]; exact hm
  exact one_ne_zero (hreg h2)

theorem divisor_descent : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A']
    [IsIntegrallyClosed A'] [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B']
    [Algebra A' B'] [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  intro A' B' _ _ _ _ _ _ _ _ _ _ s hs hpr b c hbc
  have hinj : ∀ a : A', a ≠ 0 → algebraMap A' B' a ≠ 0 := by
    intro a ha h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B')
      (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : a • (1 : B') = a • (0 : B') := by
      rw [Algebra.smul_def, mul_one, smul_zero]; exact h0
    exact one_ne_zero (hreg h1)
  have hb0 : b ≠ 0 := by rintro rfl; exact hinj s hs (by rw [← hbc, zero_mul])
  have hc0 : c ≠ 0 := by rintro rfl; exact hinj s hs (by rw [← hbc, mul_zero])
  have hloc : ∀ Q : Ideal B', Q.IsPrime → Q.height = 1 → b ∈ Q →
      ∃ j : A', c ∣ algebraMap A' B' j ∧ ∃ t ∉ Q, algebraMap A' B' j ∣ t * c := by
    intro Q hQ hQ1 hbQ
    have hsQ : algebraMap A' B' s ∈ Q := by rw [← hbc]; exact Q.mul_mem_right c hbQ
    obtain ⟨h𝔭1, h𝔭Q⟩ := primeDescent A' B' s hs hpr Q hQ hQ1 hsQ
    obtain ⟨j₀, ⟨t₁, ht₁, hj₁⟩, ⟨t₂, ht₂, hj₂⟩⟩ :=
      GlobalTheory.T.height_one_prime_associate A' B' (Q.comap (algebraMap A' B')) (by rw [h𝔭Q]; exact hQ) (by rw [h𝔭Q]; exact hQ1) c hc0
    rw [h𝔭Q] at ht₁ ht₂
    have hS0 : (0 : B') ∉ (Q.comap (algebraMap A' B')).primeCompl.map (algebraMap A' B') := by
      intro h0
      obtain ⟨u', hu', h⟩ := Submonoid.mem_map.1 h0
      by_cases hu0 : u' = 0
      · exact hu' (hu0 ▸ (Q.comap (algebraMap A' B')).zero_mem)
      · exact hinj u' hu0 h
    obtain ⟨u, huS, hu⟩ := GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one B' ((Q.comap (algebraMap A' B')).primeCompl.map (algebraMap A' B'))
      hS0 (algebraMap A' B' j₀) c hc0 (by
        intro Q' hQ' hQ'1 hcQ' hdisj
        have hsQ' : algebraMap A' B' s ∈ Q' := by rw [← hbc]; exact Q'.mul_mem_left b hcQ'
        obtain ⟨h𝔭'1, h𝔭'Q'⟩ := primeDescent A' B' s hs hpr Q' hQ' hQ'1 hsQ'
        have hle : Q'.comap (algebraMap A' B') ≤ Q.comap (algebraMap A' B') := by
          intro x hx
          by_contra hx𝔭
          exact Set.disjoint_left.1 hdisj (Submonoid.mem_map_of_mem (algebraMap A' B') hx𝔭) hx
        have heq : Q'.comap (algebraMap A' B') = Q.comap (algebraMap A' B') := by
          by_contra hne
          have := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hle hne)
          rw [h𝔭'1, h𝔭1] at this
          exact lt_irrefl _ this
        have hQQ : Q' = Q := by rw [← h𝔭'Q', heq, h𝔭Q]
        subst hQQ
        exact ⟨t₁, ht₁, hj₁⟩)
    obtain ⟨u', hu', rfl⟩ := Submonoid.mem_map.1 huS
    refine ⟨u' * j₀, by rw [map_mul]; exact hu, algebraMap A' B' u' * t₂, ?_, ?_⟩
    · intro hm
      rcases hQ.mem_or_mem hm with h | h
      · exact hu' h
      · exact ht₂ h
    · rw [map_mul, mul_assoc]; exact mul_dvd_mul_left _ hj₂
  apply colonStep A' B' b c s hbc
  intro x hx
  obtain ⟨u, hu, hdiv⟩ := GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one B' ⊥ (by simp) (algebraMap A' B' x) b hb0 (by
    intro Q hQ hQ1 hbQ _
    obtain ⟨j, hcj, t, htQ, z, hz⟩ := hloc Q hQ hQ1 hbQ
    obtain ⟨a, ha⟩ := hx j hcj
    refine ⟨t, htQ, ?_⟩
    have hj0 : algebraMap A' B' j ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hz
      rcases mul_eq_zero.1 hz with h | h
      · exact htQ (h ▸ Q.zero_mem)
      · exact hc0 h
    have hx' : algebraMap A' B' x * algebraMap A' B' j = b * c * algebraMap A' B' a := by
      rw [← map_mul, ha, map_mul, hbc]
    refine ⟨algebraMap A' B' a * z, mul_left_cancel₀ hj0 ?_⟩
    linear_combination t * hx' + b * algebraMap A' B' a * hz)
  rw [Submonoid.mem_bot] at hu
  subst hu
  simpa using hdiv

end GlobalTheory.DivDescent
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_descent_flat_normal_domains : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  first | (exact @GlobalTheory.DivDescent.divisor_descent) | (exact GlobalTheory.DivDescent.divisor_descent) | (intros; apply GlobalTheory.DivDescent.divisor_descent <;> assumption)
end

section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnitsNoeth

theorem exists_unit_of_mem_map_comap {A' B' : Type} [CommRing A'] [CommRing B'] [IsDomain B']
    [IsLocalRing B'] (f : A' →+* B') (b : B')
    (h : b ∈ ((Ideal.span {b}).comap f).map f) : ∃ (d : A') (w : B'ˣ), b = f d * w := by
  by_cases hb : b = 0
  · exact ⟨0, 1, by simp [hb]⟩
  by_contra hne
  push_neg at hne
  have hle : ((Ideal.span {b}).comap f).map f ≤ Ideal.span {b} * maximalIdeal B' := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hd
    obtain ⟨z, hz⟩ := hd
    rw [Ideal.mem_comap, hz]
    by_cases hzu : IsUnit z
    · exact absurd (by rw [hz]; exact (Units.mul_inv_cancel_right b hzu.unit).symm) (hne d hzu.unit⁻¹)
    · exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self b) ((mem_maximalIdeal z).2 hzu)
  obtain ⟨m, hm, hbm⟩ := (Ideal.mem_span_singleton_mul).1 (hle h)
  have h1 : m = 1 := by
    have : b * (m - 1) = 0 := by rw [mul_sub, hbm, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hb
    · exact sub_eq_zero.1 h0
  exact (mem_maximalIdeal m).1 hm (h1 ▸ isUnit_one)

theorem divConst_origin_noeth : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA
    bA cA sA hs hbc
  obtain ⟨A', _, _, _, _, B', _, _, _, _, _, _, _, ι, α, β, γ, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin T O hT P φ hφ hsh hP A i hi hil EA QA hQA jA hjA sA hs
  have hbc' : β bA * β cA = algebraMap A' B' (ι sA) := by
    have e := congrArg (fun g => g sA) h1
    simp only [RingHom.comp_apply] at e
    rw [e, ← hbc, map_mul]
  have hmem := GlobalTheory.T.divisor_descent_flat_normal_domains A' B' (ι sA) h4 h5 (β bA) (β cA) hbc'
  obtain ⟨d, w, hdw⟩ := exists_unit_of_mem_map_comap (algebraMap A' B') (β bA) hmem
  have e3 := congrArg (fun g => g d) h3
  simp only [RingHom.comp_apply] at e3
  refine ⟨α d, Units.map γ.toMonoidHom w, ?_⟩
  rw [← h2, RingHom.comp_apply, hdw, map_mul, e3]
  rfl

end GlobalTheory.VertUnitsNoeth
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divConst_origin_noeth_alt : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  first | (exact @GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (exact GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (intros; apply GlobalTheory.VertUnitsNoeth.divConst_origin_noeth <;> assumption)
end
