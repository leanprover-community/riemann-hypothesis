import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBundlesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PChartBundlesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PChartGlue
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PClearDenominators
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericGerm
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueBundles
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueModulesStar
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PInvOpenInside
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PInvOpenInsideRat
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PPullbackFaithful
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PRatLocalAffine
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundle
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundleNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullbackFaithful
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsDescendHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericPullInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadLocal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsBasisIsoFree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleLocal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.GenericImageEqGermImage
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.NonemptyPullbackIsoIff
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.SpreadIsoModelIff

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem GenericGermInjective.proof : GenericGermInjective.Statement := by
  intro X _ E hE U hU
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext ⟨E.presheaf, E.isSheaf⟩ U s 0 fun x hx => ?_
  change E.presheaf.germ U x hx s = E.presheaf.germ U x hx 0
  rw [map_zero]
  obtain ⟨Ux, -, hxUx, n, b, hb⟩ := hE x
  let V : X.Opens := U ⊓ Ux
  have hxV : x ∈ V := ⟨hx, hxUx⟩
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  let iVU : V ⟶ U := homOfLE inf_le_left
  let sV := E.presheaf.map iVU.op s
  obtain ⟨r, hr⟩ := (hb V inf_le_right).2 sV
  have hr0 : ∀ i, r i = 0 := by
    have h1 : E.presheaf.germ V (genericPoint X) hηV sV = E.presheaf.germ U (genericPoint X) hU 0 := by
      rw [TopCat.Presheaf.germ_res_apply, hs, map_zero]
    obtain ⟨W, hηW, iWV, iWU, e⟩ := E.presheaf.germ_eq (genericPoint X) hηV hU sV 0 h1
    have hWUx : W ≤ Ux := iWV.le.trans inf_le_right
    have key : (fun i => X.presheaf.map iWV.op (r i)) = 0 := by
      apply (hb W hWUx).1
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      rw [map_zero] at e
      rw [← e, ← hr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    intro i
    apply germ_injective_of_isIntegral X (U := V) (genericPoint X) hηV
    rw [map_zero, ← X.presheaf.germ_res_apply iWV (genericPoint X) hηW, congrFun key i,
      Pi.zero_apply, map_zero]
  have hsV : sV = 0 := by
    rw [← hr]
    simp [hr0]
  rw [← TopCat.Presheaf.germ_res_apply E.presheaf iVU x hxV s]
  change E.presheaf.germ V x hxV sV = 0
  rw [hsV, map_zero]

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open AlgebraicGeometry TopologicalSpace

namespace PrimeOpensCover

lemma not_mem_of_isCoprime {P : Ideal ℤ} (hP : P ≠ ⊤) {a b : ℤ} (h : IsCoprime a b)
    (ha : a ∈ P) : b ∉ P := by
  intro hb
  obtain ⟨u, v, huv⟩ := h
  exact hP ((Ideal.eq_top_iff_one P).mpr (huv ▸ P.add_mem (P.mul_mem_left u ha) (P.mul_mem_left v hb)))

lemma mem_of_dvd_mem {P : Ideal ℤ} {a b : ℤ} (h : a ∣ b) (ha : a ∈ P) : b ∈ P := by
  obtain ⟨c, rfl⟩ := h
  exact P.mul_mem_right c ha

lemma exists_mem_of_primeProd_mem {P : Ideal ℤ} [P.IsPrime] {S : Finset Nat.Primes}
    (h : primeProd S ∈ P) : ∃ r ∈ S, ((r : ℕ) : ℤ) ∈ P :=
  Ideal.IsPrime.prod_mem_iff.mp h

theorem proof : PrimeOpensCover.Statement := by
  intro X f S mp hcop hdvd
  refine ⟨?_, fun p hp q hq hpq => ?_⟩
  · refine top_le_iff.mp fun x _ => ?_
    let P : Ideal ℤ := (f.base x).asIdeal
    have : P.IsPrime := (f.base x).isPrime
    rw [Opens.mem_sup]
    by_cases hm : primeProd S ∈ P
    · obtain ⟨r, hr, hrP⟩ := exists_mem_of_primeProd_mem hm
      right
      rw [Opens.mem_iSup]
      refine ⟨r, ?_⟩
      rw [Opens.mem_iSup]
      refine ⟨hr, ?_⟩
      rw [mem_invOpen]
      exact not_mem_of_isCoprime (Ideal.IsPrime.ne_top ‹_›)
        ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp r.2)).mpr (hcop r hr)) hrP
    · left
      exact hm
  · have hm : ∀ x : X, x ∈ invOpen f (mp p) ⊓ invOpen f (mp q) → x ∈ invOpen f (primeProd S) := by
      intro x hx
      obtain ⟨hxp, hxq⟩ := hx
      replace hxp : mp p ∉ (f.base x).asIdeal := hxp
      replace hxq : mp q ∉ (f.base x).asIdeal := hxq
      rw [mem_invOpen]
      let P : Ideal ℤ := (f.base x).asIdeal
      have : P.IsPrime := (f.base x).isPrime
      intro hmem
      obtain ⟨r, hr, hrP⟩ := exists_mem_of_primeProd_mem (P := P) hmem
      by_cases hrp : r = p
      · subst hrp
        exact hxq (mem_of_dvd_mem (hdvd q hq r hr hpq) hrP)
      · exact hxp (mem_of_dvd_mem (hdvd p hp r hr hrp) hrP)
    refine ⟨fun x hx => hm x hx, fun x hx => ?_⟩
    have h1 := hm x hx
    obtain ⟨hxp, _⟩ := hx
    replace hxp : mp p ∉ (f.base x).asIdeal := hxp
    rw [mem_invOpen] at h1 ⊢
    have : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
    intro hmul
    rcases Ideal.IsPrime.mem_or_mem ‹_› hmul with h | h
    · exact h1 h
    · exact hxp h

end PrimeOpensCover

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadHomInj.proof (h₁ : GenericSectionsInj.Statement)
    (h₂ : PullbackFaithful.Statement.{0}) : SpreadHomInj.Statement := by
  intro X f _ _ a ha F G hF hG
  obtain ⟨m, hm, H⟩ := h₁ X f
  refine ⟨m, hm, fun n hn hmn ψ₁ ψ₂ e => ?_⟩
  have hk : IsUnit (((a : ℤ) * n : ℤ) : ℚ) := isUnit_intCast_rat _ (by positivity)
  have hG' : IsVectorBundle
      ((Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G) :=
    hG.pullback_of_isOpenImmersion _
  refine h₂ _ _ (toInvOpen f ℚ ((a : ℤ) * n) hk)
    (H _ hk (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _)) _ _ hG' ψ₁ ψ₂ ?_
  unfold pullbackHomAlong at e
  rwa [cancel_epi, cancel_mono] at e

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

lemma opensRange_homOfLE_invOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) {a k : ℤ}
    (h : invOpen f k ≤ invOpen f a) :
    (X.homOfLE h).opensRange = invOpen ((invOpen f a).ι ≫ f) k := by
  rw [Scheme.opensRange_homOfLE]
  rfl

theorem SpreadHomNbhd.proof (h₁ : DescendHom.Statement) (h₂ : GenericPullInj.Statement)
    (h₃ : SpreadHomSections.Statement) : SpreadHomNbhd.Statement := by
  intro X f _ _ a ha F G hF hG φ
  obtain ⟨m₁, hm₁, H₁⟩ := h₂ X f a ha G hG
  obtain ⟨m₂, hm₂, H₂⟩ := h₃ X f a ha F G hF hG φ
  have hn : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  have hWa : invOpen f ((a : ℤ) * ((m₁ * m₂ : ℕ) : ℤ)) ≤ invOpen f a := invOpen_mul_le_left f a _
  have hW := range_baseChangeMap_subset f ℚ ((a : ℤ) * ((m₁ * m₂ : ℕ) : ℤ))
    (isUnit_intCast_rat _ (by positivity))
  have hR := opensRange_homOfLE_invOpen f hWa
  refine ⟨_, hWa, hW, h₁ _ _ _ (X.homOfLE hWa) (toOpen f ℚ _ hW) _
    (toOpen_homOfLE f ℚ _ hW (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) hWa) F G φ
    (fun V hV => H₁ _ hn (dvd_mul_right _ _) V (hR ▸ hV))
    (fun V hV => H₂ _ hn (dvd_mul_left _ _) V (hR ▸ hV))⟩

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadIso.proof (h₁ : SpreadHom.Statement) (h₂ : SpreadHomInj.Statement) :
    SpreadIso.Statement := by
  intro X f _ _ a ha F G hF hG α
  obtain ⟨m₁, hm₁, H₁⟩ := h₁ X f a ha F G hF hG α.hom
  obtain ⟨m₂, hm₂, H₂⟩ := h₁ X f a ha G F hG hF α.inv
  obtain ⟨m₃, hm₃, I₃⟩ := h₂ X f a ha F F hF hF
  obtain ⟨m₄, hm₄, I₄⟩ := h₂ X f a ha G G hG hG
  obtain ⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄ := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  obtain ⟨ψ₁, e₁⟩ := H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring))
  obtain ⟨ψ₂, e₂⟩ := H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring))
  have k₁ : ψ₁ ≫ ψ₂ = 𝟙 _ := I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, Iso.hom_inv_id])
  have k₂ : ψ₂ ≫ ψ₁ = 𝟙 _ := I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, Iso.inv_hom_id])
  refine ⟨n, hn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩
  rw [pullbackIsoAlong_hom]
  exact e₁

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

theorem isVectorBundle_freeModule (h : FreeSheafBasis.Statement.{u}) (Y : Scheme.{u}) (n : ℕ) :
    IsVectorBundle (freeModule Y n) := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨V, hV, hyV, n, _, (h Y n).restrict le_top⟩

theorem isPreimmersion_baseChangeMap {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) :
    IsPreimmersion (baseChangeMap f (ZLoc p)) := by
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) := by
    have h := IsPreimmersion.of_isLocalization (R := ℤ) (S := ZLoc p)
      (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
    convert h using 3
    exact RingHom.ext_int _ _
  infer_instance

theorem SpreadLocal.proof (h₁ : FreeSheafBasis.Statement.{0}) (h₂ : BasisIsoFree.Statement.{0}) :
    SpreadLocal.Statement := by
  intro X f p E hE x
  obtain ⟨U, -, hxU, n, s, hs⟩ := hE x
  have := isPreimmersion_baseChangeMap f p
  obtain ⟨W, hWo, hW⟩ := (baseChangeMap f (ZLoc p)).isEmbedding.isInducing.isOpen_iff.mp U.2
  let W' : X.Opens := ⟨W, hWo⟩
  have hWU : baseChangeMap f (ZLoc p) ⁻¹ᵁ W' = U := Opens.ext hW
  refine ⟨W', hWU ▸ hxU, ?_⟩
  let V := baseChangeMap f (ZLoc p) ⁻¹ᵁ W'
  have hle : V.ι ''ᵁ ⊤ ≤ U := by simp [V, hWU]
  obtain ⟨eF⟩ := h₂ _ (E.restrict V.ι) n _ ((hs.restrict hle).restrictImage V.ι)
  let φ := (baseChangeMap f (ZLoc p) ∣_ W').toRingCatSheafHom
  have : (SheafOfModules.pushforward φ).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap f (ZLoc p) ∣_ W')).isRightAdjoint
  exact ⟨_, isVectorBundle_freeModule h₁ _ n,
    ⟨SheafOfModules.pullbackObjFreeIso φ (ULift.{0} (Fin n)) ≪≫ eF.symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app E⟩⟩

end

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model


theorem BlowUpChart.comap_eq_maximalIdeal {A K : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {n : ℕ} {x : Fin n → A}
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A) {i : Fin n} (hi : x i ≠ 0)
    (P : Ideal (blowUpChart A K x i)) (hP : P.IsPrime) (hxP : algebraMap A _ (x i) ∈ P) :
    P.comap (algebraMap A (blowUpChart A K x i)) = IsLocalRing.maximalIdeal A := by
  apply le_antisymm
  · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap (algebraMap A (blowUpChart A K x i)) (hK := hP)).ne_top
  · rw [← hx, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hxi : algebraMap A K (x i) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]
      exact hi
    have hmem : algebraMap A K (x j) / algebraMap A K (x i) ∈ blowUpChart A K x i :=
      Algebra.subset_adjoin ⟨j, rfl⟩
    have hfac : algebraMap A (blowUpChart A K x i) (x j) =
        ⟨_, hmem⟩ * algebraMap A (blowUpChart A K x i) (x i) := by
      apply Subtype.ext
      simp [div_mul_cancel₀ _ hxi]
    show algebraMap A _ (x j) ∈ P
    rw [hfac]
    exact P.mul_mem_left _ hxP

theorem BlowUpChart.equiv :
    _root_.GroundTheory.Heights₂.Heights.Model.BlowUpChart.Statement ↔
      _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.BlowUpChart.Statement := by
  constructor
  · intro h A K _ _ _ _ _ _ _ n x hx hne
    obtain ⟨i, hi, hu, -⟩ := h A K n x hx hne
    exact ⟨i, hi, hu, fun P hP hxP => BlowUpChart.comap_eq_maximalIdeal hx hi P hP hxP⟩
  · intro h A _ _ _ _ K _ _ _ n x hx hne
    obtain ⟨i, hi, hu, -⟩ := h A K n x hx hne
    have hne' : Ideal.span {algebraMap A (blowUpChart A K x i) (x i)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact hu
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne'
    exact ⟨i, hi, hu, Q, hQ.isPrime, hle (Ideal.subset_span rfl),
      BlowUpChart.comap_eq_maximalIdeal hx hi Q hQ.isPrime (hle (Ideal.subset_span rfl))⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits

noncomputable section




theorem ClearDenominators.equiv :
    GroundTheory.Heights₂.Heights.Model.ClearDenominators.Statement ↔ ClearDenominators.Statement := by
  constructor
  · intro h X _ _ hf L hL s
    exact h X (toSpecZ X) L hL s
  · intro h X f _ _ _ L hL s
    obtain rfl : f = toSpecZ X := specZ_hom_ext _ _
    exact h X inferInstance L hL s

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem Dominates.equiv (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    [Algebra A K] (V : Subring K) :
    GroundTheory.Heights₂.Heights.Model.Dominates A V ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.Dominates A V :=
  Iff.rfl

theorem DominatingDVR.equiv :
    (GroundTheory.Heights₂.Heights.Model.DominatingDVR.Statement ∧
        GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.Statement) ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.DominatingDVR.Statement := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun A K _ _ _ _ _ _ _ hA => ?_, fun Z _ _ z hz => ?_⟩
    · obtain ⟨V, hV, hd⟩ := h1 A hA K
      exact ⟨V, hV, (Dominates.equiv A V).1 hd⟩
    · obtain ⟨V, hV, hd⟩ := h2 Z z hz
      exact ⟨V, hV, (Dominates.equiv _ V).1 hd⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun A _ _ _ _ hA K _ _ _ => ?_, fun Z _ _ z hz => ?_⟩
    · obtain ⟨V, hV, hd⟩ := h1 A K hA
      exact ⟨V, hV, (Dominates.equiv A V).2 hd⟩
    · obtain ⟨V, hV, hd⟩ := h2 Z z hz
      exact ⟨V, hV, (Dominates.equiv _ V).2 hd⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

section Compare

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

theorem HeightOneIntersection.coe_bot :
    ((Subalgebra.toSubmodule (⊥ : Subalgebra A K) : Submodule A K) : Set K) =
      Set.range (algebraMap A K) := by
  ext x
  exact Algebra.mem_bot

theorem HeightOneIntersection.coe_iInf :
    ((⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        GroundTheory.Heights₂.Heights.Model.localizedIn p.asIdeal
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K)) : Submodule A K) : Set K) =
      ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p := by
  ext x
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Set.mem_iInter]
  have key : ∀ (p : Ideal A) [p.IsPrime],
      x ∈ GroundTheory.Heights₂.Heights.Model.localizedIn p
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K)) ↔ x ∈ locIn A K p := by
    intro p _
    change (∃ s : A, s ∉ p ∧ s • x ∈ (⊥ : Subalgebra A K)) ↔
      ∃ a s : A, s ∉ p ∧ algebraMap A K s * x = algebraMap A K a
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hsx
      exact ⟨a, s, hs, by rw [ha, Algebra.smul_def]⟩
    · rintro ⟨a, s, hs, h⟩
      refine ⟨s, hs, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩
      rw [Algebra.smul_def, h]
  constructor
  · intro h p hp h1
    exact (key p).mp (h ⟨p, hp⟩ h1)
  · intro h p h1
    exact (key p.asIdeal).mpr (h p.asIdeal p.isPrime h1)

theorem HeightOneIntersection.equiv_at :
    (Subalgebra.toSubmodule (⊥ : Subalgebra A K) =
      ⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        GroundTheory.Heights₂.Heights.Model.localizedIn p.asIdeal
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K))) ↔
      Set.range (algebraMap A K) =
        ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p := by
  rw [← HeightOneIntersection.coe_bot, ← HeightOneIntersection.coe_iInf]
  exact SetLike.coe_set_eq.symm

end Compare

theorem HeightOneIntersection.equiv :
    GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.Statement ↔
      HeightOneIntersection.Statement := by
  constructor
  · intro h A K _ _ _ _ _ _ _
    exact (HeightOneIntersection.equiv_at A K).mp (h A K)
  · intro h A _ _ _ _ K _ _ _
    exact (HeightOneIntersection.equiv_at A K).mpr (h A K)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem KrullAkizuki.equiv :
    GroundTheory.Heights₂.Heights.Model.KrullAkizuki.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.KrullAkizuki.Statement := by
  constructor
  · rintro ⟨h₁, h₂⟩ R K L _ _ _ _ _ _ _ _ _ _ _ hR
    exact ⟨h₁ R hR K L, h₂ R hR K⟩
  · intro h
    refine ⟨fun R _ _ _ hR K _ _ _ L _ _ _ _ _ S => (h R K L hR).1 S, ?_⟩
    intro R _ _ _ hR K _ _ _
    exact (h R K K hR).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem LatticesAgree.equiv :
    GroundTheory.Heights₂.Heights.Model.LatticesAgree.Statement ↔ LatticesAgree.Statement := by
  constructor
  · intro h A K V _ _ _ _ _ _ _ _ _ _ _ _ M N hMf hMp hNf hNp hMs hNs hloc
    refine h A K V M N hMf hMp hNf hNp hMs hNs fun p hp => ?_
    exact SetLike.coe_injective (hloc p.asIdeal p.isPrime hp)
  · intro h A _ _ _ _ K _ _ _ V _ _ _ _ _ M N hMf hMp hNf hNp hMs hNs hloc
    refine h A K V M N hMf hMp hNf hNp hMs hNs fun p hp hh => ?_
    have e := hloc ⟨p, hp⟩ hh
    exact congrArg (fun P : Submodule A V => (P : Set V)) e

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem MertensUpper.Iic_eq_range (n : ℕ) : Finset.Iic n = Finset.range (n + 1) := by
  ext m
  simp

theorem MertensUpper.equiv :
    GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement := by
  unfold GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement
  simp only [MertensUpper.Iic_eq_range]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem SectionNef.glueBundles_second_of_first (h : _root_.GroundTheory.Heights₂.Heights.Model.SectionNef.Statement) :
    SectionNef.Statement := by
  intro κ _ _ ι _ F _ P hP hd a ha
  have hs : ∃ s : MRing ι F, IsMultiHomog s a ∧ s ∉ P := by
    rcases ha with h1 | h2
    · exact h1
    · exact h2 P hP le_rfl
  obtain ⟨s, hsa, hsP⟩ := hs
  exact h κ ι F P hP hd (fun k => (a k : ℤ)) s 1
    (_root_.GroundTheory.Heights₂.Heights.Model.isRegularSection_form hP.isPrime hsa hsP)

theorem SectionNef.equiv :
    (_root_.GroundTheory.Heights₂.Heights.Model.SectionNef.Statement ∧
      _root_.GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.Statement) ↔
      SectionNef.Statement :=
  ⟨fun h => SectionNef.glueBundles_second_of_first h.1, fun _ =>
    ⟨_root_.GroundTheory.Heights₂.Heights.Model.SectionNef.proof,
      _root_.GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.proof⟩⟩


end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem cp_eq_primeWeight (p : ℕ) : cp p = GroundTheory.Heights₂.Heights.Model.primeWeight p := rfl

theorem cp_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ cp p := by
  unfold cp
  split_ifs
  · norm_num
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg zero_le_one (by linarith)

theorem sumCp_term_nonneg (d : ℤ) {p : ℕ} (hp : p.Prime) :
    0 ≤ (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p :=
  mul_nonneg (add_nonneg (cp_nonneg hp) (by positivity))
    (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))

theorem SumCp.equiv :
    GroundTheory.Heights₂.Heights.Model.SumCp.Statement ↔ SumCp.Statement := by
  constructor
  · intro hA d hd
    obtain ⟨C, hC⟩ := hA d hd
    refine ⟨C, fun B hB S hS => ?_⟩
    have h := hC B hB S fun p hp => ⟨(hS p hp).1, Or.inl (hS p hp).2⟩
    simpa [cp_eq_primeWeight] using h
  · intro hB d hd
    obtain ⟨C, hC⟩ := hB d hd
    set T := d.natAbs.primeFactors
    set K : ℝ := ∑ p ∈ T, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p
    have hK : 0 ≤ K := Finset.sum_nonneg fun p hp =>
      sumCp_term_nonneg d (Nat.mem_primeFactors.mp hp).1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨C + K / Real.log 2, fun B hB2 S hS => ?_⟩
    have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB2
    have hterm : ∀ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p =
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p := fun p _ => by
      rw [cp_eq_primeWeight]
    have hsum : ∑ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p =
        ∑ p ∈ S, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p :=
      Finset.sum_congr rfl hterm

    have h1 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ B),
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ C * Real.log B :=
      hC B hB2 _ fun p hp => by
        obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
        exact ⟨(hS p hpS).1, hpB⟩

    have h2 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ B),
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ K := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p hp _ => ?_)
      · obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpp, hor⟩ := hS p hpS
        have hpd : (p : ℤ) ∣ d := hor.resolve_left hpB
        exact Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩
      · exact sumCp_term_nonneg d (Nat.mem_primeFactors.mp hp).1
    have h3 : K ≤ K / Real.log 2 * Real.log B := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlogB hK
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ B)
      (fun p => (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p)
    have : ∑ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p ≤ (C + K / Real.log 2) * Real.log B := by
      rw [hsum, ← hsplit, add_mul]
      linarith
    exact this

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem BlowUpChart.full : BlowUpChart.Statement := BlowUpChart.proof

theorem ChartGlue.full : ChartGlue.Statement := ChartGlue.proof

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement := FiniteIntegralClosure.proof

theorem GenericGermInjective.full : GenericGermInjective.Statement := GenericGermInjective.proof

theorem GenericSectionsInj.full : GenericSectionsInj.Statement := GenericSectionsInj.proof

theorem GlueModulesStar.full : GlueModulesStar.Statement := GlueModulesStar.proof

theorem HeightOneIntersection.full : HeightOneIntersection.Statement := HeightOneIntersection.proof

theorem InvOpenInside.full : InvOpenInside.Statement := InvOpenInside.proof

theorem InvOpenInsideRat.full : InvOpenInsideRat.Statement := InvOpenInsideRat.proof

theorem MertensUpper.full : MertensUpper.Statement := MertensUpper.proof

theorem PrimeOpensCover.full : PrimeOpensCover.Statement := PrimeOpensCover.proof

theorem RatLocalAffine.full : RatLocalAffine.Statement := RatLocalAffine.proof

theorem SectionNef.full : SectionNef.Statement := SectionNef.proof

theorem SectionNefGenerated.full : SectionNefGenerated.Statement := SectionNefGenerated.proof

theorem TorsionFreeQuotientLength.full : TorsionFreeQuotientLength.Statement := TorsionFreeQuotientLength.proof

theorem VectorBundleLocal.full : VectorBundleLocal.Statement := VectorBundleLocal.proof

theorem VectorBundleRestrict.full : VectorBundleRestrict.Statement := VectorBundleRestrict.proof

theorem PullbackFaithful.full : PullbackFaithful.Statement.{0} := PullbackFaithful.proof

theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

theorem HeightOneSections.full : HeightOneSections.Statement :=
  HeightOneSections.proof GenericGermInjective.full

theorem BundlesAgree.full : BundlesAgree.Statement :=
  BundlesAgree.proof GenericGermInjective.full HeightOneSections.full

theorem ChartBundlesAgree.full : ChartBundlesAgree.Statement :=
  ChartBundlesAgree.proof HeightOneIntersection.full

theorem LatticesAgree.full : LatticesAgree.Statement :=
  LatticesAgree.proof HeightOneIntersection.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

theorem SpreadHomInj.full : SpreadHomInj.Statement :=
  SpreadHomInj.proof GenericSectionsInj.full PullbackFaithful.full

theorem FiniteNormalization.full : FiniteNormalization.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.normalization_of_scheme
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.scheme_of_alg
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.alg_iff.mp FiniteIntegralClosure.full))

theorem ClearDenominators.of_open (hPB : PullbackBasis.Statement.{0}) :
    ClearDenominators.Statement :=
  ClearDenominators.proof hPB RatLocalAffine.full

theorem SpreadLocal.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) : SpreadLocal.Statement :=
  SpreadLocal.proof hFB hBI

theorem SpreadBundleNbhd.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement) :
    SpreadBundleNbhd.Statement :=
  SpreadBundleNbhd.proof (SpreadLocal.of_open hFB hBI) hSS

theorem SpreadBundle.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement) : SpreadBundle.Statement :=
  SpreadBundle.proof (SpreadBundleNbhd.of_open hFB hBI hSS) InvOpenInside.full

theorem SpreadHomNbhd.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadHomNbhd.Statement :=
  SpreadHomNbhd.proof hDH hGP hHS

theorem SpreadHom.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadHom.Statement :=
  SpreadHom.proof (SpreadHomNbhd.of_open hDH hGP hHS) InvOpenInsideRat.full

theorem SpreadIso.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadIso.Statement :=
  SpreadIso.proof (SpreadHom.of_open hDH hGP hHS) SpreadHomInj.full

theorem GlueBundles.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement)
    (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : GlueBundles.Statement :=
  GlueBundles.proof (SpreadBundle.of_open hFB hBI hSS) (SpreadIso.of_open hDH hGP hHS)
    PrimeOpensCover.full GlueModulesStar.full VectorBundleRestrict.full VectorBundleLocal.full

end GroundTheory.Heights₂.Heights.Model

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem BlowUpChart.full : BlowUpChart.Statement :=
  BlowUpChart.equiv.mp GroundTheory.Heights₂.Heights.Model.BlowUpChart.full

theorem BundlesAgree.full : BundlesAgree.Statement :=
  BundlesAgree.equiv.mp GroundTheory.Heights₂.Heights.Model.BundlesAgree.full

theorem HeightOneIntersection.full : HeightOneIntersection.Statement :=
  HeightOneIntersection.equiv.mp GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.equiv.mp GroundTheory.Heights₂.Heights.Model.KrullAkizuki.full

theorem LatticesAgree.full : LatticesAgree.Statement :=
  LatticesAgree.equiv.mp GroundTheory.Heights₂.Heights.Model.LatticesAgree.full

theorem MertensUpper.full : MertensUpper.Statement :=
  MertensUpper.equiv.mp GroundTheory.Heights₂.Heights.Model.MertensUpper.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.equiv.mp GroundTheory.Heights₂.Heights.Model.SumCp.full

theorem SectionNef.full : SectionNef.Statement :=
  SectionNef.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.SectionNef.full,
    GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.full⟩

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement :=
  FiniteIntegralClosure.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full,
    GroundTheory.Heights₂.Heights.Model.FiniteNormalization.full⟩

theorem DominatingDVR.of_open (hS : GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.Statement) :
    DominatingDVR.Statement :=
  DominatingDVR.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.DominatingDVR.full, hS⟩

theorem ClearDenominators.of_open
    (hPB : GroundTheory.Heights₂.Heights.Model.PullbackBasis.Statement.{0}) :
    ClearDenominators.Statement :=
  ClearDenominators.equiv.mp (GroundTheory.Heights₂.Heights.Model.ClearDenominators.of_open hPB)

theorem SpreadBundle.of_open (hFB : GroundTheory.Heights₂.Heights.Model.FreeSheafBasis.Statement.{0})
    (hBI : GroundTheory.Heights₂.Heights.Model.BasisIsoFree.Statement.{0})
    (hSS : GroundTheory.Heights₂.Heights.Model.SpreadStep.Statement) : SpreadBundle.Statement :=
  SpreadBundle.equiv.mp (GroundTheory.Heights₂.Heights.Model.SpreadBundle.of_open hFB hBI hSS)

theorem SpreadIso.of_open (hDH : GroundTheory.Heights₂.Heights.Model.DescendHom.Statement)
    (hGP : GroundTheory.Heights₂.Heights.Model.GenericPullInj.Statement)
    (hHS : GroundTheory.Heights₂.Heights.Model.SpreadHomSections.Statement) : SpreadIso.Statement :=
  SpreadIso.equiv.mp (GroundTheory.Heights₂.Heights.Model.SpreadIso.of_open hDH hGP hHS)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end
