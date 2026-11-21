import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.EdgesRouteSmall
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import ReciprocityTheory.Chebotarev.StatementHolds
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.SplitPl

open Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_integer_generator : ∃ θ : 𝓞 E, IntermediateField.adjoin F {((θ : 𝓞 E) : E)} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  obtain ⟨d, hd, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := α) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α))
  refine ⟨⟨d • α, hi⟩, ?_⟩
  rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have h1 : d • α ∈ IntermediateField.adjoin F {d • α} := IntermediateField.mem_adjoin_simple_self F _
  have h2 : α = algebraMap F E (d : F)⁻¹ * (d • α) := by
    rw [zsmul_eq_mul, ← mul_assoc, map_inv₀, map_intCast, inv_mul_cancel₀ (by exact_mod_cast hd), one_mul]
  have h3 := mul_mem (IntermediateField.algebraMap_mem (IntermediateField.adjoin F {d • α}) (d : F)⁻¹) h1
  rw [← h2] at h3
  exact h3

theorem map_mem_maximalIdeal_iff (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) c ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      c ∈ v.asIdeal := by
  have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) c : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, e,
    Formalism.BasicNotions.Examples₂.adicCompl_val_algebraMap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  exact ⟨fun h => lt_of_le_of_ne (v.valuation_le_one c) h, fun h => h.ne⟩

theorem nonempty_algHom_of_congr (θ : 𝓞 E) (hθ : IntermediateField.adjoin F {(θ : E)} = ⊤)
    (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (hv : ∀ c, algebraMap (𝓞 F) (𝓞 E) c ∈ P ↔ c ∈ v.asIdeal) (a : 𝓞 F)
    (ha : θ - algebraMap (𝓞 F) (𝓞 E) a ∈ P)
    (hd : aeval θ (derivative (minpoly (𝓞 F) (θ : E))) ∉ P) : Nonempty (E →ₐ[F] Fv F v) := by
  haveI := Formalism.BasicNotions.Examples₂.adicInt_henselian (K := F) v
  have hint : IsIntegral (𝓞 F) (θ : E) := IsIntegral.tower_top (R := ℤ) θ.2
  set G := minpoly (𝓞 F) (θ : E) with hG
  have hmon : G.Monic := minpoly.monic hint
  have hG0 : aeval θ G = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_zero, ← aeval_algebraMap_apply]
    exact minpoly.aeval _ _
  have cong : ∀ Q : (𝓞 F)[X], algebraMap (𝓞 F) (𝓞 E) (Q.eval a) - aeval θ Q ∈ P := fun Q => by
    obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub (algebraMap (𝓞 F) (𝓞 E) a) θ (Q.map (algebraMap (𝓞 F) (𝓞 E)))
    rw [eval_map_apply, eval_map_algebraMap] at hc
    rw [hc, ← neg_sub, neg_mul]
    exact P.neg_mem (P.mul_mem_right _ ha)
  have h1 : G.eval a ∈ v.asIdeal := (hv _).1 (by simpa [hG0] using cong G)
  have h2 : (derivative G).eval a ∉ v.asIdeal := fun h => hd (by
    simpa using P.sub_mem ((hv _).2 h) (cong (derivative G)))
  let φ := algebraMap (𝓞 F) (v.adicCompletionIntegers F)
  obtain ⟨x, hx, -⟩ := HenselianLocalRing.is_henselian (G.map φ) (hmon.map _) (φ a)
    (by rw [eval_map_apply]; exact (map_mem_maximalIdeal_iff v _).2 h1)
    (by
      rw [derivative_map, eval_map_apply]
      by_contra hu
      exact h2 ((map_mem_maximalIdeal_iff v _).1 ((IsLocalRing.mem_maximalIdeal _).2 hu)))
  have hroot : aeval (x : v.adicCompletion F) (minpoly F (θ : E)) = 0 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint, aeval_map_algebraMap]
    haveI : IsScalarTower (𝓞 F) (v.adicCompletionIntegers F) (v.adicCompletion F) :=
      IsScalarTower.of_algebraMap_eq fun c => rfl
    have h3 := aeval_algebraMap_apply (v.adicCompletion F) x G
    have h4 : aeval x G = 0 := by rw [← eval_map_algebraMap]; exact hx
    rw [h4, map_zero] at h3
    exact h3
  have hi : IsIntegral F (θ : E) := Algebra.IsIntegral.isIntegral _
  have hadj : Algebra.adjoin F {(θ : E)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ,
      IntermediateField.top_toSubalgebra]
  let pb := PowerBasis.ofAdjoinEqTop' hi hadj
  exact ⟨pb.lift (x : v.adicCompletion F) (by rw [PowerBasis.ofAdjoinEqTop'_gen]; exact hroot)⟩

theorem split_of_frob_one [IsGalois ℚ E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E)) [hP : P.IsPrime]
    [hl : P.LiesOver (Ideal.span {(p : ℤ)})] (hu : Algebra.IsUnramifiedAt ℤ P)
    (hf : IsArithFrobAt ℤ (1 : Gal(E/ℚ)) P) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E ∧
      ∀ x : 𝓞 E, ∃ a : ℤ, x - algebraMap ℤ (𝓞 E) a ∈ P := by
  have hp1 : 1 < p := hp.one_lt
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := hl.over.symm
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hunder, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hfrob : ∀ x : 𝓞 E, x - x ^ p ∈ P := fun x => by
    have h := hf x
    rw [hcard] at h
    simpa using h
  haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  have hpP : (p : 𝓞 E) ∈ P := by
    have h : (p : ℤ) ∈ P.under ℤ := hunder ▸ Ideal.mem_span_singleton_self _
    simpa using h
  have hne : P ≠ ⊥ := fun e => hp.ne_zero (by
    rw [e, Ideal.mem_bot] at hpP
    exact_mod_cast hpP)
  haveI hmax : P.IsMaximal := hP.isMaximal hne
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  letI := Fintype.ofFinite (𝓞 E ⧸ P)
  have hle : Nat.card (𝓞 E ⧸ P) ≤ p := by
    classical
    have hQ : (X ^ p - X : (𝓞 E ⧸ P)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp1
    have hsub : (Finset.univ : Finset (𝓞 E ⧸ P)).val ⊆ (X ^ p - X : (𝓞 E ⧸ P)[X]).roots := by
      intro y _
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [mem_roots hQ, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem, ← neg_sub]
      exact P.neg_mem (hfrob x)
    have h := card_le_degree_of_subset_roots hsub
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1, Finset.card_univ] at h
    rwa [Nat.card_eq_fintype_card]
  constructor
  · have e1 : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one P ℤ
    have e2 : P.inertiaDeg ℤ = 1 := by
      have h := Ideal.absNorm_pow_inertiaDeg (Ideal.span {(p : ℤ)}) P
      have h0 : Ideal.absNorm (Ideal.span {(p : ℤ)}) = p := by
        rw [Ideal.absNorm_span_singleton]
        simp
      have h1 : Ideal.absNorm P = Nat.card (𝓞 E ⧸ P) := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h0, h1] at h
      have h2 : p ^ P.inertiaDeg ℤ ≤ p ^ 1 := by rw [h, pow_one]; exact hle
      have h3 := (Nat.pow_le_pow_iff_right hp1).1 h2
      have h4 := Ideal.inertiaDeg_pos P ℤ
      omega
    have hm := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (Ideal.span {(p : ℤ)}) (𝓞 E) Gal(E/ℚ)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(E/ℚ),
      Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(E/ℚ), e1, e2, mul_one, mul_one,
      IsGaloisGroup.card_eq_finrank Gal(E/ℚ) ℚ E] at hm
    exact hm
  · intro x
    have hinj : Function.Injective (Ideal.quotientMap P (algebraMap ℤ (𝓞 E))
        (le_refl (P.comap (algebraMap ℤ (𝓞 E))))) := Ideal.quotientMap_injective
    have hbij := hinj.bijective_of_nat_card_le (by
      change Nat.card (𝓞 E ⧸ P) ≤ Nat.card (ℤ ⧸ P.under ℤ)
      rw [hcard]
      exact hle)
    obtain ⟨q, hq⟩ := hbij.2 (Ideal.Quotient.mk P x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨a, ?_⟩
    rw [Ideal.quotientMap_mk] at hq
    exact Ideal.Quotient.eq.1 hq.symm

end GlobalTheory.CompanionTheory.Ar.RT.SplitPl

namespace GlobalTheory.CompanionTheory.Ar.RT

open Polynomial GlobalTheory.CompanionTheory.Ar.RT.SplitPl

theorem exists_splitsFully_notMem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois ℚ E] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)),
    ∃ v ∉ S, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ _ S
  classical
  obtain ⟨θ, hθ⟩ := exists_integer_generator (F := F) (E := E)
  have hint : IsIntegral (𝓞 F) (θ : E) := IsIntegral.tower_top (R := ℤ) θ.2
  have hD : aeval θ (derivative (minpoly (𝓞 F) (θ : E))) ≠ 0 := fun e => by
    have h1 : aeval (θ : E) (derivative (minpoly F (θ : E))) ≠ 0 :=
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral (R := F) (θ : E))).separable.aeval_derivative_ne_zero
        (minpoly.aeval _ _)
    apply h1
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint, derivative_map, aeval_map_algebraMap,
      aeval_algebraMap_apply E θ, e, map_zero]
  set D : 𝓞 E := aeval θ (derivative (minpoly (𝓞 F) (θ : E))) with hDdef
  set N : ℕ := Ideal.absNorm (Ideal.span {D}) with hN
  have hN0 : N ≠ 0 := fun e => hD (by
    rwa [hN, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at e)
  obtain ⟨p, hp, hpT, P, hP, hl, hu, hf⟩ := ReciprocityTheory.Cheb.statement_holds E 1
    (S.image (fun v => Ideal.absNorm (v.asIdeal.under ℤ)) ∪ N.primeFactors)
  obtain ⟨hcount, hres⟩ := split_of_frob_one hp P hu hf
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := hl.over.symm
  have hpP : (p : 𝓞 E) ∈ P := by
    have h : (p : ℤ) ∈ P.under ℤ := hunder ▸ Ideal.mem_span_singleton_self _
    simpa using h
  have hvb : P.under (𝓞 F) ≠ ⊥ := fun e => hp.ne_zero (by
    have h : (p : 𝓞 F) ∈ P.under (𝓞 F) := by
      change algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ P
      simpa using hpP
    rw [e, Ideal.mem_bot] at h
    exact_mod_cast h)
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.under (𝓞 F), inferInstance, hvb⟩
  have hvu : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hunder]
    exact Ideal.under_under P
  refine ⟨v, fun hv => hpT (Finset.mem_union_left _ (Finset.mem_image.2 ⟨v, hv, ?_⟩)), ?_, ?_⟩
  · rw [hvu, Ideal.absNorm_span_singleton]
    simp
  · change ((v.asIdeal.under ℤ).primesOver (𝓞 E)).ncard = _
    rw [hvu]
    exact hcount
  · obtain ⟨a, ha⟩ := hres θ
    refine nonempty_algHom_of_congr θ hθ v P (fun c => Iff.rfl) (a : 𝓞 F) (by simpa using ha) fun hDP => ?_
    have h1 : (N : 𝓞 E) ∈ P := (Ideal.span_singleton_le_iff_mem P).2 hDP (Ideal.absNorm_mem _)
    have h2 : (N : ℤ) ∈ P.under ℤ := by
      change algebraMap ℤ (𝓞 E) (N : ℤ) ∈ P
      simpa using h1
    rw [hunder, Ideal.mem_span_singleton] at h2
    exact hpT (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd_natCast.1 h2, hN0⟩))

end GlobalTheory.CompanionTheory.Ar.RT
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_place_outside : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois ℚ E] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)), ∃ v ∉ S, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.RT.exists_splitsFully_notMem
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo Chars Rep RealMaps FinMaps IsMatched IsTriple IsConst Match PolMatch OneConst Coinv ThetaIntegralsAgree IsRealMaps IsFinMaps RealQuot IsZetaAt At)
open GlobalTheory.WeilM (SB pureA)

namespace GlobalTheory.CompanionTheory.Ar.RT.Move

section Slice

variable {K P : Type} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] [T2Space K]
  [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P] [T2Space P]

theorem exists_nhds_invariant {g : K → ℂ} (hg : g ∈ SB K) : ∃ V ∈ 𝓝 (0 : K), ∀ x, ∀ u ∈ V, g (x + u) = g x := by
  obtain ⟨hl, hc⟩ := hg
  have hO : IsOpen {p : K × K | g (p.1 + p.2) = g p.1} := by
    have h1 : IsLocallyConstant fun p : K × K => g (p.1 + p.2) - g p.1 :=
      (hl.comp_continuous (continuous_fst.add continuous_snd)).sub (hl.comp_continuous continuous_fst)
    have := h1.isOpen_fiber 0
    simpa [sub_eq_zero, Set.preimage] using this
  have hsub : tsupport g ×ˢ ({0} : Set K) ⊆ {p : K × K | g (p.1 + p.2) = g p.1} := by
    rintro ⟨x, u⟩ ⟨_, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    simp [hu]
  obtain ⟨U, V, hU, hV, hCU, h0V, hUV⟩ := generalized_tube_lemma hc (isCompact_singleton (x := (0 : K))) hO hsub
  have hV0 : V ∈ 𝓝 (0 : K) := hV.mem_nhds (h0V rfl)
  refine ⟨V ∩ Neg.neg ⁻¹' V, inter_mem hV0 (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV0)), ?_⟩
  rintro x u ⟨hu, hu'⟩
  by_cases hx : x ∈ tsupport g
  · exact hUV (Set.mk_mem_prod (hCU hx) hu)
  by_cases hxu : x + u ∈ tsupport g
  · have := hUV (Set.mk_mem_prod (hCU hxu) hu')
    simpa using this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]

theorem slice_mem (ε : P →+ K) (π : K →+ P) (hε : Continuous ε) (hπ : Continuous π) (hπε : ∀ y, π (ε y) = y)
    {g : K → ℂ} (hg : g ∈ SB K) (z : K) : (fun y => g (z + ε y)) ∈ SB P := by
  refine ⟨hg.1.comp_continuous (continuous_const.add hε), ?_⟩
  refine HasCompactSupport.intro (K := (fun c => π c - π z) '' tsupport g)
    (hg.2.image (hπ.sub continuous_const)) fun y hy => ?_
  by_contra hne
  exact hy ⟨z + ε y, subset_tsupport _ hne, by simp [hπε]⟩

theorem sb_slice (ε : P →+ K) (π : K →+ P) (hε : Continuous ε) (hπ : Continuous π) (hπε : ∀ y, π (ε y) = y)
    (A : (P → ℂ) →ₗ[ℂ] (P → ℂ)) (hA : ∀ φ ∈ SB P, A φ ∈ SB P) {g : K → ℂ} (hg : g ∈ SB K) :
    (fun x => A (fun y => g (x - ε (π x) + ε y)) (π x)) ∈ SB K := by
  obtain ⟨V, hV, hinv⟩ := exists_nhds_invariant hg
  have hS : ∀ z z', z' - z ∈ V → (fun y => g (z' + ε y)) = fun y => g (z + ε y) := fun z z' h => by
    funext y
    have := hinv (z + ε y) _ h
    rw [← this]
    congr 1
    abel
  have hr : Continuous fun x : K => x - ε (π x) := continuous_id.sub (hε.comp hπ)
  have hrr : ∀ x y, (x - ε (π x) + ε y) - ε (π (x - ε (π x) + ε y)) = x - ε (π x) := fun x y => by
    simp [hπε]
  refine ⟨?_, ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h1 : ∀ᶠ x' in 𝓝 x, (x' - ε (π x')) - (x - ε (π x)) ∈ V := by
      have hc : Continuous fun x' : K => (x' - ε (π x')) - (x - ε (π x)) := hr.sub continuous_const
      have ht : Tendsto (fun x' : K => (x' - ε (π x')) - (x - ε (π x))) (𝓝 x) (𝓝 0) := by
        have := hc.tendsto x
        simpa only [sub_self] using this
      exact ht hV
    have h2 : ∀ᶠ x' in 𝓝 x, A (fun y => g (x - ε (π x) + ε y)) (π x') = A (fun y => g (x - ε (π x) + ε y)) (π x) :=
      hπ.continuousAt.eventually (((IsLocallyConstant.iff_eventually_eq _).1
        (hA _ (slice_mem ε π hε hπ hπε hg _)).1) (π x))
    filter_upwards [h1, h2] with x' h1' h2'
    rw [hS _ _ h1']
    exact h2'
  · set rC : Set K := (fun x : K => x - ε (π x)) '' tsupport g with hrC
    have hrCc : IsCompact rC := hg.2.image hr
    obtain ⟨Z, hZ, hcov⟩ := hrCc.elim_nhds_subcover (fun z => {w : K | w - z ∈ V}) fun z _ => by
      have hc : Continuous fun w : K => w - z := continuous_id.sub continuous_const
      have ht : Tendsto (fun w : K => w - z) (𝓝 z) (𝓝 0) := by
        have := hc.tendsto z
        simpa only [sub_self] using this
      exact ht hV
    set D : Set P := ⋃ z ∈ Z, tsupport (A fun y => g (z + ε y)) with hD
    have hDc : IsCompact D := Z.isCompact_biUnion fun z _ => (hA _ (slice_mem ε π hε hπ hπε hg z)).2
    refine HasCompactSupport.intro (K := (fun p : K × P => p.1 + ε p.2) '' (rC ×ˢ D))
      ((hrCc.prod hDc).image (continuous_fst.add (hε.comp continuous_snd))) fun x hx => ?_
    by_contra hne
    apply hx
    have hne' : (fun y => g (x - ε (π x) + ε y)) ≠ 0 := fun h0 => hne (by simp [h0])
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hne'
    have hmem : x - ε (π x) ∈ rC := ⟨_, subset_tsupport _ hy, hrr x y⟩
    obtain ⟨z, hz, hzV⟩ := Set.mem_iUnion₂.1 (hcov hmem)
    have hs := hS z _ hzV
    refine ⟨(x - ε (π x), π x), ⟨hmem, Set.mem_iUnion₂.2 ⟨z, hz, ?_⟩⟩, by simp⟩
    rw [hs] at hne
    exact subset_tsupport _ hne

end Slice

section Op

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def epsK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : (κ → Fv F v) →+ (κ → Af F) where
  toFun y i := GlobalTheory.AdelicU.singleFin v (y i)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

def piK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : (κ → Af F) →+ (κ → Fv F v) where
  toFun x i := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

theorem continuous_epsK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Continuous (epsK (κ := κ) v) :=
  continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp (continuous_apply i)

theorem continuous_piK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Continuous (piK (κ := κ) v) :=
  continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)

theorem piK_epsK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (y : κ → Fv F v) : piK v (epsK v y) = y := by
  funext i
  exact GlobalTheory.AdelicU.evalV_singleFin_self v (y i)

def finPart (x : κ → AF F) : κ → Af F := fun i => (x i).2

def repl (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x : κ → AF F) (y : κ → Fv F v) : κ → AF F :=
  fun i => ((x i).1, (finPart x - epsK v (piK v (finPart x)) + epsK v y) i)

def opF (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (g : (κ → Af F) → ℂ) : (κ → Af F) → ℂ :=
  fun x => A (fun y => g (x - epsK v (piK v x) + epsK v y)) (piK v x)

def opL (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Ψ := fun x => A (fun y => Ψ (repl v x y)) (piK v (finPart x))
  map_add' Ψ Ψ' := by
    funext x
    change A ((fun y => Ψ (repl v x y)) + fun y => Ψ' (repl v x y)) _ = _
    rw [map_add]
    rfl
  map_smul' c Ψ := by
    funext x
    change A (c • fun y => Ψ (repl v x y)) _ = _
    rw [map_smul]
    rfl

theorem opF_mem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ))
    (hA : ∀ φ ∈ SB (κ → Fv F v), A φ ∈ SB (κ → Fv F v)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    opF v A g ∈ SB (κ → Af F) :=
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  sb_slice (epsK v) (piK v) (continuous_epsK v) (continuous_piK v) (piK_epsK v) A hA hg

theorem opL_pureA (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    opL v A (pureA F f g) = pureA F f (opF v A g) := by
  funext x
  have : (fun y => pureA F f g (repl v x y)) =
      (f fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) •
        fun y => g (finPart x - epsK v (piK v (finPart x)) + epsK v y) := rfl
  change A (fun y => pureA F f g (repl v x y)) (piK v (finPart x)) = _
  rw [this, map_smul]
  rfl

end Op

section Pure

attribute [local instance] Classical.propDecidable

local notation "pureT" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

open GlobalTheory.AdelicU (evFin)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
  {vac : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ}

theorem finite_mulSupport
    (hv : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ} (hφ : ∀ᶠ w in cofinite, φ w = vac w) (x : κ → AF F) :
    (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite := by
  have hint : ∀ᶠ w in cofinite, ∀ i, evFin F w (x i) ∈ (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F).adicCompletionIntegers F :=
    eventually_all.2 fun i => (x i).2.2
  have h : ∀ᶠ w in cofinite, (φ w fun i => evFin F w (x i)) = 1 := by
    filter_upwards [hv, hφ, hint] with w h1 h2 h3
    rw [h2, h1]
    exact Set.indicator_of_mem (show (fun i => evFin F w (x i)) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from h3) 1
  exact Filter.eventually_cofinite.1 h

theorem pure_update
    (hv : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ} (hφ : ∀ᶠ w in cofinite, φ w = vac w)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : (κ → Fv F v) → ℂ) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (x : κ → AF F) :
    pureT f (Function.update φ v ψ) x =
      ψ (fun i => evFin F v (x i)) * pureT f (Function.update φ v 1) x := by
  classical
  have hφ1 : ∀ᶠ w in cofinite, Function.update φ v 1 w = vac w := by
    filter_upwards [hφ, Filter.eventually_cofinite_ne v] with w h1 h2
    rw [Function.update_of_ne h2, h1]
  have h1 := finite_mulSupport hv hφ1 x
  set t : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → ℂ := fun w => if w = v then ψ (fun i => evFin F v (x i)) else 1 with ht
  have hts : (Function.mulSupport t).Finite := (Set.finite_singleton v).subset fun w hw => by
    by_contra h
    exact hw (if_neg h)
  have key : (fun w => Function.update φ v ψ w fun i => evFin F w (x i)) =
      fun w => t w * Function.update φ v 1 w fun i => evFin F w (x i) := by
    funext w
    by_cases h : w = v
    · subst h
      simp [ht]
    · simp [ht, h, Function.update_of_ne h]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [key, finprod_mul_distrib hts h1, finprod_eq_single t v fun w hw => if_neg hw]
  simp only [ht, if_true]
  ring

theorem piK_repl (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x : κ → AF F) (y : κ → Fv F v) :
    (fun i => evFin F v (repl v x y i)) = y := by
  change piK v (finPart x - epsK v (piK v (finPart x)) + epsK v y) = y
  simp [piK_epsK]

theorem pure_repl
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ}
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (x : κ → AF F) (y : κ → Fv F v) :
    pureT f (Function.update φ v 1) (repl v x y) = pureT f (Function.update φ v 1) x := by
  classical
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  refine finprod_congr fun w => ?_
  by_cases h : w = v
  · subst h
    simp
  · rw [Function.update_of_ne h]
    congr 1
    funext i
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w ((x i).2 - GlobalTheory.AdelicU.singleFin v _ + GlobalTheory.AdelicU.singleFin v _) = _
    rw [map_add, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne h, GlobalTheory.AdelicU.evalV_singleFin_ne h]
    simp
    rfl

theorem opL_pure
    (hv : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ} (hφ : ∀ᶠ w in cofinite, φ w = vac w)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) :
    opL v A (pureT f φ) = pureT f (Function.update φ v (A (φ v))) := by
  classical
  funext x
  have hs : (fun y => pureT f φ (repl v x y)) = pureT f (Function.update φ v 1) x • φ v := by
    funext y
    have h := pure_update hv hφ v (φ v) f (repl v x y)
    rw [Function.update_eq_self, piK_repl, pure_repl] at h
    rw [h]
    simp [mul_comm]
  change A (fun y => pureT f φ (repl v x y)) (piK v (finPart x)) = _
  rw [hs, map_smul, pure_update hv hφ v (A (φ v)) f x]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  rfl

theorem pure_update_mem
    (hv : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ} (hφ : ∀ᶠ w in cofinite, φ w = vac w)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Submodule ℂ ((κ → AF F) → ℂ))
    {S : Set ((κ → Fv F v) → ℂ)} (hS : ∀ ψ ∈ S, pureT f (Function.update φ v ψ) ∈ L) {ψ : (κ → Fv F v) → ℂ}
    (hψ : ψ ∈ Submodule.span ℂ S) : pureT f (Function.update φ v ψ) ∈ L := by
  have e : ∀ ψ, pureT f (Function.update φ v ψ) =
      fun x => ψ (fun i => evFin F v (x i)) * pureT f (Function.update φ v 1) x :=
    fun ψ => funext (pure_update hv hφ v ψ f)
  induction hψ using Submodule.span_induction with
  | mem ψ h => exact hS ψ h
  | zero =>
    rw [e]
    convert L.zero_mem using 1
    funext x
    simp
  | add a b _ _ ha hb =>
    rw [e] at ha hb ⊢
    convert L.add_mem ha hb using 1
    funext x
    simp [add_mul]
  | smul c a _ ha =>
    rw [e] at ha ⊢
    convert L.smul_mem c ha using 1
    funext x
    simp [mul_assoc]

end Pure

section Tensor

open scoped TensorProduct

theorem tensor_insert {ι Q : Type} [DecidableEq ι] {Mo : ι → Type} [∀ i, AddCommGroup (Mo i)] [∀ i, Module ℂ (Mo i)]
    [AddCommGroup Q] [Module ℂ Q] (T : Finset ι) (v : ι) (ξ : Mo v) {m m' : ℕ}
    (a : Fin m → Q) (b : Fin m → ∀ i, Mo i) (a' : Fin m' → Q) (b' : Fin m' → ∀ i, Mo i)
    (hb : v ∉ T → ∀ i, b i v = ξ) (hb' : v ∉ T → ∀ j, b' j v = ξ)
    (h : ∑ i, a i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun w : T => b i w) =
      ∑ j, a' j ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun w : T => b' j w)) :
    ∑ i, a i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun w : (insert v T : Finset ι) => b i w) =
      ∑ j, a' j ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun w : (insert v T : Finset ι) => b' j w) := by
  by_cases hvT : v ∈ T
  · rw [Finset.insert_eq_of_mem hvT]
    exact h
  let ex : ∀ w, Mo w := Function.update 0 v ξ
  let e : (∀ w : T, Mo w) → ∀ w : (insert v T : Finset ι), Mo w :=
    fun m w => if hw : w.1 ∈ T then m ⟨w.1, hw⟩ else ex w.1
  have hup : ∀ (m : ∀ w : T, Mo w) (i : T) (x : Mo i), e (Function.update m i x) =
      Function.update (e m) ⟨i.1, Finset.mem_insert_of_mem i.2⟩ x := by
    intro m i x
    funext w
    by_cases hw : w = ⟨i.1, Finset.mem_insert_of_mem i.2⟩
    · subst hw
      simp [e]
    · rw [Function.update_of_ne hw]
      have hne : ∀ hw' : w.1 ∈ T, (⟨w.1, hw'⟩ : T) ≠ i := fun hw' h' => hw (Subtype.ext (show w.1 = i.1 from congrArg Subtype.val h'))
      simp only [e]
      split_ifs with hw'
      · rw [Function.update_of_ne (hne hw')]
      · rfl
  let M : MultilinearMap ℂ (fun w : T => Mo w) (PiTensorProduct ℂ fun w : (insert v T : Finset ι) => Mo w) :=
    MultilinearMap.mk' (fun m => PiTensorProduct.tprod ℂ (e m))
      (fun m i x y => by
        simp only [hup, MultilinearMap.map_update_add])
      (fun m i c x => by
        simp only [hup, MultilinearMap.map_update_smul])
  have hM : ∀ c : ∀ i, Mo i, c v = ξ → M (fun w : T => c w) =
      PiTensorProduct.tprod ℂ fun w : (insert v T : Finset ι) => c w := by
    intro c hc
    have hMe : M (fun w : T => c w) = PiTensorProduct.tprod ℂ (e fun w : T => c w) := rfl
    rw [hMe]
    congr 1
    funext w
    rcases w with ⟨w, hw⟩
    by_cases hwT : w ∈ T
    · simp [e, hwT]
    · obtain rfl : w = v := (Finset.mem_insert.1 hw).resolve_right hwT
      simp [e, hwT, ex, hc]
  have := congrArg (LinearMap.lTensor Q (PiTensorProduct.lift M)) h
  simpa only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.lift.tprod, hM _ (hb hvT _), hM _ (hb' hvT _)] using this

end Tensor

section Main

attribute [local instance] Classical.propDecidable

local notation "pureT" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_section {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P] (p : V →ₗ[ℂ] P) (S : Set V)
    (hs : ∀ ξ, ∃ φ ∈ S, p φ = ξ) : ∃ A : V →ₗ[ℂ] V, (∀ φ, p (A φ) = p φ) ∧ ∀ φ, A φ ∈ Submodule.span ℂ S := by
  choose sec hsec hp using hs
  let b := Module.Basis.ofVectorSpace ℂ P
  let s : P →ₗ[ℂ] V := b.constr ℂ fun i => sec (b i)
  have hps : p ∘ₗ s = LinearMap.id := b.ext fun i => by simp [s, hp]
  refine ⟨s ∘ₗ p, fun φ => LinearMap.congr_fun hps (p φ), fun φ => ?_⟩
  have : LinearMap.range s ≤ Submodule.span ℂ S := by
    rw [Module.Basis.constr_range]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun i => hsec _)
  exact this ⟨p φ, rfl⟩

theorem soLoc_sub {n d : ℕ} {Y : Spc F E n} {Z : Spc F E d} (M : Model σ Y Z) (ψ : AddChar (AF F) ℂ)
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) :
    Submodule.span ℂ (M.SoLoc ψ t) ≤ SB (Fin n × Fin d → Fv F v) :=
  Submodule.span_le.2 fun _ h => h.1

theorem opL_so {n d : ℕ} {Y : Spc F E n} {Z : Spc F E d} (M : Model σ Y Z) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    {v₁ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t₁ : E →ₐ[F] Fv F v₁) (t : E →ₐ[F] Fv F v) (hne : v ≠ v₁)
    (A : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ))
    (hA : ∀ φ, A φ ∈ Submodule.span ℂ (M.SoLoc ψ t)) {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ M.So ψ t₁) :
    opL v A Ψ ∈ M.So ψ t₁ ∧ opL v A Ψ ∈ M.So ψ t := by
  have hle : M.So ψ t₁ ≤ (M.So ψ t₁ ⊓ M.So ψ t).comap (opL v A) := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, φ, h1, h2, h3, rfl⟩
    have hU : ∀ ψ' ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update φ v ψ' w ∈ SB _ := fun ψ' h' w => by
      by_cases h : w = v
      · subst h
        simpa using h'
      · rw [Function.update_of_ne h]
        exact h1 w
    have hC : ∀ ψ', ∀ᶠ w in cofinite, Function.update φ v ψ' w = M.vac w := fun ψ' => by
      filter_upwards [h2, Filter.eventually_cofinite_ne v] with w h h'
      rw [Function.update_of_ne h', h]
    rw [SetLike.mem_coe, Submodule.mem_comap, opL_pure hM.std h2]
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ?_, ?_⟩
    · refine ⟨f, _, hU _ (soLoc_sub M ψ t (hA _)), hC _, ?_, rfl⟩
      rw [Function.update_of_ne hne.symm]
      exact h3
    · refine pure_update_mem hM.std h2 v f _ (S := M.SoLoc ψ t) (fun ψ' h' => Submodule.subset_span ?_) (hA _)
      exact ⟨f, _, hU _ h'.1, hC _, by simpa using h', rfl⟩
  exact hle hΨ

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem polMatch_move (hM' : G.M'.IsGood B.ψ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (hsph : Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v))
    (A : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ))
    (hSB : ∀ φ, A φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) (hp : ∀ φ, Rf.p' v (A φ) = Rf.p' v φ)
    {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ} (h : PolMatch B G X R Rf Φ Ψ) :
    PolMatch B G X R Rf Φ (opL v A Ψ) := by
  obtain ⟨T, hT, m, m', f, φ, f', φ', h1, h2, rfl, rfl, he⟩ := h
  have hc : ∀ j, ∀ᶠ w in cofinite, φ' j w = G.M'.vac w := fun j => by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with w hw using (h2 j).2.2 w hw
  have hpu : ∀ j (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
      Rf.p' w (Function.update (φ' j) v (A (φ' j v)) w) = Rf.p' w (φ' j w) := fun j w => by
    by_cases h : w = v
    · subst h
      simpa using hp _
    · rw [Function.update_of_ne h]
  refine ⟨insert v T, hT.trans (Finset.subset_insert _ _), m, m', f, φ, f',
    fun j => Function.update (φ' j) v (A (φ' j v)),
    fun i => ⟨(h1 i).1, (h1 i).2.1, fun w hw => (h1 i).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    fun j => ⟨(h2 j).1, fun w => ?_, fun w hw => ?_⟩, rfl, ?_, ?_⟩
  · change Function.update (φ' j) v (A (φ' j v)) w ∈ _
    by_cases h : w = v
    · subst h
      simpa using hSB _
    · rw [Function.update_of_ne h]
      exact (h2 j).2.1 w
  · have h : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
    change Function.update (φ' j) v (A (φ' j v)) w = _
    rw [Function.update_of_ne h]
    exact (h2 j).2.2 w fun h' => hw (Finset.mem_insert_of_mem h')
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => opL_pure hM'.std (hc j) v A (f' j)
  · simp only [hpu]
    exact tensor_insert T v (Rf.p v (G.M.vac v)) _ (fun i w => Rf.p w (φ i w)) _ (fun j w => Rf.p' w (φ' j w))
      (fun hv i => by simp only [(h1 i).2.2 v hv]) (fun hv j => by simp only [(h2 j).2.2 v hv, hsph]) he

abbrev mv (B : Base F E) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (τ : E →ₐ[F] Fv F v) : Base F E := { B with v₁ := v, τ₁ := τ }

theorem match_move (hM' : G.M'.IsGood B.ψ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (hne : v ≠ B.v₁)
    (hsph : Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v))
    (A : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ))
    (hA : ∀ φ, A φ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ τ)) (hp : ∀ φ, Rf.p' v (A φ) = Rf.p' v φ)
    {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ} (h : Match B G X R Rf Φ Ψ) :
    Match B G X R Rf Φ (opL v A Ψ) ∧ Match (mv B v τ) G X R Rf Φ (opL v A Ψ) := by
  have hSB : ∀ φ, A φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) := fun φ => soLoc_sub G.M' B.ψ τ (hA φ)
  obtain ⟨hΨ, m, m', g, f, s, g', f', s', hc, hc', rfl, rfl, hk⟩ := h
  have hg : ∀ j, opF v A (g' j) ∈ SB _ := fun j => opF_mem v A (fun φ _ => hSB φ) (hc' j).1
  have he : ∀ u : Fin m' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      opL v A (∑ j, pureA F (u j) (g' j)) = ∑ j, pureA F (u j) (opF v A (g' j)) := fun u => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => opL_pureA v A _ _
  have hso := opL_so G.M' B.ψ hM' B.τ₁ τ hne A hA hΨ
  have hk' := fun k => opL_so G.M' B.ψ hM' B.τ₁ τ hne A hA (hk k).1
  have hpm := fun k => polMatch_move (G := G) (X := X) (R := R) (Rf := Rf) hM' hsph A hSB hp (hk k).2
  refine ⟨⟨hso.1, m, m', g, f, s, fun j => opF v A (g' j), f', s', hc, fun j => ⟨hg j, (hc' j).2⟩, rfl, he f', fun k => ?_⟩,
    ⟨hso.2, m, m', g, f, s, fun j => opF v A (g' j), f', s', hc, fun j => ⟨hg j, (hc' j).2⟩, rfl, he f', fun k => ?_⟩⟩
  · rw [← he]
    exact ⟨(hk' k).1, hpm k⟩
  · rw [← he]
    exact ⟨(hk' k).2, hpm k⟩

theorem const_eq (hM : IsMatched B G X om om' R Rf) (one : OneConst B G X om om' R Rf) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (τ : E →ₐ[F] Fv F v) (hne : v ≠ B.v₁) (hvT : v ∉ X.T) (hs : ∀ ξ, ∃ φ ∈ G.M'.SoLoc B.ψ τ, Rf.p' v φ = ξ) {c c' : ℂ}
    (hc : IsConst B G X om om' R Rf c) (hc' : IsConst (mv B v τ) G X om om' R Rf c') : c = c' := by
  obtain ⟨A, hp, hA⟩ := exists_section (Rf.p' v) _ hs
  have hnz : ∃ Φ Ψ h, Match B G X R Rf Φ Ψ ∧ G.M'.I om' Ψ h ≠ 0 := by
    by_contra hcon
    have hz : ∀ Φ Ψ h, Match B G X R Rf Φ Ψ → G.M'.I om' Ψ h = 0 :=
      fun Φ Ψ h hm => by_contra fun hn => hcon ⟨Φ, Ψ, h, hm, hn⟩
    obtain ⟨c₀, _, hu⟩ := one.2.1
    have hc1 : IsConst B G X om om' R Rf (c + 1) := fun Φ Ψ hm h => by
      rw [hc Φ Ψ hm h, hz Φ Ψ h hm, mul_zero, mul_zero]
    have := (hu _ hc1).trans (hu _ hc).symm
    simp at this
  obtain ⟨Φ, Ψ, h, hm, hI⟩ := hnz
  obtain ⟨m1, m2⟩ := match_move hM.triple.geo.hM' τ hne (hM.fin.sph v hvT).1 A hA hp hm
  have e1 := hc Φ Ψ hm h
  have e2 := hc _ _ m1 h
  have e3 := hc' _ _ m2 h
  have hI' : G.M'.I om' (opL v A Ψ) h ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at e2
    rw [e2] at e1
    exact mul_ne_zero (one.2.2 c hc) hI e1.symm
  exact mul_right_cancel₀ hI' (e2.symm.trans e3)



end Main


end GlobalTheory.CompanionTheory.Ar.RT.Move

end
end
