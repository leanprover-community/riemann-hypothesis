import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_etalePullback_orders : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z → ∃ E : DivOver p, E.IsAt (f z) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  first | exact @GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd | exact GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd | (intros; apply GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specializes_dominatesStalk_of_regular : ∀ (X : Scheme.{0}) [IsIntegral X] (V : ValuationSubring X.functionField) (y : X), (∀ g, RegAt y g → g ∈ V) → ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  first | exact @GlobalTheory.exists_specializes_dominatesStalk_of_regAt | exact GlobalTheory.exists_specializes_dominatesStalk_of_regAt | (intros; apply GlobalTheory.exists_specializes_dominatesStalk_of_regAt <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FunctionFieldEtale

theorem finiteDimensional_fractionRing_of_etale {R S K L : Type} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] (φ : R →+* S) (hφ : φ.Etale) (ψ : K →+* L)
    (h : ∀ r, ψ (algebraMap R K r) = algebraMap S L (φ r)) :
    letI := ψ.toAlgebra; FiniteDimensional K L := by
  letI : Algebra K L := ψ.toAlgebra
  letI : Algebra R S := φ.toAlgebra
  haveI : Algebra.Etale R S := hφ
  letI : Algebra R L := (ψ.comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq (fun r => h r)
  haveI : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  let g : K ⊗[R] S →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L)
    (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K g.range :=
    Module.Finite.of_surjective g.rangeRestrict.toLinearMap g.rangeRestrict_surjective
  have hS : ∀ s : S, algebraMap S L s ∈ g.range := fun s => ⟨1 ⊗ₜ s, by simp [g]⟩
  have hinv : ∀ x ∈ g.range, x⁻¹ ∈ g.range := fun x hx =>
    Subalgebra.inv_mem_of_algebraic (A := g.range) (x := ⟨x, hx⟩)
      ((Algebra.IsAlgebraic.isAlgebraic (R := K) (⟨x, hx⟩ : g.range)).algHom g.range.val)
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) y
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ (hS a) (hinv _ (hS b))
  exact Module.Finite.of_surjective g.toLinearMap hsurj

theorem finiteDimensional_functionField_of_etale_on_open : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty →
    letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  intro M W _ _ f _ U hf hU
  have hξU : genericPoint M ∈ U :=
    ((genericPoint_spec M).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  obtain ⟨V, hV, hfξV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f (genericPoint M))
    (U := ⊤) trivial
  let x : U := ⟨genericPoint M, hξU⟩
  have hx : x ∈ (U.ι ≫ f) ⁻¹ᵁ V := hfξV
  obtain ⟨V', hV', hxV', hV'sub⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : V' ≤ (U.ι ≫ f) ⁻¹ᵁ V := fun _ h => hV'sub h
  let U' : M.Opens := U.ι ''ᵁ V'
  have hU' : IsAffineOpen U' := hV'.image_of_isOpenImmersion U.ι
  have hξU' : genericPoint M ∈ U' := ⟨x, hxV', rfl⟩
  have e' : U' ≤ f ⁻¹ᵁ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hV'sub hy
  haveI : Nonempty V := ⟨⟨_, hfξV⟩⟩
  haveI : Nonempty U' := ⟨⟨_, hξU'⟩⟩
  have het0 := HasRingHomProperty.appLE (P := @Etale) (f := U.ι ≫ f) hf ⟨V, hV⟩ ⟨V', hV'⟩ hle
  have key : (U.ι ≫ f).appLE V V' hle = f.appLE V U' e' := by
    rw [Scheme.Hom.comp_appLE]
    erw [Scheme.Opens.ι_appLE]
    rfl
  have het : (f.appLE V U' e').hom.Etale := by
    rw [← key]; exact het0
  haveI := functionField_isFractionRing_of_isAffineOpen W V hV
  haveI := functionField_isFractionRing_of_isAffineOpen M U' hU'
  refine finiteDimensional_fractionRing_of_etale (f.appLE V U' e').hom het (functionFieldMap f) ?_
  intro r
  have := functionFieldMap_algebraMap f (genericPoint M) (W.presheaf.germ V _ hfξV r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at this
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  refine this.trans ?_
  rw [Scheme.Hom.germ_stalkMap_apply]
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hfξV⟩⟩
  erw [Scheme.algebraMap_germ_eq_germToFunctionField]
  show M.presheaf.germ _ _ _ (f.app V r) =
    M.presheaf.germ U' _ hξU' (M.presheaf.map (homOfLE e').op (f.app V r))
  rw [TopCat.Presheaf.germ_res_apply]

end GlobalTheory.FunctionFieldEtale
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  atlas_forward_decl GlobalTheory.FunctionFieldEtale.finiteDimensional_functionField_of_etale_on_open
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) :
    ∀ N : ℕ, ∀ s ∈ S, s ∉ (IsLocalRing.maximalIdeal V) ^ N →
      ∃ k : ℕ, ∃ u ∈ S, u ∉ IsLocalRing.maximalIdeal V ∧ s = π ^ k * u := by
  intro N
  induction N with
  | zero => intro s _ hs; simp at hs
  | succ N ih =>
    intro s hs hsN
    by_cases hm : s ∈ IsLocalRing.maximalIdeal V
    · obtain ⟨t, htS, rfl⟩ := hdiv s hs hm
      have htN : t ∉ (IsLocalRing.maximalIdeal V) ^ N := by
        intro ht
        apply hsN
        rw [pow_succ']
        exact Ideal.mul_mem_mul hπm ht
      obtain ⟨k, u, huS, hum, rfl⟩ := ih t htS htN
      exact ⟨k + 1, u, huS, hum, by ring⟩
    · exact ⟨0, s, hs, hm, by simp⟩

theorem dvrSubring_factor {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t)
    (s : V) (hs : s ∈ S) (h0 : s ≠ 0) :
    ∃ k : ℕ, ∃ u ∈ S, u ∉ IsLocalRing.maximalIdeal V ∧ s = π ^ k * u := by
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  have : ∃ N : ℕ, s ∉ (maximalIdeal V) ^ N := by
    by_contra hc
    push_neg at hc
    have : s ∈ ⨅ i : ℕ, (maximalIdeal V) ^ i := Ideal.mem_iInf.2 hc
    rw [hinf, Ideal.mem_bot] at this
    exact h0 this
  obtain ⟨N, hN⟩ := this
  exact dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow S π hπm hdiv N s hs hN

theorem dvrSubring_eq_top (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπS : π ∈ S) (hπ0 : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hinv : ∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t)
    (hfrac : ∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) : S = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨a, haS, b, hbS, hb0, hvb⟩ := hfrac v
  by_cases ha0 : a = 0
  · subst ha0
    have : v = 0 := (mul_eq_zero.1 hvb).resolve_right hb0
    rw [this]; exact S.zero_mem
  obtain ⟨k, u, huS, hum, rfl⟩ := dvrSubring_factor S π hπm hdiv a haS ha0
  obtain ⟨l, u', hu'S, hu'm, rfl⟩ := dvrSubring_factor S π hπm hdiv b hbS hb0
  obtain ⟨t', ht'S, ht'⟩ := hinv u' hu'S hu'm
  have hπl : π ^ l ≠ 0 := pow_ne_zero _ hπ0
  by_cases hkl : l ≤ k
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    have h1 : v * u' = π ^ d * u := by
      apply mul_left_cancel₀ hπl
      rw [pow_add] at hvb
      linear_combination hvb
    have h2 : v = π ^ d * u * t' := by
      linear_combination t' * h1 - v * ht'
    rw [h2]
    exact S.mul_mem (S.mul_mem (S.pow_mem hπS _) huS) ht'S
  · push_neg at hkl
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkl
    subst hd
    have hπk : π ^ k ≠ 0 := pow_ne_zero _ hπ0
    have h1 : v * π ^ (d + 1) * u' = u := by
      apply mul_left_cancel₀ hπk
      rw [show k + d + 1 = k + (d + 1) by ring, pow_add] at hvb
      linear_combination hvb
    apply absurd _ hum
    rw [← h1, pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hπm))

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subring_eq_univ_of_uniformizer_generates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (S : Subring V) (π : V), π ∈ S → π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V → (∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1) → (∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) → (∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) → S = ⊤ := by
  atlas_forward_decl GlobalTheory.dvrSubring_eq_top
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem formallyUnramified_of_dvr_of_essFiniteType : ∀ (R T V : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing T] [Algebra R T] [Algebra.FormallyUnramified R T] [Algebra.EssFiniteType R T] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] (μ : T →ₐ[R] V), (∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R V r ∈ IsLocalRing.maximalIdeal V) → Function.Injective (algebraMap R V) → (∀ v : V, ∃ a b : T, μ b ≠ 0 ∧ v * μ b = μ a) → Algebra.FormallyUnramified R V := by
  intro R T V _ _ _ _ _ _ _ _ _ _ _ μ hm hinj hfrac
  let Q : Ideal T := (IsLocalRing.maximalIdeal V).comap μ
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  let D := Localization.AtPrime Q
  haveI : Algebra.FormallyUnramified T D := .of_isLocalization Q.primeCompl
  haveI : Algebra.FormallyUnramified R D := .comp R T D
  haveI : Algebra.EssFiniteType T D := .of_isLocalization D Q.primeCompl
  haveI : Algebra.EssFiniteType R D := .comp R T D
  have hQ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R T r ∈ Q := fun r hr => by
    show μ (algebraMap R T r) ∈ IsLocalRing.maximalIdeal V
    rw [μ.commutes]; exact hm r hr
  haveI : IsLocalHom (algebraMap R D) := ⟨fun r hr => by
    by_contra hnu
    rw [IsScalarTower.algebraMap_apply R T D, IsLocalization.AtPrime.isUnit_to_map_iff D Q] at hr
    exact hr (hQ r ((IsLocalRing.mem_maximalIdeal _).2 hnu))⟩
  have hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R D) = IsLocalRing.maximalIdeal D :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hunit : ∀ y : Q.primeCompl, IsUnit (μ y) := fun y => by
    by_contra h; exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  let ν : D →ₐ[R] V := IsLocalization.liftAlgHom (M := Q.primeCompl) (f := μ) hunit
  have hν : ∀ t, ν (algebraMap T D t) = μ t := fun t => IsLocalization.lift_eq _ _
  have hνu : ∀ d, IsUnit (ν d) → IsUnit d := by
    intro d hd
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl d
    have e : IsLocalization.mk' D x s * algebraMap T D s = algebraMap T D x :=
      IsLocalization.mk'_spec D x s
    have hx : IsUnit (μ x) := by
      have := congrArg ν e
      rw [map_mul, hν, hν] at this
      rw [← this]; exact hd.mul (hunit s)
    have hxQ : x ∈ Q.primeCompl := fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
    have : IsUnit (algebraMap T D x) := IsLocalization.map_units D (⟨x, hxQ⟩ : Q.primeCompl)
    rw [← e] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmD : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap R D ϖ} := by
    rw [← hmax, hmR, Ideal.map_span, Set.image_singleton]
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hS := GlobalTheory.T.subring_eq_univ_of_uniformizer_generates V (ν : D →+* V).range (algebraMap R V ϖ) ⟨algebraMap R D ϖ, ν.commutes ϖ⟩
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (hm ϖ hϖm) ?_ ?_ ?_
  · refine Algebra.FormallyUnramified.of_surjective ν fun v => ?_
    have hv : v ∈ (ν : D →+* V).range := hS ▸ Subring.mem_top v
    obtain ⟨d, hd⟩ := hv
    exact ⟨d, hd⟩
  · rintro _ ⟨d, rfl⟩ hs
    have hu : IsUnit (ν d) := by
      by_contra h; exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu'⟩ := hνu d hu
    refine ⟨ν ↑u⁻¹, ⟨_, rfl⟩, ?_⟩
    change ν d * ν ↑u⁻¹ = 1
    rw [← map_mul, ← hu', Units.mul_inv, map_one]
  · rintro _ ⟨d, rfl⟩ hs
    have hd : d ∈ IsLocalRing.maximalIdeal D := (IsLocalRing.mem_maximalIdeal _).2 fun h =>
      (IsLocalRing.mem_maximalIdeal _).1 hs (h.map ν)
    rw [hmD] at hd
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hd
    refine ⟨ν a, ⟨a, rfl⟩, ?_⟩
    change ν (a * algebraMap R D ϖ) = _
    rw [map_mul, ν.commutes, mul_comm]
  · intro v
    obtain ⟨a, b, hb, hab⟩ := hfrac v
    exact ⟨μ a, ⟨_, hν a⟩, μ b, ⟨_, hν b⟩, hb, hab⟩

end GlobalTheory

namespace GlobalTheory

theorem trace_dvr_formallyUnramified_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ (V : ValuationSubring M.functionField) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap (functionFieldMap f))], DominatesStalk V z → letI := ((functionFieldMap f).restrict (V.comap (functionFieldMap f)) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap (functionFieldMap f)) V := by
  intro M W _ _ f _ U hU z hz V _ _ hV
  obtain ⟨-, hfe, hess⟩ :=
    stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict M W f U hU z hz
  set φ := functionFieldMap f with hφ
  set R := V.comap φ
  let A := W.presheaf.stalk (f z)
  let B := M.presheaf.stalk z
  let g : A →+* B := (f.stalkMap z).hom
  letI : Algebra A B := g.toAlgebra
  haveI : Algebra.FormallyEtale A B := hfe
  haveI : Algebra.EssFiniteType A B := hess
  have hcomp : ∀ a : A, φ (algebraMap A W.functionField a) = algebraMap B M.functionField (g a) :=
    fun a => functionFieldMap_algebraMap f z a
  have hαR : ∀ a : A, algebraMap A W.functionField a ∈ R := fun a => by
    change φ _ ∈ V
    rw [hcomp]; exact hV.1 _
  let αR : A →+* R := (algebraMap A W.functionField).codRestrict R hαR
  let βV : B →+* V := (algebraMap B M.functionField).codRestrict V hV.1
  letI algRV : Algebra R V := (φ.restrict R V fun _ hx => hx).toAlgebra
  letI : Algebra A R := αR.toAlgebra
  letI : Algebra A V := (βV.comp g).toAlgebra
  haveI : IsScalarTower A R V := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hcomp a).symm
  let gV : B →ₐ[A] V := { βV with commutes' := fun _ => rfl }
  let μ : TensorProduct A R B →ₐ[R] V :=
    Algebra.TensorProduct.lift (Algebra.ofId R V) gV fun _ _ => Commute.all _ _
  haveI : Algebra.FormallyUnramified R (TensorProduct A R B) := Algebra.FormallyUnramified.base_change R
  haveI : Algebra.EssFiniteType R (TensorProduct A R B) := Algebra.EssFiniteType.baseChange A B R
  refine formallyUnramified_of_dvr_of_essFiniteType R (TensorProduct A R B) V μ ?_ ?_ ?_
  · intro r hr
    by_contra hnu
    have hu : IsUnit (algebraMap R V r) := by
      by_contra h; exact hnu ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have hw' : φ (r : W.functionField) * (w : M.functionField) = 1 := congrArg Subtype.val hw
    have hr0 : (r : W.functionField) ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hw'; exact zero_ne_one hw'
    have hinv : (r : W.functionField)⁻¹ ∈ R := by
      change φ _ ∈ V
      rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hw']
      exact w.2
    exact (IsLocalRing.mem_maximalIdeal _).1 hr
      (isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hr0)⟩)
  · intro x y hxy
    exact Subtype.ext (φ.injective (congrArg Subtype.val hxy))
  · intro v
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) (v : M.functionField)
    have hμ : ∀ c : B, ((μ (1 ⊗ₜ c) : V) : M.functionField) = algebraMap B M.functionField c := by
      intro c
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_, ?_⟩
    · intro h0
      apply nonZeroDivisors.ne_zero hb
      apply IsFractionRing.injective B M.functionField
      rw [map_zero]
      rw [← hμ, h0]; rfl
    · apply Subtype.ext
      rw [Subring.coe_mul, hμ, hμ]
      rw [← hab, div_mul_cancel₀]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_restrict_dvr_comap_dominatesStalk : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ (V : ValuationSubring M.functionField) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap (functionFieldMap f))], DominatesStalk V z → letI := ((functionFieldMap f).restrict (V.comap (functionFieldMap f)) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap (functionFieldMap f)) V := by
  atlas_forward_decl GlobalTheory.trace_dvr_formallyUnramified_of_etale
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RestrictOrd

open IsLocalRing

theorem isLocalHom_restrict {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) :
    IsLocalHom (φ.restrict (V.comap φ) V fun _ hx => hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha
  have hb' : ((b : V) : L) = φ (a : K) := by
    rw [hb]; rfl
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    have : ((b : V) : L) = 0 := by rw [hb', h0, map_zero]
    exact b.ne_zero (Subtype.ext this)
  have hmem : (a : K)⁻¹ ∈ V.comap φ := by
    change φ (a : K)⁻¹ ∈ V
    rw [map_inv₀, ← hb']
    have : ((b⁻¹ : Vˣ) : V) * (b : V) = 1 := b.inv_mul
    have h2 : (((b⁻¹ : Vˣ) : V) : L) = ((b : V) : L)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val this)
    rw [← h2]
    exact ((b⁻¹ : Vˣ) : V).2
  exact isUnit_iff_exists_inv.2 ⟨⟨(a : K)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

theorem log_ordFrac_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)] :
    (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra;
      Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) →
    ∀ g : K, g ≠ 0 →
      WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  intro h g hg
  set ψ := φ.restrict (V.comap φ) V fun _ hx => hx with hψdef
  letI := ψ.toAlgebra
  obtain ⟨hu, he⟩ := h
  haveI : IsLocalHom ψ := isLocalHom_restrict φ V
  haveI : IsLocalHom (algebraMap (V.comap φ) V) := inferInstanceAs (IsLocalHom ψ)
  have hmap : (maximalIdeal (V.comap φ)).map (algebraMap (V.comap φ) V) = maximalIdeal V :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (V.comap φ)
  have ht' : Irreducible (ψ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmap,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  exact GlobalTheory.EtaleDiv.log_ordFrac_map (V.comap φ) V φ ψ (fun _ => rfl) ht ht' hg

end GlobalTheory.RestrictOrd
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)], (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) → ∀ g : K, g ≠ 0 → WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  atlas_forward_decl GlobalTheory.RestrictOrd.log_ordFrac_comap
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.TopForm

theorem isFreeGen_formMap_of_formallyUnramified :
    ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  intro k A B _ _ _ α β ψ h n hU ω hω hex
  obtain ⟨ω', hω'⟩ := hex
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ψ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyUnramified A B := hU
  have hspan : Submodule.span B (Set.range fun a : A => KaehlerDifferential.D k B (ψ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k A B x).mp (Subsingleton.elim _ _)
    induction y with
    | zero => simp
    | add _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B a]
        exact Submodule.smul_mem _ _ hx
  have hgen : Submodule.span B {formMap n ψ h ω} = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span B n (Omega β) hspan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    choose v hv using fun i => hw (Set.mem_range_self i)
    have e : exteriorPower.ιMulti B n w = formMap n ψ h (dForm α v) := by
      rw [formMap_dForm, dForm_eq]
      congr 1
      funext i
      exact (hv i).symm
    rw [SetLike.mem_coe, e, ← hω.repr_smul (dForm α v), map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hmem : ω' ∈ Submodule.span B {formMap n ψ h ω} := hgen ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hb := hω'.repr_smul (formMap n ψ h ω)
  rw [← hb] at hc ⊢
  refine hω'.smul_iff.mpr (IsUnit.of_mul_eq_one c ?_)
  refine hω'.1 ?_
  simp only [mul_comm _ c, mul_smul, one_smul]
  exact hc

end GlobalTheory.TopForm
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified : ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  atlas_forward_decl GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_restrict : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  intro M W _ _ _ _ p f _ n _ _ U hf y hy E' hE'
  have e := functionFieldMap_comp_constFn p f
  have hc : ∀ a, functionFieldMap f (Cartier.constFn p a) ∈ E'.ring := fun a => by
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  obtain ⟨z, hzy, hz⟩ := GlobalTheory.T.exists_specializes_dominatesStalk_of_regular M E'.ring y hE'
  have hzU : z ∈ U := hzy.mem_open U.isOpen hy
  have hfin := GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' M W f U hf ⟨y, hy⟩
  have hess' : ((functionFieldMap f).comp (Cartier.constFn p)).codRestrict E'.ring hc =
      (Cartier.constFn (f ≫ p)).codRestrict E'.ring E'.const_mem :=
    RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  obtain ⟨hdvr, hess⟩ := GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex W.functionField M.functionField (functionFieldMap f)
    (Cartier.constFn p) hfin E'.ring hc (hess' ▸ E'.essFiniteType)
  let E : DivOver p := ⟨E'.ring.comap (functionFieldMap f), hc, hdvr, hess⟩
  haveI : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap f)) := hdvr
  have hun := GlobalTheory.T.etale_restrict_dvr_comap_dominatesStalk M W f U hf z hzU E'.ring hz
  let ψ : E.ring →+* E'.ring := (functionFieldMap f).restrict E.ring E'.ring fun _ hx => hx
  letI := ψ.toAlgebra
  have hψ : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  have hft : Algebra.EssFiniteType E.ring E'.ring := by
    have h1 : (ψ.comp E.const).EssFiniteType := hψ ▸ E'.essFiniteType
    exact RingHom.EssFiniteType.of_comp E.const h1
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr W.functionField M.functionField (functionFieldMap f) E'.ring ⟨hun, hft⟩ g g.ne_zero
  refine ⟨E, fun g ⟨a, ha⟩ => ?_, hord, fun η hη => ?_⟩
  · show functionFieldMap f g ∈ E'.ring
    exact hE' _ ⟨f.stalkMap y a, by rw [← functionFieldMap_algebraMap, ha]⟩
  · haveI := SmoothOfRelativeDimension.smooth n p
    haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
    have hnW : topologicalKrullDim W = n := NadelApp.topologicalKrullDim_eq_of_smooth W p n
    have hnM : topologicalKrullDim M = n := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
    obtain ⟨ω, hω, g, rfl, hg⟩ := E.isFormOrd_formOrd hnW hη
    have hω' := GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified E.const E'.const ψ hψ n hun ω hω (E'.exists_isFreeGen hnM)
    have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      have h1 := formMap_formMap (D := n) E.ring.subtype (functionFieldMap f)
        ((functionFieldMap f).comp E.ring.subtype) rfl rfl e
        (by rw [RingHom.comp_assoc]; exact e) ω
      have h2 := formMap_formMap (D := n) ψ E'.ring.subtype
        ((functionFieldMap f).comp E.ring.subtype) rfl hψ rfl
        (by rw [RingHom.comp_assoc]; exact e) ω
      exact h1.trans h2.symm
    have hpull : ratPull p f n ((g : W.functionField) • E.toRat n ω) =
        ((Units.map (functionFieldMap f).toMonoidHom g : M.functionFieldˣ) : M.functionField) •
          E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      rw [map_smulₛₗ, key]; rfl
    have hne : ratPull p f n ((g : W.functionField) • E.toRat n ω) ≠ 0 := by
      rw [hpull]
      refine smul_ne_zero (Units.ne_zero _) fun h0 => ?_
      have := (E'.isFreeGen_toRat hω').1 (a₁ := 0) (a₂ := 1) (by simp [h0])
      exact zero_ne_one this
    rw [← hg, ← hord g]
    exact DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', _, hpull, rfl⟩

end GlobalTheory.EtaleKlt
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeDivisorOver_restrict_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  atlas_forward_decl GlobalTheory.EtaleKlt.divOver_restrict
end

section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧ (f.stalkMap y).hom.EssFiniteType := by
  first | exact @GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | exact GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | (intros; apply GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict <;> assumption)
end

section
section
open TensorProduct IsLocalRing

namespace GlobalTheory

theorem tensorLift_injective_of_flat {R S A K L : Type} [CommRing R] [CommRing S] [IsDomain S]
    [CommRing A] [Field K] [Field L] [Algebra R S] [Module.Flat R S] [Algebra R A] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] (i : A →ₐ[R] K)
    (hi : Function.Injective i) (f : K →+* L)
    (hf : ∀ r, f (algebraMap R K r) = algebraMap S L (algebraMap R S r)) (g : A ⊗[R] S →+* L)
    (hg : ∀ a s, g (a ⊗ₜ s) = f (i a) * algebraMap S L s) : Function.Injective g := by
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  let fK : K →ₐ[R] L := { toRingHom := f, commutes' := hf }
  let H : K ⊗[R] S →ₐ[R] L :=
    Algebra.TensorProduct.lift fK (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  have hH : ∀ k s, H (k ⊗ₜ s) = f k * algebraMap S L s := fun k s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hgH : ∀ x, g x = H (LinearMap.rTensor S i.toLinearMap x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a s => rw [hg, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hH]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hloc : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K S 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).mpr (TensorProduct.isBaseChange R S K)
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have hHinj : Function.Injective H := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨s, r⟩, hr⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K S 1) y
    have hs : s = 0 := by
      have h1 : H (r • y) = 0 := by
        rw [Submonoid.smul_def, show H (r.1 • y) = r.1 • H y from H.toLinearMap.map_smul r.1 y, hy, smul_zero]
      rw [hr, TensorProduct.mk_apply, hH, map_one, one_mul] at h1
      exact IsFractionRing.injective S L (h1.trans (map_zero _).symm)
    have ha : algebraMap R K r.1 ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    have h2 : algebraMap R K r.1 • y = 0 := by
      rw [algebraMap_smul, ← Submonoid.smul_def, hr, hs, TensorProduct.mk_apply, TensorProduct.tmul_zero]
    rw [← one_smul K y, ← inv_mul_cancel₀ ha, mul_smul, h2, smul_zero]
  intro x y hxy
  rw [hgH, hgH] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := S) i.toLinearMap hi (hHinj hxy)

def rangeValuationSubring {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L]
    (j : B →+* L) (hj : ∀ x : L, ∃ a b : B, j b ≠ 0 ∧ x = j a / j b) : ValuationSubring L where
  toSubring := j.range
  mem_or_inv_mem' x := by
    obtain ⟨a, b, hb, rfl⟩ := hj x
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · right
      have ha : j a ≠ 0 := fun h => hb (by rw [← hc, map_mul, h, zero_mul])
      exact ⟨c, by rw [inv_div, ← hc, map_mul, mul_div_cancel_left₀ _ ha]⟩
    · left
      exact ⟨c, by rw [← hc, map_mul, mul_div_cancel_left₀ _ hb]⟩

theorem exists_valuationSubring_extend_of_formallyEtale : ∀ {K K' R S : Type} [Field K] [Field K']
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K]
    [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S)
    [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType →
    φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K,
    IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) →
    ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧
      (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧
      (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  intro K K' R S _ _ _ _ _ _ _ _ _ _ _ _ φ σ _ hfl het hef hc V hV hRV
  letI : Algebra R S := σ.toAlgebra
  haveI : Module.Flat R S := hfl
  haveI : Algebra.FormallyEtale R S := het
  haveI : Algebra.EssFiniteType R S := hef
  haveI : IsLocalHom (algebraMap R S) := ‹IsLocalHom σ›
  haveI : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  letI : Algebra R V := ((algebraMap R K).codRestrict V hRV).toAlgebra
  letI : Algebra R K' := ((algebraMap S K').comp σ).toAlgebra
  haveI : IsScalarTower R S K' := .of_algebraMap_eq fun _ => rfl
  let fV : V →ₐ[R] K' := { toRingHom := φ.comp V.subtype, commutes' := fun r => RingHom.congr_fun hc r }
  let iV : V →ₐ[R] K := { toRingHom := V.subtype, commutes' := fun _ => rfl }
  let g : V ⊗[R] S →ₐ[R] K' :=
    Algebra.TensorProduct.lift fV (IsScalarTower.toAlgHom R S K') (fun _ _ => Commute.all _ _)
  have hg' : ∀ (a : V) (s : S), g (a ⊗ₜ s) = φ a * algebraMap S K' s := fun a s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hg1 : ∀ s : S, g (1 ⊗ₜ s) = algebraMap S K' s := fun s => by
    rw [hg']; simp
  have hg : Function.Injective g :=
    tensorLift_injective_of_flat (S := S) (L := K') iV Subtype.val_injective φ (RingHom.congr_fun hc) g.toRingHom hg'
  let C := V ⊗[R] S
  haveI : IsDomain C := Function.Injective.isDomain g.toRingHom hg
  obtain ⟨⟨Q, hQ⟩, hQm⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := V) (B := C)
    ⟨maximalIdeal V, inferInstance⟩
  have hQm' : Q.comap (algebraMap V C) = maximalIdeal V := congrArg PrimeSpectrum.asIdeal hQm
  let B := Localization.AtPrime Q
  haveI : Module.Flat V B := Module.Flat.trans V C B
  haveI : Algebra.EssFiniteType V B := .comp V C B
  haveI : Algebra.FormallyEtale V B := .comp V C B
  have hQB : ∀ c : C, IsUnit (algebraMap C B c) ↔ c ∉ Q := fun c =>
    IsLocalization.AtPrime.isUnit_to_map_iff B Q c
  haveI : IsLocalHom (algebraMap V B) := ⟨fun v hv => by
    by_contra hn
    have h1 : algebraMap V C v ∈ Q := by rw [← Ideal.mem_comap, hQm']; exact hn
    rw [IsScalarTower.algebraMap_apply V C B] at hv
    exact (hQB _).mp hv h1⟩
  obtain ⟨_, hB⟩ := exists_isDiscreteValuationRing_of_unramified V B
  have hunit : ∀ y : Q.primeCompl, IsUnit (g.toRingHom y) := fun y => by
    refine Ne.isUnit fun h0 => y.2 ?_
    rw [hg (h0.trans (map_zero g).symm)]
    exact Q.zero_mem
  let j : B →+* K' := IsLocalization.lift (M := Q.primeCompl) (S := B) hunit
  have hjC : ∀ c, j (algebraMap C B c) = g c := IsLocalization.lift_eq (M := Q.primeCompl) (S := B) hunit
  have hj : Function.Injective j := IsLocalization.injective_of_map_algebraMap_zero (M := Q.primeCompl) B j fun x hx => by
    rw [hjC] at hx
    rw [hg (hx.trans (map_zero g).symm), map_zero]
  have hgen : ∀ x : K', ∃ a b : B, j b ≠ 0 ∧ x = j a / j b := fun x => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    refine ⟨algebraMap C B (1 ⊗ₜ a), algebraMap C B (1 ⊗ₜ b), ?_, ?_⟩
    · rw [hjC, hg1]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [hjC, hjC, hg1, hg1]
  let V' := rangeValuationSubring j hgen
  have hVV' : ∀ x ∈ V, φ x ∈ V' := fun x hx =>
    ⟨algebraMap C B (⟨x, hx⟩ ⊗ₜ 1), by rw [hjC, hg', map_one, mul_one]⟩
  let e₀ : B →+* V' := j.codRestrict V' fun b => ⟨b, rfl⟩
  have he₀ : Function.Bijective e₀ :=
    ⟨fun a b h => hj (congrArg Subtype.val h), fun y => by
      obtain ⟨b, hb⟩ := y.2
      exact ⟨b, Subtype.ext hb⟩⟩
  let e : B ≃+* V' := RingEquiv.ofBijective e₀ he₀
  have he : ∀ b, (e b : K') = j b := fun _ => rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have htQ : algebraMap V C t ∈ Q := by
    rw [← Ideal.mem_comap, hQm']
    exact (mem_maximalIdeal _).mpr ht.not_isUnit
  have htB : ¬ IsUnit (algebraMap C B (algebraMap V C t)) := fun h => (hQB _).mp h htQ
  have hφt : φ t ≠ 0 := by
    rw [map_ne_zero]
    exact fun h => ht.ne_zero (Subtype.ext h)
  have hjt : j (algebraMap C B (algebraMap V C t)) = φ t := by
    rw [hjC, Algebra.TensorProduct.algebraMap_apply, hg']
    simp
  have key : (φ t)⁻¹ ∉ V' := by
    rintro ⟨b, hb⟩
    refine htB (IsUnit.of_mul_eq_one b (hj ?_))
    rw [map_mul, hb, map_one, hjt, mul_inv_cancel₀ hφt]
  refine ⟨V', hVV', ?_, fun b => ⟨algebraMap C B (1 ⊗ₜ b), by rw [hjC, hg1]⟩, ?_, ?_⟩
  · obtain ⟨b, hbm, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (IsDiscreteValuationRing.not_a_field B)
    exact
      { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
        toIsLocalRing := inferInstance
        not_a_field' := fun h => by
          have h1 : e b ∈ maximalIdeal V' := fun hu => hbm (by simpa using hu.map e.symm.toRingHom)
          rw [h] at h1
          exact hb0 (e.injective (by simpa using h1)) }
  · intro x hx
    by_contra hxV
    have hinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x⁻¹, hinv⟩ : V)) (fun h => inv_ne_zero hx0 (congrArg Subtype.val h)) ht
    have hn' : x⁻¹ = (u : K) * (t : K) ^ n := congrArg Subtype.val hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => hxV ?_)
      have h2 : ((u : V) : K) * (((u⁻¹ : Vˣ) : V) : K) = 1 := by
        exact_mod_cast congrArg Subtype.val u.mul_inv
      have hn0 : x⁻¹ = (u : K) := by rw [hn', h0, pow_zero, mul_one]
      have : x = (((u⁻¹ : Vˣ) : V) : K) := by
        rw [← inv_inv x, hn0]
        exact inv_eq_of_mul_eq_one_right h2
      exact this ▸ Subtype.property _
    apply key
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have : (φ t)⁻¹ = φ ((t ^ m * u : V) : K) * φ x := by
      rw [← map_inv₀, ← map_mul]
      congr 1
      have hu0 : ((u : V) : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
      have hx' : x = ((u : K) * (t : K) ^ (m + 1))⁻¹ := by rw [← hn', inv_inv]
      rw [hx']
      push_cast
      field_simp
      ring
    rw [this]
    exact mul_mem (hVV' _ (t ^ m * u : V).2) hx
  · letI : Algebra V V' := (φ.restrict V V' hVV').toAlgebra
    let eA : B ≃ₐ[V] V' := AlgEquiv.ofRingEquiv (f := e) fun v => Subtype.ext (by
      rw [he, IsScalarTower.algebraMap_apply V C B, hjC, Algebra.TensorProduct.algebraMap_apply,
        hg']
      simp
      rfl)
    exact ⟨Algebra.FormallyEtale.of_equiv eA, Algebra.EssFiniteType.of_surjective eA.toAlgHom eA.surjective⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local : ∀ {K K' R S : Type} [Field K] [Field K'] [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K] [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S) [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType → φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) → ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧ (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧ (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  atlas_forward_decl GlobalTheory.exists_valuationSubring_extend_of_formallyEtale
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open IsLocalRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleKlt

theorem ord_functionFieldMap_of_formallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  intro M W _ _ p f _ E E' h htr het hft g
  set φ := functionFieldMap f
  set ρ := φ.restrict E.ring E'.ring h
  letI := ρ.toAlgebra
  haveI : Algebra.FormallyEtale E.ring E'.ring := het
  haveI : Algebra.EssFiniteType E.ring E'.ring := hft
  haveI : IsLocalHom (algebraMap E.ring E'.ring) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have e : φ (x : W.functionField) * (y : M.functionField) = 1 := congrArg Subtype.val hy
    have hx0 : (x : W.functionField) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at e
      exact zero_ne_one e
    have hinv : φ ((x : W.functionField)⁻¹) = y := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right e
    have hmem : (x : W.functionField)⁻¹ ∈ E.ring := htr _ (hinv ▸ y.2)
    exact IsUnit.of_mul_eq_one (b := (⟨_, hmem⟩ : E.ring)) (Subtype.ext (mul_inv_cancel₀ hx0))
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := E.ring) (S := E'.ring)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht' : Irreducible (ρ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨m, u, e⟩ := exists_eq_unit_mul_zpow (F := W.functionField) ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := W.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := M.functionField) ht' (Units.map ρ.toMonoidHom u) m
  rw [← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have e2 : ((Units.map φ.toMonoidHom g : M.functionFieldˣ) : M.functionField) =
      algebraMap E'.ring M.functionField (Units.map ρ.toMonoidHom u) *
        algebraMap E'.ring M.functionField (ρ t) ^ m := by
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, e, map_mul, map_zpow₀]
    rfl
  rw [← e2, ordTop_vw_of_ne_zero _ (Units.ne_zero _), WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.EtaleKlt
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordFrac_functionFieldMap_of_essentiallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  atlas_forward_decl GlobalTheory.EtaleKlt.ord_functionFieldMap_of_formallyEtale
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem isFreeGen_formMap_of_formallyEtale {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} {D : ℕ} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β)
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem formOrd_ratPull (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ)
    (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p]
    (hn : topologicalKrullDim W = n) (E : DivOver p) (E' : DivOver (f ≫ p))
    (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring)
    (hρ : ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale)
    (hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g)
    (η : RatForms p n) (hη : η ≠ 0) :
    E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  set φ := functionFieldMap f with hφ
  set ρ := φ.restrict E.ring E'.ring h with hρdef
  obtain ⟨ω, hω, g, hη', hg⟩ := E.isFormOrd_formOrd hn hη
  have hc : ρ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun (functionFieldMap_comp_constFn p f) a
  have hω' : IsFreeGen E'.ring (TopForm.formMap n ρ hc ω) := isFreeGen_formMap_of_formallyEtale hρ hc hω
  have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ρ := by
    ext x
    rfl
  have hτ : (E'.ring.subtype.comp ρ).comp E.const = Cartier.constFn (f ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ρ hc ω) := by
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl
      (functionFieldMap_comp_constFn p f) hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ρ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hpull : ratPull p f n η = φ (g : W.functionField) • E'.toRat n (TopForm.formMap n ρ hc ω) := by
    rw [hη', map_smulₛₗ, key]
  have hne : ratPull p f n η ≠ 0 := by
    rw [hpull]
    intro h0
    have hinj := (E'.isFreeGen_toRat hω').1
    have : φ (g : W.functionField) = 0 := hinj (by simpa using h0)
    exact (g.map φ.toMonoidHom).ne_zero this
  rw [← hg]
  refine DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', Units.map φ.toMonoidHom g, hpull, hord g⟩

end GlobalTheory.EtaleKlt
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p], topologicalKrullDim W = n → ∀ (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) → ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  atlas_forward_decl GlobalTheory.EtaleKlt.formOrd_ratPull
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_lift : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E : DivOver p, E.Through (f y) → ∃ E' : DivOver (f ≫ p), E'.Through y ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  intro M W _ _ _ _ p f _ n _ _ U hU y hy E hE
  obtain ⟨hfl, hfe, hft⟩ := GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open M W f U hU y hy
  obtain ⟨V', h, hdvr, hS, hcomap, het, hess⟩ := GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local (K := W.functionField)
    (K' := M.functionField) (R := W.presheaf.stalk (f y)) (S := M.presheaf.stalk y)
    (functionFieldMap f) (f.stalkMap y).hom hfl hfe hft
    (RingHom.ext fun a => functionFieldMap_algebraMap f y a) E.ring E.dvr (fun a => hE _ ⟨a, rfl⟩)
  have hc : ∀ a, Cartier.constFn (f ≫ p) a ∈ V' := fun a => by
    rw [← functionFieldMap_comp_constFn p f]
    exact h _ (E.const_mem a)
  have hess' : ((Cartier.constFn (f ≫ p)).codRestrict V' hc).EssFiniteType := by
    have e : (Cartier.constFn (f ≫ p)).codRestrict V' hc =
        ((functionFieldMap f).restrict E.ring V' h).comp E.const := by
      ext a
      simp [DivOver.const, ← functionFieldMap_comp_constFn p f]
    rw [e]
    exact E.essFiniteType.comp hess
  let E' : DivOver (f ≫ p) := ⟨V', hc, hdvr, hess'⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  have hdim := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hord := GlobalTheory.T.ordFrac_functionFieldMap_of_essentiallyEtale M W p f E E' h hcomap het hess
  refine ⟨E', fun g hg => ?_, hord, fun η hη => GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale M W p f n hdim E E' h het hord η hη⟩
  obtain ⟨a, rfl⟩ := hg
  exact hS a

end GlobalTheory.EtaleKlt
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeDivisor_lift_along_etale_map : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E : DivOver p, E.Through (f y) → ∃ E' : DivOver (f ≫ p), E'.Through y ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  atlas_forward_decl GlobalTheory.EtaleKlt.divOver_lift
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem formallyEtale_of_isIso {R S : CommRingCat.{0}} (e : R ⟶ S) [IsIso e] :
    e.hom.FormallyEtale := by
  letI := e.hom.toAlgebra
  let E : R ≃ₐ[R] S := { (asIso e).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  show Algebra.FormallyEtale R S
  exact Algebra.FormallyEtale.of_equiv E

theorem genericPoint_mem_of_nonempty {X : Scheme.{0}} [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem formallyEtale_functionFieldMap {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens) (hf : Etale (U.ι ≫ f))
    (hU : (U : Set M).Nonempty) : (functionFieldMap f).FormallyEtale := by
  have hξ := genericPoint_mem_of_nonempty U hU
  let u : (U : Scheme.{0}) := ⟨genericPoint M, hξ⟩
  have h1 : ((U.ι ≫ f).stalkMap u).hom.FormallyEtale := by
    have hu := FormallyUnramified.stalkMap (U.ι ≫ f) u
    have hs : ((U.ι ≫ f).stalkMap u).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ u))
    algebraize [((U.ι ≫ f).stalkMap u).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  rw [Scheme.Hom.stalkMap_comp] at h1
  have h2 : (f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    have e : f.stalkMap (genericPoint M) =
        (f.stalkMap (U.ι u) ≫ U.ι.stalkMap u) ≫ inv (U.ι.stalkMap u) := by simp; rfl
    rw [e]
    exact RingHom.FormallyEtale.comp h1 (formallyEtale_of_isIso _)
  have hiso : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      IsIso (W.presheaf.stalkSpecializes h) := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  have key : ∀ h : f (genericPoint M) ⤳ genericPoint W,
      (W.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    intro h
    haveI := hiso h (map_genericPoint f)
    exact RingHom.FormallyEtale.comp (formallyEtale_of_isIso _) h2
  exact key _

theorem injective_of_isBaseChange_field {A B M N : Type*} [Field A] [CommRing B] [Nontrivial B]
    [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) : Function.Injective φ := by
  have e : (φ : M → N) = hφ.equiv ∘ ((Algebra.linearMap A B).rTensor M) ∘
      (TensorProduct.lid A M).symm := by
    funext m
    simp [hφ.equiv_tmul]
  rw [e]
  refine hφ.equiv.injective.comp ((Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap A B).injective).comp (TensorProduct.lid A M).symm.injective)

theorem ratPull_ne_zero : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M]
    [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ)
    [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 →
      GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  intro M W _ _ _ _ p f _ n _ _ U hf hU η hη h0
  have hE := formallyEtale_functionFieldMap f U hf hU
  letI := (Cartier.constFn p).toAlgebra
  letI := (Cartier.constFn (f ≫ p)).toAlgebra
  letI := (functionFieldMap f).toAlgebra
  haveI : IsScalarTower ℂ W.functionField M.functionField :=
    IsScalarTower.of_algebraMap_eq' (functionFieldMap_comp_constFn p f).symm
  haveI : Algebra.FormallyEtale W.functionField M.functionField := hE
  have hb := isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ W.functionField M.functionField) n
  exact hη (injective_of_isBaseChange_field hb (h0.trans (map_zero _).symm))

end GlobalTheory.EtaleKlt
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalTopFormPullback_ne_zero_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 → GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  atlas_forward_decl GlobalTheory.EtaleKlt.ratPull_ne_zero
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem kltAt_iff_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n m : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens) (D₀ : CartierDiv W) (D₁ : CartierDiv M), Etale (U.ι ≫ f) → 0 < m → (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) → ∀ y ∈ U, (GlobalTheory.Discrepancy.KltAt (f ≫ p) n (GlobalTheory.Discrepancy.qWeil D₁ m) y ↔ GlobalTheory.Discrepancy.KltAt p n (GlobalTheory.Discrepancy.qWeil D₀ m) (f y)) := by
  intro M W _ _ _ _ p f _ n m _ _ U D₀ D₁ hU hm hD y hy
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme M := ModifSections.isNormalScheme_of_smooth (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := ModifSections.isNormalScheme_of_smooth p
  have hnM := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
  have hnW := NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hne : ∀ η : RatForms p n, η ≠ 0 → ratPull p f n η ≠ 0 := GlobalTheory.T.rationalTopFormPullback_ne_zero_of_etale M W p f n U hU ⟨y, hy⟩
  have hlog : ∀ (η : RatForms p n) (m' : ℕ) (g : W.functionFieldˣ), η ≠ 0 →
      IsLogEqn p (qWeil D₀ m) η (f y) m' g →
      IsLogEqn (f ≫ p) (qWeil D₁ m) (ratPull p f n η) y m'
        (Units.map (functionFieldMap f).toMonoidHom g) := by
    intro η m' g hη h z hz E' hE'
    have hzU : z ∈ U := hz.mem_open U.isOpen hy
    obtain ⟨E, hE, hord, hform⟩ := GlobalTheory.T.exists_primeDivisor_etalePullback_orders M W p f n U hU z hzU E' hE'
    have key := h (f z) (hz.map f.continuous) E hE
    obtain ⟨d, hd⟩ := D₀.exists_isEqn (f z)
    have hd' := hD z d hd
    have hmult : D₁.mult z = D₀.mult (f z) := by
      rw [hd'.mult_eq, hd.mult_eq, ← hE'.ord_eq, ← hE.ord_eq, hord]
    rw [hform η hη, hord, ← key]
    simp [qWeil, hmult]
  constructor
  · intro hk
    obtain ⟨η, hη, hG⟩ := isLogCanonicalMultiple_canonical (p := p) (n := n) hnW D₀ hm
    obtain ⟨g, hg⟩ := (m • canonical p n + D₀).exists_isEqn (f y)
    have h1 := hG (f y) g hg
    refine (h1.kltAt_iff hnW hη hm).2 fun E hE => ?_
    obtain ⟨E', hE', hord, hform⟩ := GlobalTheory.T.primeDivisor_lift_along_etale_map M W p f n U hU y hy E hE
    have h2 := ((hlog η m g hη h1).kltAt_iff hnM (hne η hη) hm).1 hk E' hE'
    rw [discrep, hord, hform η hη] at h2
    exact h2
  · rintro ⟨η, m', g, hη, hm', h1, h2⟩
    refine ⟨ratPull p f n η, m', _, hne η hη, hm', hlog η m' g hη h1, fun E' hE' => ?_⟩
    obtain ⟨E, hE, hord, hform⟩ := GlobalTheory.T.primeDivisorOver_restrict_etale M W p f n U hU y hy E' hE'
    have h3 := h2 E hE
    rw [discrep] at h3 ⊢
    rw [hord, hform η hη]
    exact h3
end GlobalTheory.EtaleKlt
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataLogTerminal_iff_etale_pullback : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n m : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens) (D₀ : CartierDiv W) (D₁ : CartierDiv M), Etale (U.ι ≫ f) → 0 < m → (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) → ∀ y ∈ U, (GlobalTheory.Discrepancy.KltAt (f ≫ p) n (GlobalTheory.Discrepancy.qWeil D₁ m) y ↔ GlobalTheory.Discrepancy.KltAt p n (GlobalTheory.Discrepancy.qWeil D₀ m) (f y)) := by
  atlas_forward_decl GlobalTheory.EtaleKlt.kltAt_iff_etale
end
