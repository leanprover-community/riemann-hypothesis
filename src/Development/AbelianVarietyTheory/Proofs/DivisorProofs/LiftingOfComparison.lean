import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

namespace GlobalTheory.PlaceExt

theorem valuation_lt_one_iff_inv {L : Type*} [Field L] (V : ValuationSubring L) (y : L) :
    V.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ V := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hpos : 0 < V.valuation y := zero_lt_iff.2 ((map_ne_zero _).2 hy)
    rw [← V.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ hpos]
    simp [hy]

theorem exists_lift {L M C : Type*} [Field L] [Field M] [Algebra L M] [Algebra.IsAlgebraic L M] [Field C]
    [IsAlgClosed C] (f : L →+* C) : ∃ h : M →+* C, ∀ x, h (algebraMap L M x) = f x := by
  letI := f.toAlgebra
  exact ⟨(IsAlgClosed.lift : M →ₐ[L] C), fun x => (IsAlgClosed.lift : M →ₐ[L] C).commutes x⟩

theorem exists_extend_compatible : ∀ (F F' : IntermediateField ℚ ℂ) (hle : F ≤ F'), FiniteDimensional ℚ F' →
    ∀ (W : ValuationSubring ℂ) (K : Type) [Field K] [IsAlgClosed K] (O : ValuationSubring K) (g : F →+* K),
    (∀ x : F, (x : ℂ) ∈ W ↔ g x ∈ O) → ∃ g' : F' →+* K, (∀ x : F, g' (IntermediateField.inclusion hle x) = g x) ∧
      ∀ x : F', (x : ℂ) ∈ W → g' x ∈ O := by
  intro F F' hle hfin W K _ _ O g hg
  haveI : FiniteDimensional ℚ F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  haveI : NumberField F := ⟨⟩
  letI : Algebra F F' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F F' := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let Ω := AlgebraicClosure F'
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F F' Ω
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨g₀, hg₀⟩ := exists_lift (M := F') g
  obtain ⟨ι₂, hι₂⟩ := exists_lift (M := Ω) g₀
  obtain ⟨ι₁, hι₁⟩ := exists_lift (M := Ω) (algebraMap F' ℂ)
  have k₁ : ∀ y : F, ι₁ (algebraMap F Ω y) = (y : ℂ) := fun y => by
    rw [IsScalarTower.algebraMap_apply F F' Ω, hι₁]; rfl
  have k₂ : ∀ y : F, ι₂ (algebraMap F Ω y) = g y := fun y => by
    rw [IsScalarTower.algebraMap_apply F F' Ω, hι₂, hg₀]
  let A := W.comap ι₁
  let A' := O.comap ι₂
  have h : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω x) < 1 ↔ A'.valuation (algebraMap F Ω x) < 1 := by
    intro x
    generalize (x : F) = y
    rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap,
      ValuationSubring.mem_comap, ← map_inv₀, k₁, k₂, hg]
  obtain ⟨σ, hσ⟩ := GlobalTheory.InertiaLift.exists_smul_eq (F := F) (Ω := Ω) h
  refine ⟨ι₂.comp (σ.toRingEquiv.toRingHom.comp (algebraMap F' Ω)), fun x => ?_, fun x hx => ?_⟩
  · change ι₂ (σ (algebraMap F' Ω (algebraMap F F' x))) = g x
    rw [← IsScalarTower.algebraMap_apply, σ.commutes, k₂]
  · change ι₂ (σ (algebraMap F' Ω x)) ∈ O
    by_contra hn
    have h1 : A'.valuation (σ (algebraMap F' Ω x)⁻¹) < 1 := by
      rw [valuation_lt_one_iff_inv, map_inv₀, inv_inv]
      exact Or.inr hn
    rcases (valuation_lt_one_iff_inv _ _).1 ((hσ _).1 h1) with h2 | h2
    · have : x = 0 := by simpa using h2
      subst this
      exact hn (by simp)
    · apply h2
      rw [inv_inv, ValuationSubring.mem_comap, hι₁]
      exact hx

end GlobalTheory.PlaceExt
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_extension_field : ∀ (F F' : IntermediateField ℚ ℂ) (hle : F ≤ F'), FiniteDimensional ℚ F' → ∀ (W : ValuationSubring ℂ) (K : Type) [Field K] [IsAlgClosed K] (O : ValuationSubring K) (g : F →+* K), (∀ x : F, (x : ℂ) ∈ W ↔ g x ∈ O) → ∃ g' : F' →+* K, (∀ x : F, g' (IntermediateField.inclusion hle x) = g x) ∧ ∀ x : F', (x : ℂ) ∈ W → g' x ∈ O := by
  atlas_forward_decl GlobalTheory.PlaceExt.exists_extend_compatible
end

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
open scoped NNReal

namespace GlobalTheory.PlaceNorm

theorem norm_le_one_iff_valuation_le_one :
    ∀ {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime] (T : CDVR)
      (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]),
      (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) →
      ∀ a : K, ‖k (io a)‖ ≤ 1 ↔ la.valuation K a ≤ 1 := by
  intro K _ _ la p _ T io e ho k kO hk a
  obtain ⟨r, hr⟩ := GlobalTheory.CompHt.exists_log_eq (PadicComplexInt.integers p) k kO hk
  have hnorm : ∀ x : ℂ_[p], ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := GlobalTheory.FlatModel.coe_valued p
  have hpne : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp0 : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hpne

  have hpv : 0 ≤ vV T.V (p : T.Fr) := by
    have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (p : T.V)
    have h1' : valV T.V (p : T.Fr) ≤ 1 := by
      rw [← map_natCast (algebraMap T.V T.Fr)]; exact h1
    have h2 : valV T.V (p : T.Fr) ≠ 0 := valV_ne_zero hp0
    have h3 := (WithZero.log_le_log h2 one_ne_zero).2 h1'
    rw [WithZero.log_one] at h3
    simp only [vV]; omega

  have h1 := hr (p : T.Fr) hp0
  rw [map_natCast, hnorm] at h1
  have hpn : ‖(p : ℂ_[p])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hpos : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hpne)
  have hl : Real.log ‖(p : ℂ_[p])‖ < 0 := Real.log_neg hpos hpn
  have hr0 : r < 0 := by
    rw [h1] at hl
    by_contra hc
    push_neg at hc
    have : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) * r := mul_nonneg (by exact_mod_cast hpv) hc
    linarith
  by_cases ha : a = 0
  · subst ha; simp
  have hx : io a ≠ 0 := (map_ne_zero io).2 ha
  have hk0 : k (io a) ≠ 0 := (map_ne_zero k).2 hx
  have h2 := hr (io a) hx
  rw [hnorm, ho.2 a] at h2
  have hva : la.valuation K a ≠ 0 := (la.valuation K).ne_zero_iff.2 ha
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  rw [← Real.log_nonpos_iff (norm_nonneg _), h2, ← WithZero.log_le_log hva one_ne_zero, WithZero.log_one]
  have hv : vLa la a = -WithZero.log (la.valuation K a) := rfl
  push_cast
  constructor
  · intro h
    have h3 : 0 ≤ (e : ℝ) * (vLa la a : ℝ) := by nlinarith
    have h4 : (0 : ℝ) ≤ (vLa la a : ℝ) := by
      by_contra hc; push_neg at hc; nlinarith
    have h5 : (0 : ℤ) ≤ vLa la a := by exact_mod_cast h4
    omega
  · intro h
    have h5 : (0 : ℤ) ≤ vLa la a := by omega
    have h4 : (0 : ℝ) ≤ (vLa la a : ℝ) := by exact_mod_cast h5
    have h3 : 0 ≤ (e : ℝ) * (vLa la a : ℝ) := mul_nonneg he.le h4
    nlinarith

end GlobalTheory.PlaceNorm
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_norm_le_one_iff_valuation : ∀ {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]), (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) → ∀ a : K, ‖k (io a)‖ ≤ 1 ↔ la.valuation K a ≤ 1 := by
  atlas_forward_decl GlobalTheory.PlaceNorm.norm_le_one_iff_valuation_le_one
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

set_option autoImplicit false

namespace GlobalTheory.FinDesc

theorem spField_pt_eq (K : Type) [Field K] (a b : Sp K) : a = b := by
  have h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥ := fun c => Ideal.eq_bot_of_prime c.asIdeal
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem exists_finite_subext_point : ∀ (X S : Scheme.{0}) (s : X ⟶ S), LocallyOfFiniteType s → ∀ (K₀ K : Type) [Field K₀]
    [Field K] [Algebra K₀ K], Algebra.IsAlgebraic K₀ K → ∀ (y : Sp K ⟶ X) (z : Sp K₀ ⟶ S),
    y ≫ s = spMap (algebraMap K₀ K) ≫ z → ∃ (L : IntermediateField K₀ K) (yL : Sp L ⟶ X), FiniteDimensional K₀ L ∧
      spMap (algebraMap L K) ≫ yL = y ∧ yL ≫ s = spMap (algebraMap K₀ L) ≫ z := by
  intro X S s hs K₀ K _ _ _ halg y z hyz
  classical
  let pb : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hpt : ∀ a : Sp K₀, z a = s (y pb) := fun a => by
    have e := congrArg (fun h : Sp K ⟶ S => h pb) hyz
    simp only [Scheme.Hom.comp_apply] at e
    rw [e, spField_pt_eq K₀ a]
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
    (show s (y pb) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hgV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show y pb ∈ s ⁻¹ᵁ U from hqU)
  have hU' : IsAffineOpen U := hU
  have hV' : IsAffineOpen V := hV
  have hry : Set.range y ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [spField_pt_eq K a pb]
    exact hgV
  have hrz : Set.range z ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [hpt a]
    exact hqU
  have hy₁ := IsOpenImmersion.lift_fac hV'.fromSpec y hry
  have hz₁ := IsOpenImmersion.lift_fac hU'.fromSpec z hrz
  rw [← Spec.map_preimage (IsOpenImmersion.lift hV'.fromSpec y hry)] at hy₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec z hrz)] at hz₁
  set φ := Spec.preimage (IsOpenImmersion.lift hV'.fromSpec y hry) with hφ
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec z hrz) with hψ
  have key : s.appLE U V hVU ≫ φ = ψ ≫ CommRingCat.ofHom (algebraMap K₀ K) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec s hU' hV' hVU, ← Category.assoc, hy₁, hz₁]
    exact hyz
  have hft := LocallyOfFiniteType.finiteType_appLE s hU' hV' hVU
  let _ := (s.appLE U V hVU).hom.toAlgebra
  obtain ⟨T, hT⟩ := hft.out
  let L : IntermediateField K₀ K := IntermediateField.adjoin K₀ ((T.image φ.hom : Finset K) : Set K)
  have hfin : FiniteDimensional K₀ L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
  have hmem : ∀ b : Γ(X, V), φ.hom b ∈ L := by
    intro b
    have hb : b ∈ Algebra.adjoin Γ(S, U) (T : Set Γ(X, V)) := by rw [hT]; exact Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem b hb => exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
    | algebraMap a =>
      have e := congrArg (fun h => h.hom a) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [RingHom.algebraMap_toAlgebra, e]
      exact L.algebraMap_mem _
    | add b c _ _ hb hc => rw [map_add]; exact L.add_mem hb hc
    | mul b c _ _ hb hc => rw [map_mul]; exact L.mul_mem hb hc
  let φL : Γ(X, V) →+* L := φ.hom.codRestrict L hmem
  refine ⟨L, Spec.map (CommRingCat.ofHom φL : Γ(X, V) ⟶ CommRingCat.of L) ≫ hV'.fromSpec, hfin, ?_, ?_⟩
  · rw [← hy₁, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp]
    congr 1
  · have key' : s.appLE U V hVU ≫ CommRingCat.ofHom φL = ψ ≫ CommRingCat.ofHom (algebraMap K₀ L) := by
      ext a
      have e := congrArg (fun h => h.hom a) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e ⊢
      exact e
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec s hU' hV' hVU, ← Category.assoc, ← Spec.map_comp, key',
      Spec.map_comp, ← hz₁, spMap]
    simp only [Category.assoc]

end GlobalTheory.FinDesc
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_subextension_point : ∀ (X S : Scheme.{0}) (s : X ⟶ S), LocallyOfFiniteType s → ∀ (K₀ K : Type) [Field K₀] [Field K] [Algebra K₀ K], Algebra.IsAlgebraic K₀ K → ∀ (y : Sp K ⟶ X) (z : Sp K₀ ⟶ S), y ≫ s = spMap (algebraMap K₀ K) ≫ z → ∃ (L : IntermediateField K₀ K) (yL : Sp L ⟶ X), FiniteDimensional K₀ L ∧ spMap (algebraMap L K) ≫ yL = y ∧ yL ≫ s = spMap (algebraMap K₀ L) ≫ z := by
  first | exact @GlobalTheory.FinDesc.exists_finite_subext_point | exact GlobalTheory.FinDesc.exists_finite_subext_point | (intros; apply GlobalTheory.FinDesc.exists_finite_subext_point <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

namespace GlobalTheory.FlatModel

theorem locallyOfFiniteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsQProjOver f) : LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

theorem locallyOfFiniteType_spMap_inclusion {F F' : IntermediateField ℚ ℂ} [FiniteDimensional ℚ F']
    (hle : F ≤ F') : LocallyOfFiniteType (spMap (IntermediateField.inclusion hle).toRingHom) := by
  have h1 : ((IntermediateField.inclusion hle).toRingHom.comp (algebraMap ℚ F)).FiniteType := by
    have : (IntermediateField.inclusion hle).toRingHom.comp (algebraMap ℚ F) = algebraMap ℚ F' :=
      RingHom.ext fun _ => by simp
    rw [this]
    exact (RingHom.Finite.finiteType (RingHom.finite_algebraMap.mpr inferInstance))
  have h2 := RingHom.FiniteType.of_comp_finiteType h1
  exact HasRingHomProperty.Spec_iff.mpr h2

theorem locallyOfFiniteType_of_overIncl : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), GlobalTheory.FlatModel.OverIncl r hle → LocallyOfFiniteType r := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' r hle h
  haveI : FiniteDimensional ℚ c'.F := c'.fin
  haveI := locallyOfFiniteType_of_isQProjOver Xo'.qproj
  haveI := locallyOfFiniteType_spMap_inclusion hle
  haveI : LocallyOfFiniteType (r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [h]; infer_instance
  exact locallyOfFiniteType_of_comp r (pullback.snd _ _)

end GlobalTheory.FlatModel
end

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_change_locally_finite_type : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), GlobalTheory.FlatModel.OverIncl r hle → LocallyOfFiniteType r := by
  atlas_forward_decl GlobalTheory.FlatModel.locallyOfFiniteType_of_overIncl
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_dvr_extension : ∀ (p : ℕ) [Fact p.Prime] (T : CDVR), T.FinRes → ∀ (kO : T.V →+* 𝓞_ℂ_[p]) (k : T.Fr →+* ℂ_[p]), (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) → ∀ (L : Type) [Field L] [Algebra T.Fr L] [FiniteDimensional T.Fr L] (kL : L →+* ℂ_[p]), (∀ a, kL (algebraMap T.Fr L a) = k a) → ∃ (T' : CDVR) (i : T.V →+* T'.V) (iF : T.Fr →+* T'.Fr) (ψ : L ≃+* T'.Fr) (kO' : T'.V →+* 𝓞_ℂ_[p]), T'.FinRes ∧ Function.Injective kO' ∧ (∀ a, algebraMap T'.V T'.Fr (i a) = iF (algebraMap T.V T.Fr a)) ∧ (∀ a, ψ (algebraMap T.Fr L a) = iF a) ∧ (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap T'.V T'.Fr a))) ∧ ∀ (A : Type) [CommRing A] (f : A →+* L), (∀ a, ‖kL (f a)‖ ≤ 1) → ∃ fO : A →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (fO a) = ψ (f a) := by
  first | exact @GlobalTheory.CdvrLiftCp.exists_cdvr_lift | exact GlobalTheory.CdvrLiftCp.exists_cdvr_lift | (intros; apply GlobalTheory.CdvrLiftCp.exists_cdvr_lift <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_extend_of_isProper {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {V : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (y : Sp (FractionRing V) ⟶ X) (s : Sp V ⟶ B) (h : y ≫ f = spMap (algebraMap V (FractionRing V)) ≫ s) :
    ∃ χ : Sp V ⟶ X, y = spMap (algebraMap V (FractionRing V)) ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

theorem liftSt_of_cmpSt (hC : CmpSt) : LiftSt := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle Z la p _ Xw hc _ T io e y₀ ho halg k y hy
  letI := io.toAlgebra
  have hfin : T.FinRes := halg.1
  obtain ⟨hOI, hW, -, -, -, -, -, -, hlift⟩ := hc
  obtain ⟨kO, hk⟩ : ∃ kO : T.V →+* 𝓞_ℂ_[p], ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := by
    letI := H.starRing
    obtain ⟨-, kO, P, _, _, hP, -⟩ := hy
    exact ⟨kO, hP.1⟩
  let kk : T.Fr →+* ℂ_[p] := k.toRingHom
  letI algT : Algebra T.Fr ℂ_[p] := kk.toAlgebra
  let K : IntermediateField T.Fr ℂ_[p] := algebraicClosure T.Fr ℂ_[p]
  haveI hKc : IsAlgClosure T.Fr K := algebraicClosure.isAlgClosure T.Fr ℂ_[p]
  haveI : IsAlgClosed K := hKc.isAlgClosed
  have hKa : Algebra.IsAlgebraic T.Fr K := hKc.isAlgebraic
  let O : ValuationSubring K := (𝓞_ℂ_[p]).comap K.val.toRingHom
  have hO : ∀ x : K, x ∈ O ↔ ‖(x : ℂ_[p])‖ ≤ 1 := fun x => by
    show (Valued.v (x : ℂ_[p]) ≤ 1) ↔ _
    rw [← coe_valued]
    exact NNReal.coe_le_one.symm
  let g : c.F →+* K := (algebraMap T.Fr K).comp io
  have hg : ∀ x : c.F, (x : ℂ) ∈ W ↔ g x ∈ O := fun x => by
    rw [hW, hO, ← GlobalTheory.T.p_adic_norm_le_one_iff_valuation la p T io e ho kk kO hk x]
    rfl
  obtain ⟨fK, hfK1, hfK2⟩ := GlobalTheory.T.exists_valuation_extension_field c.F c'.F hle c'.fin W K O g hg
  have hgf : (algebraMap T.Fr K).comp (algebraMap c.F T.Fr) = fK.comp (IntermediateField.inclusion hle).toRingHom :=
    RingHom.ext fun x => (hfK1 x).symm
  obtain ⟨yy, hyy1, hyy2, hyy3⟩ := hlift K fK (spMap (algebraMap T.Fr K) ≫ ptF y₀.1) (by
      rw [Category.assoc, ptF, pullback.lift_snd, spMap_spMap, hgf]) (by
      rintro _ ⟨q, rfl⟩
      exact halg.2 _)
  obtain ⟨L, yL, hLfin, hyL1, hyL2⟩ := GlobalTheory.T.exists_finite_subextension_point _ _ r (GlobalTheory.T.level_change_locally_finite_type r hle hOI) T.Fr K hKa yy (ptF y₀.1) hyy2
  obtain ⟨kL, hkL⟩ : ∃ kL : L →+* ℂ_[p], kL = K.val.toRingHom.comp L.val.toRingHom := ⟨_, rfl⟩
  have hkL1 : ∀ x : L, kL x = ((x : K) : ℂ_[p]) := fun x => by rw [hkL]; rfl
  obtain ⟨T', i, iF, ψ, kO', hT'fin, hkO'inj, hi, hψ, hkO', hint⟩ :=
    GlobalTheory.T.exists_finite_dvr_extension p T hfin kO kk hk L kL (fun a => by rw [hkL1]; rfl)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (yL ≫ pullback.snd _ _ : Sp L ⟶ Sp c'.F)
  obtain ⟨fL, hfLφ⟩ : ∃ fL : c'.F →+* L, fL = φ.hom := ⟨_, rfl⟩
  have hφ' : yL ≫ pullback.snd _ _ = spMap fL := by rw [← hφ, hfLφ]; rfl
  have hfL : ∀ x, ((fL x : K)) = fK x := fun x => by
    have e1 : spMap ((algebraMap L K).comp fL) = spMap fK := by
      rw [← spMap_spMap, ← hφ', ← Category.assoc, hyL1, hyy1]
    have e2 := congrArg (fun f => (CommRingCat.Hom.hom f) x) (Spec.map_injective e1)
    exact e2
  obtain ⟨β', hβ'⟩ := hint (c'.V W) (fL.comp (c'.V W).subtype) (fun a => by
    rw [RingHom.comp_apply, hkL1, hfL, ← hO]
    exact hfK2 a a.2)
  obtain ⟨yyT, hyyT⟩ : ∃ t : Sp T'.Fr ⟶ Xo'.XF c', t = spMap ψ.toRingHom ≫ yL := ⟨_, rfl⟩
  have hring : ψ.toRingHom.comp (fL.comp (c'.V W).subtype) = (algebraMap T'.V T'.Fr).comp β' :=
    RingHom.ext fun a => (hβ' a).symm
  have hsq : (yyT ≫ Y.j) ≫ Y.s = spMap (algebraMap T'.V (FractionRing T'.V)) ≫ spMap β' := by
    have hj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [hyyT, Category.assoc, Category.assoc, hj, ← Category.assoc yL, hφ', spMap_spMap, spMap_spMap, spMap_spMap,
      hring]
  obtain ⟨yT, hyT⟩ := exists_extend_of_isProper Y.s (projProper _ _ _ Y.proj) (yyT ≫ Y.j) (spMap β') hsq
  obtain ⟨k', hk'⟩ : ∃ k' : T'.Fr →+* ℂ_[p], k' = kL.comp ψ.symm.toRingHom := ⟨_, rfl⟩
  have hk'iF : ∀ a, k' (iF a) = k a := fun a => by
    rw [hk', RingHom.comp_apply, ← hψ a]
    show kL (ψ.symm (ψ _)) = _
    rw [RingEquiv.symm_apply_apply, hkL1]
    rfl
  have hkO'' : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k' (algebraMap T'.V T'.Fr a) := fun a => by
    rw [hk', hkO' a]; rfl
  have hψi : ψ.toRingHom.comp (algebraMap T.Fr L) = iF := RingHom.ext hψ
  have hyyTr : yyT ≫ r = spMap iF ≫ ptF y₀.1 := by
    rw [hyyT, Category.assoc, hyL2, ← Category.assoc, spMap_spMap, hψi]
  obtain ⟨P, π, ψ2, hHT⟩ := hC E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p T T' i iF hi io y₀ k y hy k' kO'
    hkO'' hk'iF yT yyT hyT.symm hyyTr
  refine ⟨spMap kO' ≫ yT, spMap k' ≫ yyT, ⟨⟨T', kO', yT, hT'fin, hkO'inj, rfl⟩, ?_⟩, P, π, ψ2, hHT⟩
  have hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' = k'.comp (algebraMap T'.V T'.Fr) := RingHom.ext hkO''
  have e3 : spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO' ≫ yT = (spMap k' ≫ spMap ψ.toRingHom) ≫ yL ≫ Y.j := by
    rw [← Category.assoc, spMap_spMap, hrk, ← spMap_spMap, Category.assoc, ← hyT, hyyT]
    simp only [Category.assoc]
  rw [e3]
  rintro _ ⟨q, rfl⟩
  obtain ⟨q0⟩ : Nonempty (Sp K) := inferInstance
  have hq : (spMap k' ≫ spMap ψ.toRingHom) q = spMap (algebraMap L K) q0 :=
    Subsingleton.elim (α := PrimeSpectrum L) _ _
  rw [Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, ← Category.assoc, hyL1]
  exact hyy3 ⟨q0, rfl⟩

end GlobalTheory.FlatModel

end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifting_of_comparison : CmpSt → LiftSt := by
  atlas_forward_decl GlobalTheory.FlatModel.liftSt_of_cmpSt
end
