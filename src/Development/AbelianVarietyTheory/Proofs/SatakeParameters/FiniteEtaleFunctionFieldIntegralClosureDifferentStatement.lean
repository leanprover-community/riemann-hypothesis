import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem finiteDimensional_of_finite_subring_fraction :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (B : Subring K) (B' : Subring L)
      (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite →
      (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → FiniteDimensional K L := by
  intro K L _ _ _ B B' φ hφ hfin hfrac
  letI : Algebra B B' := φ.toAlgebra
  have hMF : Module.Finite B B' := hfin
  obtain ⟨s, hs⟩ := hMF.fg_top

  have hB'span : ∀ x : B', (x : L) ∈ Submodule.span K ((fun z : B' => (z : L)) '' (s : Set B')) := by
    intro x
    have hx : x ∈ Submodule.span B (s : Set B') := by rw [hs]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul b u _ hu =>
      have : ((b • u : B') : L) = (b : K) • (u : L) := by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Subring.coe_mul, hφ, Algebra.smul_def]
      rw [this]; exact Submodule.smul_mem _ _ hu
  let S : Subalgebra K L := Algebra.adjoin K (B' : Set L)
  have hSsub : Subalgebra.toSubmodule S =
      Submodule.span K ((fun z : B' => (z : L)) '' (s : Set B')) := by
    apply le_antisymm
    · rw [Algebra.adjoin_eq_span]
      apply Submodule.span_le.mpr
      intro y hy
      have hy' : y ∈ B'.toSubmonoid := by
        rw [← Submonoid.closure_eq B'.toSubmonoid]; exact hy
      exact hB'span ⟨y, hy'⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨z, _, rfl⟩
      exact Algebra.subset_adjoin z.2
  have hFG : (Subalgebra.toSubmodule S).FG := by
    rw [hSsub]
    exact Submodule.fg_span ((s.finite_toSet).image _)
  have hB'S : ∀ y ∈ B', y ∈ S := fun y hy => Algebra.subset_adjoin hy
  have htop : ∀ y : L, y ∈ S := by
    intro y
    obtain ⟨a, ha, b, hb, hb0, hyb⟩ := hfrac y
    have hbinv : b⁻¹ ∈ S := by
      have hint : IsIntegral K b := IsIntegral.of_mem_of_fg S hFG b (hB'S b hb)
      exact Subalgebra.inv_mem_of_algebraic (A := S) (x := ⟨b, hB'S b hb⟩) hint.isAlgebraic
    have : y = a * b⁻¹ := by rw [← hyb, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
    rw [this]; exact S.mul_mem (hB'S a ha) hbinv
  refine ⟨?_⟩
  obtain ⟨t, ht⟩ := hFG
  refine ⟨t, ?_⟩
  rw [ht, eq_top_iff]
  intro y _
  exact htop y

end GlobalTheory
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_finite_subring_hom_of_fractions : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (B : Subring K) (B' : Subring L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → FiniteDimensional K L := by
  first | (exact @GlobalTheory.finiteDimensional_of_finite_subring_fraction) | (exact GlobalTheory.finiteDimensional_of_finite_subring_fraction) | (intros; apply GlobalTheory.finiteDimensional_of_finite_subring_fraction  <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem integralClosure_of_finite_map : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → IsIntegrallyClosed B → IsIntegrallyClosed B' → (∀ x : K, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → (∀ y ∈ B', IsIntegral B (y : L)) ∧ (∀ x : K, IsIntegral B x → x ∈ B) ∧ (∀ y : L, IsIntegral B y → y ∈ B') := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hfin hB hB' hK hL
  letI : Algebra B B' := φ.toAlgebra
  haveI : IsScalarTower B B' L := IsScalarTower.of_algebraMap_eq fun x => (hφ x).symm
  have fracK : IsFractionRing B K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hK z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [eq_div_iff hb0, h]
  have fracL : IsFractionRing B' L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hL z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [eq_div_iff hb0, h]
  have hint : (algebraMap B B').IsIntegral := RingHom.Finite.to_isIntegral hfin
  refine ⟨fun y hy => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : IsIntegral B (⟨y, hy⟩ : B') := hint _
    have := h1.algebraMap (B := L)
    simpa using this
  · obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff K).mp hB hx
    rw [← hc]; exact c.2
  · have h2 : IsIntegral B' y := hy.tower_top
    obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff L).mp hB' h2
    rw [← hc]; exact c.2

end GlobalTheory.W1
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_of_finite_map_integrallyClosed_subrings : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → IsIntegrallyClosed B → IsIntegrallyClosed B' → (∀ x : K, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → (∀ y ∈ B', IsIntegral B (y : L)) ∧ (∀ x : K, IsIntegral B x → x ∈ B) ∧ (∀ y : L, IsIntegral B y → y ∈ B') := by
  first | (exact @GlobalTheory.W1.integralClosure_of_finite_map) | (exact GlobalTheory.W1.integralClosure_of_finite_map) | (intros; apply GlobalTheory.W1.integralClosure_of_finite_map  <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W1

theorem dv_mem_span_of_formallyUnramified : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.FormallyUnramified → ∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → L) (w : Fin m → K), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D k L v) = ∑ j, b j • mapDR k K L (ι1 (D k K (w j))) := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hU v hv
  letI := φ.toAlgebra
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    change algebraMap k L c = ((φ (algebraMap k B c) : B') : L)
    rw [hφ, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : Algebra.FormallyUnramified B B' := hU
  have hspan : Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k B B' x).mp (Subsingleton.elim _ _)
    induction y with
    | zero => simp
    | add _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B' a]
        exact Submodule.smul_mem _ _ hx
  have hmem : KaehlerDifferential.D k B' ⟨v, hv⟩ ∈
      Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) := hspan ▸ Submodule.mem_top
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  choose w hw using fun j => (g j).2
  refine ⟨n, fun j => (f j : L), fun j => (w j : K), fun j => ⟨(f j).2, (w j).2⟩, ?_⟩
  have key : KaehlerDifferential.D k L v = ∑ j, (f j : L) • KaehlerDifferential.D k L (algebraMap K L (w j)) := by
    have h := congrArg (KaehlerDifferential.map k k B' L) hsum
    rw [map_sum, KaehlerDifferential.map_D] at h
    refine h.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hw j, KaehlerDifferential.map_D, ← hφ]
    first | rfl | simp [Subalgebra.smul_def]
  have hpull : ∀ a : K, mapDR k K L (ι1 (D k K a)) = ι1 (D k L (algebraMap K L a)) := by
    intro a
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]
    simp [map1]
  simp_rw [hpull, key, map_sum, map_smul]

end GlobalTheory.W1
end
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formally_unramified_differentials_span : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.FormallyUnramified → ∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → L) (w : Fin m → K), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D k L v) = ∑ j, b j • mapDR k K L (ι1 (D k K (w j))) := by
  first | (exact @GlobalTheory.W1.dv_mem_span_of_formallyUnramified) | (exact GlobalTheory.W1.dv_mem_span_of_formallyUnramified) | (intros; apply GlobalTheory.W1.dv_mem_span_of_formallyUnramified  <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem isIntegrallyClosed_sections_of_smooth_complex :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  intro Z _ s hsm U hU hg
  have hs : (s.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth s hsm ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  letI : Algebra Γ(Sp ℂ, ⊤) Γ(Z, U) := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
  let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  letI : Field Γ(Sp ℂ, ⊤) := (e.toMulEquiv.isField (Field.toIsField ℂ)).toField
  have : Nonempty U := ⟨⟨_, hg⟩⟩
  have : IsDomain Γ(Z, U) := inferInstance
  exact GlobalTheory.isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)

end GlobalTheory
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  first | (exact @GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (exact GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (intros; apply GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex  <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

noncomputable section

namespace GlobalTheory.W1.SchFF

def eqv {A K σ : Type} [CommRing A] [CommRing K] [SetLike σ K] [SubringClass σ K] (g : A →+* K)
    (hg : Function.Injective g) (S : σ) (hS : ∀ y, y ∈ S ↔ ∃ f, g f = y) : A ≃+* S :=
  RingEquiv.ofBijective (g.codRestrict S fun f => (hS _).2 ⟨f, rfl⟩)
    ⟨fun a b h => hg (congrArg Subtype.val h), fun y => by
      obtain ⟨f, hf⟩ := (hS y).1 y.2
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp] theorem eqv_coe {A K σ : Type} [CommRing A] [CommRing K] [SetLike σ K] [SubringClass σ K] (g : A →+* K)
    (hg : Function.Injective g) (S : σ) (hS : ∀ y, y ∈ S ↔ ∃ f, g f = y) (a : A) :
    ((eqv g hg S hS a : S) : K) = g a := rfl

theorem frac (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) (h : genericPoint X ∈ U) (x : X.functionField) :
    ∃ a b : Γ(X, U), (X.presheaf.germ U _ h).hom b ≠ 0 ∧ x * (X.presheaf.germ U _ h).hom b = (X.presheaf.germ U _ h).hom a := by
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) x
  have hb' : algebraMap Γ(X, U) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem finiteEtale_functionField : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → IsFinite c → Etale c → ∀ (d : ℕ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] [i1 : Algebra ℂ Z.functionField] [i2 : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], i1 = ffAlg s → i2 = ffAlg s' → (∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (f : Γ(Z, U)), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom ((c.app U).hom f) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ U (genericPoint Z) hU).hom f)) → FiniteDimensional Z.functionField Y.functionField ∧ ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (B : Subalgebra ℂ Z.functionField) (B' : Subalgebra ℂ Y.functionField), IsAffineOpen U → (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y) → (∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y) → (∀ y ∈ B', IsIntegral B (y : Y.functionField)) ∧ (∀ x : Z.functionField, IsIntegral B x → x ∈ B) ∧ (∀ y : Y.functionField, IsIntegral B y → y ∈ B') ∧ (∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → Y.functionField) (w : Fin m → Z.functionField), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D ℂ Y.functionField v) = ∑ j, b j • mapDR ℂ Z.functionField Y.functionField (ι1 (D ℂ Z.functionField (w j)))) := by
  intro Z Y _ _ s s' c hcs hfin het d _ _ i1 i2 _ _ h1 h2 hcomp
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  haveI : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  haveI := hfin
  haveI := het
  have hφ : ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) {σ σ' : Type}
      [SetLike σ Z.functionField] [SubringClass σ Z.functionField] [SetLike σ' Y.functionField] [SubringClass σ' Y.functionField]
      (B : σ) (B' : σ') (hB : ∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y)
      (hB' : ∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y),
      IsAffineOpen U → ∃ φ : B →+* B', (∀ x : B, (φ x : Y.functionField) = algebraMap Z.functionField Y.functionField x) ∧
        φ.Finite ∧ φ.FormallyUnramified ∧ Nonempty (Γ(Z, U) ≃+* B) ∧ Nonempty (Γ(Y, c ⁻¹ᵁ U) ≃+* B') := by
    intro U hU hU' σ σ' _ _ _ _ B B' hB hB' hUa
    let eB := GlobalTheory.W1.SchFF.eqv _ (germ_injective_of_isIntegral Z _ hU) B hB
    let eB' := GlobalTheory.W1.SchFF.eqv _ (germ_injective_of_isIntegral Y _ hU') B' hB'
    refine ⟨eB'.toRingHom.comp ((c.app U).hom.comp eB.symm.toRingHom), fun x => ?_, ?_, ?_, ⟨eB⟩, ⟨eB'⟩⟩
    · obtain ⟨f, rfl⟩ := eB.surjective x
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
      exact (GlobalTheory.W1.SchFF.eqv_coe _ _ _ _ _).trans (hcomp U hU hU' f)
    · exact (RingHom.Finite.of_surjective _ eB'.surjective).comp
        ((c.finite_app U hUa).comp (RingHom.Finite.of_surjective _ eB.symm.surjective))
    · have he := HasRingHomProperty.appLE @Etale c het ⟨U, hUa⟩ ⟨c ⁻¹ᵁ U, hUa.preimage c⟩ le_rfl
      rw [Scheme.Hom.appLE_eq_app] at he
      exact ((RingHom.FormallyUnramified.of_surjective eB.symm.surjective).comp
        (RingHom.Etale.formallyUnramified _ he)).comp (RingHom.FormallyUnramified.of_surjective eB'.surjective)
  have hfr : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) {σ : Type}
      [SetLike σ X.functionField] [SubringClass σ X.functionField] (B : σ),
      (∀ y, y ∈ B ↔ ∃ f : Γ(X, U), (X.presheaf.germ U _ h).hom f = y) → IsAffineOpen U →
      ∀ x : X.functionField, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a := by
    intro X _ U h σ _ _ B hB hUa x
    obtain ⟨a, b, hb, e⟩ := GlobalTheory.W1.SchFF.frac X U hUa h x
    exact ⟨_, (hB _).2 ⟨a, rfl⟩, _, (hB _).2 ⟨b, rfl⟩, hb, e⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨U₀, hU₀, hm⟩ := GlobalTheory.QCoh.exists_affine_mem (c (genericPoint Y))
    have hU₀' : genericPoint Y ∈ c ⁻¹ᵁ U₀ := hm
    have hU₀g : genericPoint Z ∈ U₀ := GlobalTheory.VB.genericPoint_mem hm
    obtain ⟨φ, hφ1, hφ2, -, -, -⟩ := hφ U₀ hU₀g hU₀' (Z.presheaf.germ U₀ _ hU₀g).hom.range
      (Y.presheaf.germ _ _ hU₀').hom.range (fun y => RingHom.mem_range) (fun y => RingHom.mem_range) hU₀
    exact GlobalTheory.T.finiteDimensional_of_finite_subring_hom_of_fractions _ _ _ _ φ hφ1 hφ2 (hfr Y _ hU₀' _ (fun y => RingHom.mem_range) (hU₀.preimage c))
  · intro U hU hU' B B' hUa hB hB'
    obtain ⟨φ, hφ1, hφ2, hφ3, ⟨eB⟩, ⟨eB'⟩⟩ := hφ U hU hU' B B' hB hB' hUa
    haveI := GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' Z s U hUa hU
    haveI := GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' Y s' (c ⁻¹ᵁ U) (hUa.preimage c) hU'
    haveI : IsIntegrallyClosed B := IsIntegrallyClosed.of_equiv eB
    haveI : IsIntegrallyClosed B' := IsIntegrallyClosed.of_equiv eB'
    obtain ⟨r1, r2, r3⟩ := GlobalTheory.T.integralClosure_of_finite_map_integrallyClosed_subrings ℂ _ _ B B' φ hφ1 hφ2 inferInstance inferInstance (hfr Z U hU B hB hUa)
      (hfr Y _ hU' B' hB' (hUa.preimage c))
    exact ⟨r1, r2, r3, GlobalTheory.T.formally_unramified_differentials_span ℂ _ _ B B' φ hφ1 hφ3⟩

end GlobalTheory.W1.SchFF

end
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → IsFinite c → Etale c → ∀ (d : ℕ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] [i1 : Algebra ℂ Z.functionField] [i2 : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], i1 = ffAlg s → i2 = ffAlg s' → (∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (f : Γ(Z, U)), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom ((c.app U).hom f) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ U (genericPoint Z) hU).hom f)) → FiniteDimensional Z.functionField Y.functionField ∧ ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (B : Subalgebra ℂ Z.functionField) (B' : Subalgebra ℂ Y.functionField), IsAffineOpen U → (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y) → (∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y) → (∀ y ∈ B', IsIntegral B (y : Y.functionField)) ∧ (∀ x : Z.functionField, IsIntegral B x → x ∈ B) ∧ (∀ y : Y.functionField, IsIntegral B y → y ∈ B') ∧ (∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → Y.functionField) (w : Fin m → Z.functionField), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D ℂ Y.functionField v) = ∑ j, b j • mapDR ℂ Z.functionField Y.functionField (ι1 (D ℂ Z.functionField (w j)))) := by
  first | (exact @GlobalTheory.W1.SchFF.finiteEtale_functionField) | (exact GlobalTheory.W1.SchFF.finiteEtale_functionField) | (intros; apply GlobalTheory.W1.SchFF.finiteEtale_functionField  <;> assumption)
end
