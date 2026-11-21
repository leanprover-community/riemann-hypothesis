import Mathlib
import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.SeparableClosureValuation
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.UnitMulPowAdic

section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

section Ambient

variable {K Ω : Type*} [Field K] [Field Ω] [ValuativeRel Ω] [Algebra K Ω]

theorem valuation_le_valuation_iff_coe (E : IntermediateField K Ω) (x y : E) :
    valuation E x ≤ valuation E y ↔ valuation Ω (x : Ω) ≤ valuation Ω (y : Ω) := by
  rw [← Valuation.vle_iff_le, ← Valuation.vle_iff_le, IntermediateField.coe_vle_coe_iff]

theorem valuation_eq_valuation_iff_coe (E : IntermediateField K Ω) (x y : E) :
    valuation E x = valuation E y ↔ valuation Ω (x : Ω) = valuation Ω (y : Ω) := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_valuation_iff_coe,
    valuation_le_valuation_iff_coe]

theorem mem_integer_intermediateField_iff (E : IntermediateField K Ω) (x : E) :
    x ∈ 𝒪[E] ↔ valuation Ω (x : Ω) ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation E), valuation_le_valuation_iff_coe]
  simp

theorem isUnit_integer_intermediateField_iff (E : IntermediateField K Ω) (x : 𝒪[E]) :
    IsUnit x ↔ valuation Ω ((x : E) : Ω) = 1 := by
  rw [(Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one, ← map_one (valuation E)]
  exact (valuation_eq_valuation_iff_coe E _ _).trans (by simp; rfl)

theorem mem_maximalIdeal_intermediateField_iff (E : IntermediateField K Ω) (x : 𝒪[E]) :
    x ∈ 𝓂[E] ↔ valuation Ω ((x : E) : Ω) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_intermediateField_iff]
  have : valuation Ω ((x : E) : Ω) ≤ 1 := (mem_integer_intermediateField_iff E x).mp x.2
  exact ⟨fun h ↦ lt_of_le_of_ne this h, fun h ↦ h.ne⟩

theorem dvd_integer_intermediateField_iff (E : IntermediateField K Ω) (x y : 𝒪[E]) :
    x ∣ y ↔ valuation Ω ((y : E) : Ω) ≤ valuation Ω ((x : E) : Ω) := by
  rw [(Valuation.integer.integers (valuation E)).dvd_iff_le]
  exact valuation_le_valuation_iff_coe E _ _

def integerInclusion [ValuativeRel K] [ValuativeExtension K Ω] {E F : IntermediateField K Ω}
    (h : E ≤ F) : 𝒪[E] →ₐ[𝒪[K]] 𝒪[F] where
  toFun x := ⟨IntermediateField.inclusion h x, by
    rw [mem_integer_intermediateField_iff]
    exact (mem_integer_intermediateField_iff E x).mp x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_integerInclusion [ValuativeRel K] [ValuativeExtension K Ω] {E F : IntermediateField K Ω}
    (h : E ≤ F) (x : 𝒪[E]) : (((integerInclusion h x : 𝒪[F]) : F) : Ω) = ((x : E) : Ω) :=
  rfl

theorem integerInclusion_injective [ValuativeRel K] [ValuativeExtension K Ω]
    {E F : IntermediateField K Ω} (h : E ≤ F) : Function.Injective (integerInclusion h) := by
  intro x y hxy
  have := congrArg (fun z : 𝒪[F] ↦ ((z : F) : Ω)) hxy
  exact Subtype.ext (Subtype.ext this)

instance isLocalHom_integerInclusion [ValuativeRel K] [ValuativeExtension K Ω]
    {E F : IntermediateField K Ω} (h : E ≤ F) : IsLocalHom (integerInclusion h) :=
  ⟨fun x hx ↦ by
    rw [isUnit_integer_intermediateField_iff] at hx ⊢
    exact hx⟩

end Ambient

section Discrete

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

theorem exists_valuation_eq_algebraMap {x : Ω} (hx : x ∈ 𝔼) (hx0 : x ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ valuation Ω x = valuation Ω (algebraMap K Ω a) := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp hx
  have := hL.1
  have he : ramificationIndex K L = 1 := hL.ramificationIndex_eq_one
  set y : L := ⟨x, hxL⟩
  obtain ⟨a, ha, hay⟩ := exists_ord_eq K (ord y)
  refine ⟨a, ha, ?_⟩
  have h1 := ordRat_algebraMap_of_finite (K := K) (Ω := Ω) y
  rw [he, Nat.cast_one, div_one] at h1
  rw [← ordRat_eq_ordRat_iff (K := K) hx0 ((_root_.map_ne_zero _).mpr ha), ordRat_algebraMap,
    hay]
  exact h1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

@[simp]
theorem coe_algebraMap_integer_intermediateField (E : IntermediateField K Ω) (a : 𝒪[K]) :
    (((algebraMap 𝒪[K] 𝒪[E] a : 𝒪[E]) : E) : Ω) = algebraMap K Ω (a : K) :=
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

theorem valuation_algebraMap_eq_one_iff (x : K) :
    valuation Ω (algebraMap K Ω x) = 1 ↔ valuation K x = 1 := by
  simpa using valuation_algebraMap_eq_iff (G := Ω) x 1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

theorem not_isUnit_algebraMap_uniformizer (E : IntermediateField K Ω) {ϖ : 𝒪[K]}
    (hϖ : Irreducible ϖ) : ¬ IsUnit (algebraMap 𝒪[K] 𝒪[E] ϖ) := by
  rw [isUnit_integer_intermediateField_iff, coe_algebraMap_integer_intermediateField,
    valuation_algebraMap_eq_one_iff]
  exact ((Valuation.integer.integers (valuation K)).valuation_irreducible_lt_one hϖ).ne

theorem exists_associated_pow {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {r : 𝒪[𝔼]} (hr : r ≠ 0) :
    ∃ n : ℕ, Associated (algebraMap 𝒪[K] 𝒪[𝔼] ϖ ^ n) r := by
  have hx0 : ((r : 𝔼) : Ω) ≠ 0 := by
    intro h
    exact hr (Subtype.ext (Subtype.ext h))
  obtain ⟨a, ha, hva⟩ := exists_valuation_eq_algebraMap (r : 𝔼).2 hx0
  have haK : a ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, ← map_one (valuation K), ← valuation_algebraMap_le_iff (G := Ω),
      map_one, ← hva]
    exact (mem_integer_intermediateField_iff _ _).mp r.2
  set a' : 𝒪[K] := ⟨a, haK⟩
  have ha' : a' ≠ 0 := fun h ↦ ha (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha' hϖ
  have hu1 : valuation Ω (algebraMap K Ω ((u : 𝒪[K]) : K)) = 1 := by
    rw [valuation_algebraMap_eq_one_iff]
    exact (Valuation.integer.integers (valuation K)).valuation_unit u
  have hv : valuation Ω ((r : 𝔼) : Ω) = valuation Ω (algebraMap K Ω (ϖ : K)) ^ n := by
    have h2 : a = ((u : 𝒪[K]) : K) * (ϖ : K) ^ n := by
      have := congrArg Subtype.val hu
      simpa [a'] using this
    rw [hva, h2, map_mul, map_mul, hu1, one_mul, map_pow, map_pow]
  have hv' : valuation Ω (((algebraMap 𝒪[K] 𝒪[𝔼] ϖ ^ n : 𝒪[𝔼]) : 𝔼) : Ω) =
      valuation Ω (algebraMap K Ω (ϖ : K)) ^ n := by
    rw [← map_pow]
    simp
  refine ⟨n, associated_of_dvd_dvd ?_ ?_⟩ <;> rw [dvd_integer_intermediateField_iff, hv, hv']

theorem irreducible_algebraMap_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap 𝒪[K] 𝒪[𝔼] ϖ) := by
  set p := algebraMap 𝒪[K] 𝒪[𝔼] ϖ
  have hp := not_isUnit_algebraMap_uniformizer 𝔼 hϖ
  have hp0 : p ≠ 0 := by
    intro h
    have h' := congrArg (fun z : 𝒪[𝔼] ↦ ((z : 𝔼) : Ω)) h
    simp only [p, coe_algebraMap_integer_intermediateField] at h'
    rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, map_eq_zero_iff _ (algebraMap K Ω).injective] at h'
    exact hϖ.ne_zero (Subtype.ext h')
  have hdvd : ∀ x : 𝒪[𝔼], ¬ IsUnit x → p ∣ x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨n, hn⟩ := exists_associated_pow hϖ hx0
    rcases n with _ | n
    · exact absurd (hn.isUnit (by simp)) hx
    · exact (dvd_pow_self p n.succ_ne_zero).trans hn.dvd
  refine irreducible_iff.mpr ⟨hp, fun a b hab ↦ ?_⟩
  by_contra h
  push Not at h
  obtain ⟨c, rfl⟩ := hdvd a h.1
  obtain ⟨d, rfl⟩ := hdvd b h.2
  have : p * (c * d) = 1 := by
    apply mul_left_cancel₀ hp0
    linear_combination hab.symm
  exact hp (isUnit_iff_exists_inv.mpr ⟨_, this⟩)

instance isDiscreteValuationRing_integer : IsDiscreteValuationRing 𝒪[𝔼] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_algebraMap_uniformizer hϖ, fun hx ↦ exists_associated_pow hϖ hx⟩

theorem map_maximalIdeal_integer : (𝓂[K]).map (algebraMap 𝒪[K] 𝒪[𝔼]) = 𝓂[𝔼] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    (irreducible_algebraMap_uniformizer hϖ).maximalIdeal_eq]

end Discrete

section Automorphism

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsAlgebraic K L]

variable (K L) in

def integerAlgEquivOfIsAlgebraic : (L ≃ₐ[K] L) →* (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) where
  toFun ρ :=
    { toFun x := ⟨ρ x, by
        rw [Valuation.mem_integer_iff, valuation_algEquiv_apply_of_isAlgebraic]
        exact x.2⟩
      invFun x := ⟨ρ.symm x, by
        rw [Valuation.mem_integer_iff, valuation_algEquiv_apply_of_isAlgebraic]
        exact x.2⟩
      left_inv x := Subtype.ext (ρ.symm_apply_apply _)
      right_inv x := Subtype.ext (ρ.apply_symm_apply _)
      map_mul' x y := Subtype.ext (map_mul ρ _ _)
      map_add' x y := Subtype.ext (map_add ρ _ _)
      commutes' a := Subtype.ext (ρ.commutes _) }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem coe_integerAlgEquivOfIsAlgebraic_apply (ρ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    (integerAlgEquivOfIsAlgebraic K L ρ x : L) = ρ x :=
  rfl

end Automorphism

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] in

instance isAlgebraic_maximalUnramifiedExtension : Algebra.IsAlgebraic K 𝔼 :=
  inferInstance

theorem exists_pow_card_pow_sub_mem_maximalIdeal (x : 𝒪[𝔼]) :
    ∃ n : ℕ, n ≠ 0 ∧ x ^ (Nat.card 𝓀[K] ^ n) - x ∈ 𝓂[𝔼] := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr
    ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩
  have hxz : integerInclusion hle z = x := rfl
  refine ⟨Module.finrank K L, Module.finrank_pos.ne', ?_⟩
  have := Fintype.ofFinite 𝓀[L]
  have hz : z ^ (Nat.card 𝓀[K] ^ Module.finrank K L) - z ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← card_residueField_of_unramified K L h,
      Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  rw [mem_maximalIdeal_intermediateField_iff] at hz ⊢
  rw [← hxz]
  simpa using hz

theorem exists_isPrimitiveRoot_residue {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : ResidueField 𝒪[𝔼], IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
  obtain ⟨hL, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  set L := IntermediateField.adjoin K {ζ}
  have := hL.1
  have hle := hL.le_maximalUnramifiedExtension
  have hmK := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have hm : ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : 𝓀[L]) ≠ 0 := natCast_residueField_ne_zero L hmK
  have hm0 : Nat.card 𝓀[K] ^ n - 1 ≠ 0 := by
    rintro h0
    rw [h0, Nat.cast_zero] at hmK
    exact hmK rfl
  set ζL : L := IntermediateField.AdjoinSimple.gen K ζ
  have hζL : IsPrimitiveRoot ζL (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := L.val) Subtype.val_injective
  set ζO : 𝒪[L] := ⟨ζL, mem_integer_of_pow_eq_one hm0 hζL.pow_eq_one⟩
  have hζO : IsPrimitiveRoot ζO (Nat.card 𝓀[K] ^ n - 1) :=
    hζL.of_map_of_injective (f := (𝒪[L]).subtype) Subtype.val_injective
  have hres := isPrimitiveRoot_residue hm hζO
  refine ⟨residue 𝒪[𝔼] (integerInclusion hle ζO), ?_⟩
  refine ⟨by rw [← map_pow, ← map_pow, hζO.pow_eq_one, map_one, map_one], fun l hl ↦ ?_⟩
  refine hres.dvd_of_pow_eq_one l ?_
  rw [← map_pow, ← map_pow] at hl
  rw [← map_pow, ← map_one (residue 𝒪[L]), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    mem_maximalIdeal_intermediateField_iff]
  rw [← map_one (residue 𝒪[𝔼]), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    mem_maximalIdeal_intermediateField_iff] at hl
  simpa using hl

variable [IsGalois K Ω]

theorem frobenius_integer_sub_pow_mem_maximalIdeal (x : 𝒪[𝔼]) :
    integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x -
      x ^ Nat.card 𝓀[K] ∈ 𝓂[𝔼] := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  obtain ⟨ξ, hξ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  rw [card_residueField_of_unramified K L h] at hξ
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have key : (maximalUnramifiedExtension K Ω).val.comp
      ((maximalUnramifiedExtensionFrobenius K Ω).toAlgHom.comp (IntermediateField.inclusion hle)) =
      L.val.comp (frobenius K L h).toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h1 : (IntermediateField.inclusion hle ξ) ^ (Nat.card 𝓀[K] ^ Module.finrank K L - 1) = 1 := by
      rw [← map_pow, hξ.pow_eq_one, map_one]
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm h1,
      frobenius_apply_of_pow_eq_one h hm hξ.pow_eq_one]
    simp
  set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr
    ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩
  have hz := frobenius_sub_pow_mem_maximalIdeal K L h z
  rw [mem_maximalIdeal_intermediateField_iff] at hz ⊢
  have hk := congrArg (fun f : L →ₐ[K] Ω ↦ f ⟨(x : 𝔼), hxL⟩) key
  simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] at hk
  convert hz using 2
  change ((maximalUnramifiedExtensionFrobenius K Ω (IntermediateField.inclusion hle ⟨(x : 𝔼), hxL⟩) :
      𝔼) : Ω) - _ = ((frobenius K L h ⟨(x : 𝔼), hxL⟩ : L) : Ω) - _
  rw [hk]
  rfl

end Frobenius

section FiniteFieldClosure

open Polynomial

variable {k k' : Type*} [Field k] [Finite k] [Field k'] [Algebra k k']

theorem isAlgebraic_of_pow_card_pow_eq_self {y : k'} {n : ℕ} (hn : n ≠ 0)
    (hy : y ^ (Nat.card k ^ n) = y) : IsAlgebraic k y :=
  ⟨X ^ (Nat.card k ^ n) - X, FiniteField.X_pow_card_pow_sub_X_ne_zero k hn Finite.one_lt_card,
    by simp [hy]⟩

omit [Algebra k k'] in

theorem splits_X_pow_card_pow_sub_X_of_isPrimitiveRoot {m : ℕ} {ζ : k'}
    (hζ : IsPrimitiveRoot ζ (Nat.card k ^ m - 1)) :
    Splits (X ^ (Nat.card k ^ m) - X : k'[X]) := by
  have h1 : 1 ≤ Nat.card k ^ m := Nat.one_le_pow _ _ Nat.card_pos
  have : (X ^ (Nat.card k ^ m) - X : k'[X]) = X * (X ^ (Nat.card k ^ m - 1) - C 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ]
    rw [map_one]
    ring
  rw [this]
  exact Splits.X.mul (X_pow_sub_one_splits hζ)

theorem isAlgClosed_of_isPrimitiveRoot [Algebra.IsAlgebraic k k']
    (h : ∀ m : ℕ, m ≠ 0 → ∃ ζ : k', IsPrimitiveRoot ζ (Nat.card k ^ m - 1)) : IsAlgClosed k' := by
  refine IsAlgClosed.of_exists_root _ fun p _ hirr ↦ ?_
  have := Fact.mk hirr
  let A := AdjoinRoot p
  let α : A := AdjoinRoot.root p
  have : Module.Finite k' A := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Algebra.IsAlgebraic k' A := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic k A := Algebra.IsAlgebraic.trans k k' A
  have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  let F := IntermediateField.adjoin k {α}
  have : FiniteDimensional k F := IntermediateField.adjoin.finiteDimensional hint
  have : Fintype k := Fintype.ofFinite k
  have : Finite F := Module.finite_of_finite k
  have : Fintype F := Fintype.ofFinite F
  set m := Module.finrank k F
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Fintype.card F = Nat.card k ^ m := by
    rw [Module.card_eq_pow_finrank (K := k) (V := F), Nat.card_eq_fintype_card]
  have hα : α ^ (Nat.card k ^ m) = α := by
    have := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen k α)
    rw [hcard] at this
    exact congrArg Subtype.val this
  obtain ⟨ζ, hζ⟩ := h m hm
  have hroot : ((X ^ (Nat.card k ^ m) - X : k'[X]).map (algebraMap k' A)).IsRoot α := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, IsRoot.def, eval_sub, eval_pow,
      eval_X, hα, sub_self]
  obtain ⟨β, hβ⟩ := (splits_X_pow_card_pow_sub_X_of_isPrimitiveRoot hζ).mem_range_of_isRoot
    (FiniteField.X_pow_card_pow_sub_X_ne_zero k' hm Finite.one_lt_card) hroot
  refine ⟨β, ?_⟩
  have h0 : aeval α p = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [← hβ, aeval_algebraMap_apply_eq_algebraMap_eval] at h0
  exact (map_eq_zero_iff _ (algebraMap k' A).injective).mp h0

end FiniteFieldClosure

section Residue

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

theorem exists_pow_card_pow_eq_self (y : 𝓀[𝔼]) :
    ∃ n : ℕ, n ≠ 0 ∧ y ^ (Nat.card 𝓀[K] ^ n) = y := by
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨n, hn, hx⟩ := exists_pow_card_pow_sub_mem_maximalIdeal x
  refine ⟨n, hn, ?_⟩
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hx

instance isAlgebraic_residueField : Algebra.IsAlgebraic 𝓀[K] 𝓀[𝔼] := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨n, hn, hy⟩ := exists_pow_card_pow_eq_self y
  exact isAlgebraic_of_pow_card_pow_eq_self hn hy

instance isAlgClosed_residueField : IsAlgClosed 𝓀[𝔼] :=
  isAlgClosed_of_isPrimitiveRoot (k := 𝓀[K]) fun _ hm ↦ exists_isPrimitiveRoot_residue hm

instance isAlgClosure_residueField :
    letI : Module.IsTorsionFree 𝓀[K] 𝓀[𝔼] := DivisionSemiring.to_moduleIsTorsionFree
    IsAlgClosure 𝓀[K] 𝓀[𝔼] :=
  letI : Module.IsTorsionFree 𝓀[K] 𝓀[𝔼] := DivisionSemiring.to_moduleIsTorsionFree
  ⟨isAlgClosed_residueField, isAlgebraic_residueField⟩

end Residue

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open IsLocalRing ValuativeRel

section Lift

variable {R : Type*} [CommRing R] {I : Ideal R}

variable (I) in

theorem factorPow_evalₐ {k n : ℕ} (hle : k ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := x.2 hle
  rw [SModEq.sub_mem] at h
  have hI : (I ^ k • ⊤ : Submodule R R) = I ^ k := by ext; simp
  rw [← neg_sub]
  exact neg_mem (hI ▸ h)

theorem pow_le_comap_pow {θ : R →+* R} (hθ : I ≤ I.comap θ) (n : ℕ) : I ^ n ≤ (I ^ n).comap θ :=
  Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hθ) n)

def adicCompletionQuotientMap (θ : R →+* R) (hθ : I ≤ I.comap θ) (n : ℕ) :
    AdicCompletion I R →+* R ⧸ I ^ n :=
  (Ideal.quotientMap (I ^ n) θ (pow_le_comap_pow hθ n)).comp
    (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)

theorem factorPow_comp_adicCompletionQuotientMap (θ : R →+* R) (hθ : I ≤ I.comap θ) {k n : ℕ}
    (hle : k ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (adicCompletionQuotientMap θ hθ n) =
      adicCompletionQuotientMap θ hθ k := by
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hk : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
    rw [← factorPow_evalₐ I hle, ← hr]
    rfl
  simp only [adicCompletionQuotientMap, RingHom.comp_apply, RingHom.coe_coe]
  rw [← hr, hk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

def adicCompletionMap (θ : R →+* R) (hθ : I ≤ I.comap θ) :
    AdicCompletion I R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (adicCompletionQuotientMap θ hθ)
    (factorPow_comp_adicCompletionQuotientMap θ hθ)

theorem evalₐ_adicCompletionMap (θ : R →+* R) (hθ : I ≤ I.comap θ) (n : ℕ)
    (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (adicCompletionMap θ hθ x) =
      Ideal.quotientMap (I ^ n) θ (pow_le_comap_pow hθ n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom I _ (factorPow_comp_adicCompletionQuotientMap θ hθ) n x

@[simp]
theorem adicCompletionMap_of (θ : R →+* R) (hθ : I ≤ I.comap θ) (r : R) :
    adicCompletionMap θ hθ (AdicCompletion.of I R r) = AdicCompletion.of I R (θ r) := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_adicCompletionMap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of,
    Ideal.quotientMap_mk]

theorem adicCompletionMap_id :
    adicCompletionMap (RingHom.id R) (Ideal.comap_id I).ge = RingHom.id (AdicCompletion I R) := by
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_adicCompletionMap, RingHom.id_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr, Ideal.quotientMap_mk, RingHom.id_apply]

theorem adicCompletionMap_comp (θ₁ θ₂ : R →+* R) (h₁ : I ≤ I.comap θ₁) (h₂ : I ≤ I.comap θ₂) :
    (adicCompletionMap θ₁ h₁).comp (adicCompletionMap θ₂ h₂) =
      adicCompletionMap (θ₁.comp θ₂)
        (by rw [← Ideal.comap_comap]; exact h₂.trans (Ideal.comap_mono h₁)) := by
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [RingHom.comp_apply, evalₐ_adicCompletionMap, evalₐ_adicCompletionMap,
    evalₐ_adicCompletionMap]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, RingHom.comp_apply]

end Lift

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "𝔅" => AdicCompletion (maximalIdeal R) R

variable (R) in

theorem algebraMap_adicCompletion_injective : Function.Injective (algebraMap R 𝔅) :=
  AdicCompletion.of_injective _ _

theorem maximalIdeal_adicCompletion_eq_span {ϖ : R} (hϖ : Irreducible ϖ) :
    maximalIdeal 𝔅 = Ideal.span {algebraMap R 𝔅 ϖ} := by
  rw [AdicCompletion.maximalIdeal_eq_map, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

theorem eq_zero_of_forall_mem_maximalIdeal_pow {x : 𝔅} (h : ∀ n, x ∈ maximalIdeal 𝔅 ^ n) :
    x = 0 :=
  IsHausdorff.haus' (I := maximalIdeal 𝔅) x fun n ↦ by
    simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top] using h n

theorem exists_eq_unit_mul_pow_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) {x : 𝔅} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : 𝔅ˣ), x = u * algebraMap R 𝔅 ϖ ^ n :=
  _root_.GroundTheory.Variant₂.N1.exists_eq_unit_mul_pow_adicCompletion hϖ hx

theorem algebraMap_pow_ne_zero {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    algebraMap R 𝔅 ϖ ^ n ≠ 0 := by
  rw [← map_pow, Ne, ← map_zero (algebraMap R 𝔅), (algebraMap_adicCompletion_injective R).eq_iff]
  exact pow_ne_zero n hϖ.ne_zero

instance isDomain_adicCompletion : IsDomain 𝔅 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : NoZeroDivisors 𝔅 := ⟨fun {x y} hxy ↦ by
    by_contra h
    push Not at h
    obtain ⟨m, u, rfl⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ h.1
    obtain ⟨n, v, rfl⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ h.2
    apply algebraMap_pow_ne_zero hϖ (m + n)
    have : ((u * v : 𝔅ˣ) : 𝔅) * algebraMap R 𝔅 ϖ ^ (m + n) = 0 := by
      rw [← hxy, Units.val_mul, pow_add]
      ring
    exact (Units.mul_right_eq_zero _).mp this⟩
  exact NoZeroDivisors.to_isDomain _

theorem irreducible_algebraMap_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap R 𝔅 ϖ) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (by simpa using algebraMap_pow_ne_zero hϖ 1) (maximalIdeal_adicCompletion_eq_span hϖ)

instance isDiscreteValuationRing_adicCompletion : IsDiscreteValuationRing 𝔅 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_algebraMap_adicCompletion hϖ, fun hx ↦ by
      obtain ⟨n, u, hu⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ hx
      exact ⟨n, u, by rw [hu, mul_comm]⟩⟩

theorem exists_sub_algebraMap_mem_pow (x : 𝔅) (n : ℕ) :
    ∃ r : R, x - algebraMap R 𝔅 r ∈ maximalIdeal 𝔅 ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm := maximalIdeal_adicCompletion_eq_span hϖ
  have hres : ∀ y : 𝔅, ∃ s : R, y - algebraMap R 𝔅 s ∈ maximalIdeal 𝔅 := by
    intro y
    obtain ⟨t, ht⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue 𝔅 y)
    obtain ⟨s, rfl⟩ := residue_surjective t
    refine ⟨s, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, ← ht, ResidueField.map_residue, sub_self]
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hr
    obtain ⟨c, hc⟩ := hr
    obtain ⟨s, hs⟩ := hres c
    rw [hm, Ideal.mem_span_singleton'] at hs
    obtain ⟨d, hd⟩ := hs
    refine ⟨r + ϖ ^ n * s, ?_⟩
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨d, ?_⟩
    rw [map_add, map_mul, map_pow]
    linear_combination (algebraMap R 𝔅 ϖ) ^ n * hd + hc

theorem ringHom_ext_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) {τ₁ τ₂ : 𝔅 →+* 𝔅}
    (h : ∀ r, τ₁ (algebraMap R 𝔅 r) = τ₂ (algebraMap R 𝔅 r))
    (hmem : τ₁ (algebraMap R 𝔅 ϖ) ∈ maximalIdeal 𝔅) : τ₁ = τ₂ := by
  have hm := maximalIdeal_adicCompletion_eq_span hϖ
  refine RingHom.ext fun x ↦ ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_maximalIdeal_pow fun n ↦ ?_
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_pow x n
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hr
  obtain ⟨c, hc⟩ := hr
  have hx : x = algebraMap R 𝔅 r + c * algebraMap R 𝔅 ϖ ^ n := by rw [hc]; ring
  rw [hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, h r, ← h ϖ]
  have : τ₁ (algebraMap R 𝔅 ϖ) ^ n ∈ maximalIdeal 𝔅 ^ n := Ideal.pow_mem_pow hmem n
  convert Ideal.mul_mem_left _ (τ₁ c - τ₂ c) this using 1
  ring

end DVR

section Automorphism

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "𝔅" => AdicCompletion (maximalIdeal R) R

theorem maximalIdeal_le_comap_ringEquiv (θ : R ≃+* R) :
    maximalIdeal R ≤ (maximalIdeal R).comap (θ : R →+* R) := by
  intro x hx
  rw [Ideal.mem_comap]
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  simpa using hu.map θ.symm

theorem adicCompletionMap_congr {θ₁ θ₂ : R →+* R} (h : θ₁ = θ₂)
    (h₁ : maximalIdeal R ≤ (maximalIdeal R).comap θ₁) (h₂ : maximalIdeal R ≤ (maximalIdeal R).comap θ₂) :
    adicCompletionMap θ₁ h₁ = adicCompletionMap θ₂ h₂ := by
  subst h
  rfl

theorem adicCompletionMap_eq_id {θ : R →+* R} (hθ : maximalIdeal R ≤ (maximalIdeal R).comap θ)
    (h : θ = RingHom.id R) : adicCompletionMap θ hθ = RingHom.id 𝔅 := by
  subst h
  exact adicCompletionMap_id

def adicCompletionRingEquiv (θ : R ≃+* R) : 𝔅 ≃+* 𝔅 :=
  RingEquiv.ofRingHom
    (adicCompletionMap (θ : R →+* R) (maximalIdeal_le_comap_ringEquiv θ))
    (adicCompletionMap (θ.symm : R →+* R) (maximalIdeal_le_comap_ringEquiv θ.symm))
    (by
      rw [adicCompletionMap_comp]
      exact adicCompletionMap_eq_id _ (by ext; simp))
    (by
      rw [adicCompletionMap_comp]
      exact adicCompletionMap_eq_id _ (by ext; simp))


variable {S : Type*} [CommRing S] [Algebra S R]

def adicCompletionAlgEquiv : (R ≃ₐ[S] R) →* (𝔅 ≃ₐ[S] 𝔅) where
  toFun θ :=
    AlgEquiv.ofRingEquiv (f := adicCompletionRingEquiv θ.toRingEquiv) (fun s ↦ by
      change adicCompletionMap _ _ (AdicCompletion.of _ R (algebraMap S R s)) =
        AdicCompletion.of _ R (algebraMap S R s)
      rw [adicCompletionMap_of]
      simp)
  map_one' := by
    ext1 x
    change adicCompletionMap _ _ x = x
    rw [adicCompletionMap_eq_id _ (by ext; simp)]
    rfl
  map_mul' θ₁ θ₂ := by
    ext1 x
    change adicCompletionMap _ _ x = adicCompletionMap _ _ (adicCompletionMap _ _ x)
    rw [← RingHom.comp_apply (adicCompletionMap _ _), adicCompletionMap_comp]
    exact congrArg (fun f : 𝔅 →+* 𝔅 ↦ f x) (adicCompletionMap_congr (by ext; simp) _ _)

@[simp]
theorem adicCompletionAlgEquiv_algebraMap (θ : R ≃ₐ[S] R) (r : R) :
    adicCompletionAlgEquiv θ (algebraMap R 𝔅 r) = algebraMap R 𝔅 (θ r) :=
  show adicCompletionMap _ _ (AdicCompletion.of _ R r) = _ from adicCompletionMap_of _ _ r


end Automorphism

section FixedRing

open Polynomial

theorem mem_range_of_pow_card_eq_self {F k : Type*} [Field F] [Finite F] [Field k] [Algebra F k]
    {y : k} (hy : y ^ Nat.card F = y) : y ∈ (algebraMap F k).range := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at hy
  have hs : Splits (X ^ Fintype.card F - X : F[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F hq]
    exact Finset.card_univ
  refine hs.mem_range_of_isRoot (FiniteField.X_pow_card_sub_X_ne_zero F hq) ?_
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, IsRoot.def, eval_sub, eval_pow,
    eval_X, hy, sub_self]

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

theorem isLocalHom_algebraMap_of_map_maximalIdeal
    (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsLocalHom (algebraMap A B) := by
  refine ⟨fun a ha ↦ ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 h
  have := Ideal.mem_map_of_mem (algebraMap A B) hm
  rw [hunr] at this
  exact (mem_maximalIdeal _).1 this ha

variable [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
include hunr hσ

omit [IsAdicComplete (maximalIdeal A) A] in

theorem exists_sub_algebraMap_mem_of_fixed {c : B} (hc : σ c = c) :
    ∃ d : A, c - algebraMap A B d ∈ maximalIdeal B := by
  have := isLocalHom_algebraMap_of_map_maximalIdeal hunr
  have hy : residue B c ^ Nat.card (ResidueField A) = residue B c := by rw [← hσ, hc]
  obtain ⟨t, ht⟩ := mem_range_of_pow_card_eq_self hy
  obtain ⟨d, rfl⟩ := residue_surjective t
  refine ⟨d, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← ht, ResidueField.algebraMap_residue, sub_self]

theorem mem_range_algebraMap_iff_fixed (b : B) : b ∈ (algebraMap A B).range ↔ σ b = b := by
  refine ⟨fun ⟨a, ha⟩ ↦ by rw [← ha, σ.commutes], fun hb ↦ ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set ϖ := algebraMap A B π with hϖdef
  have hmB : maximalIdeal B = Ideal.span {ϖ} := by
    rw [← hunr, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field B
    rw [hmB, h0, Ideal.span_singleton_eq_bot]
  have hϖm : ϖ ∈ maximalIdeal B := hmB ▸ Ideal.mem_span_singleton_self ϖ
  have hπm : π ∈ maximalIdeal A := hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hσϖ : σ ϖ = ϖ := σ.commutes π
  have step : ∀ c : B, σ c = c → ∃ d : A, ∃ c' : B, σ c' = c' ∧ c = algebraMap A B d + ϖ * c' := by
    intro c hc
    obtain ⟨d, hd⟩ := exists_sub_algebraMap_mem_of_fixed hunr σ hσ hc
    rw [hmB, Ideal.mem_span_singleton'] at hd
    obtain ⟨c', hc'⟩ := hd
    refine ⟨d, c', ?_, by rw [mul_comm, hc']; ring⟩
    have h1 := congrArg σ hc'
    rw [map_mul, hσϖ, map_sub, hc, σ.commutes, ← hc'] at h1
    exact mul_right_cancel₀ hϖ0 h1
  choose D N hN hDN using step
  let c : ℕ → {x : B // σ x = x} := fun n ↦
    Nat.rec ⟨b, hb⟩ (fun _ x ↦ ⟨N x.1 x.2, hN x.1 x.2⟩) n
  have hc_succ : ∀ n, (c (n + 1)).1 = N (c n).1 (c n).2 := fun _ ↦ rfl
  let d : ℕ → A := fun n ↦ D (c n).1 (c n).2
  let s : ℕ → A := fun n ↦ ∑ i ∈ Finset.range n, π ^ i * d i
  have hs : ∀ n, b = algebraMap A B (s n) + ϖ ^ n * (c n).1 := by
    intro n
    induction n with
    | zero => simp [s, c]
    | succ n ih =>
      have h := hDN (c n).1 (c n).2
      rw [← hc_succ] at h
      rw [ih, h]
      simp only [s, d, Finset.sum_range_succ, map_add, map_mul, map_pow]
      ring
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → s m ≡ s n [SMOD (maximalIdeal A ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, neg_mem_iff]
    simp only [s]
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    refine Ideal.sum_mem _ fun i hi ↦ ?_
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.mp hi).1 (Ideal.pow_mem_pow hπm i)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal A) s hcauchy
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := maximalIdeal B) _ fun n ↦ ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have hLn := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hLn
  have h1 : algebraMap A B (s n - L) ∈ maximalIdeal B ^ n := by
    rw [← hunr, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hLn
  have h2 : ϖ ^ n * (c n).1 ∈ maximalIdeal B ^ n :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖm n)
  have : algebraMap A B L - b = -(algebraMap A B (s n - L) + ϖ ^ n * (c n).1) := by
    rw [hs n, map_sub]
    ring
  rw [this, neg_mem_iff]
  exact add_mem h1 h2

end FixedRing

section Completed

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

abbrev CompletedUnramifiedIntegers : Type _ :=
  AdicCompletion (maximalIdeal 𝒪[maximalUnramifiedExtension K Ω]) 𝒪[maximalUnramifiedExtension K Ω]

local notation "𝔹" => CompletedUnramifiedIntegers K Ω

example : IsDiscreteValuationRing 𝔹 := inferInstance


instance isScalarTower_completedUnramifiedIntegers : IsScalarTower 𝒪[K] 𝒪[𝔼] 𝔹 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

theorem algebraMap_integer_completedUnramifiedIntegers_injective :
    Function.Injective (algebraMap 𝒪[𝔼] 𝔹) :=
  algebraMap_adicCompletion_injective _

theorem algebraMap_completedUnramifiedIntegers_injective :
    Function.Injective (algebraMap 𝒪[K] 𝔹) := by
  rw [IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[𝔼] 𝔹]
  exact (algebraMap_integer_completedUnramifiedIntegers_injective K Ω).comp
    (algebraMap_integer_injective K 𝔼)

theorem map_maximalIdeal_completedUnramifiedIntegers :
    (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝔹) = maximalIdeal 𝔹 := by
  rw [IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[𝔼] 𝔹, ← Ideal.map_map, map_maximalIdeal_integer,
    AdicCompletion.maximalIdeal_eq_map]

instance isLocalHom_algebraMap_completedUnramifiedIntegers : IsLocalHom (algebraMap 𝒪[K] 𝔹) :=
  isLocalHom_algebraMap_of_map_maximalIdeal (map_maximalIdeal_completedUnramifiedIntegers K Ω)

theorem irreducible_algebraMap_completedUnramifiedIntegers_iff (π : 𝒪[K]) :
    Irreducible (algebraMap 𝒪[K] 𝔹 π) ↔ Irreducible π := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine irreducible_iff.mpr ⟨fun hu ↦ h.not_isUnit (hu.map _), fun a b hab ↦ ?_⟩
    rw [hab, map_mul] at h
    exact (h.isUnit_or_isUnit rfl).imp (isUnit_of_map_unit _ _) (isUnit_of_map_unit _ _)
  · rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[𝔼] 𝔹]
    exact irreducible_algebraMap_adicCompletion (irreducible_algebraMap_uniformizer h)

def residueFieldCompletedUnramifiedIntegersEquiv :
    ResidueField 𝒪[𝔼] ≃+* ResidueField 𝔹 :=
  RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective 𝒪[𝔼])

instance isAlgClosed_residueField_completedUnramifiedIntegers : IsAlgClosed (ResidueField 𝔹) :=
  IsAlgClosed.of_ringEquiv _ _ (residueFieldCompletedUnramifiedIntegersEquiv K Ω)

instance isAlgebraic_residueField_completedUnramifiedIntegers :
    Algebra.IsAlgebraic 𝓀[K] (ResidueField 𝔹) :=
  AlgEquiv.isAlgebraic (R := 𝓀[K]) (A := ResidueField 𝒪[𝔼])
    (AlgEquiv.ofRingEquiv (f := residueFieldCompletedUnramifiedIntegersEquiv K Ω) fun t ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective t
      change ResidueField.map (algebraMap 𝒪[𝔼] 𝔹)
        (algebraMap 𝓀[K] (ResidueField 𝒪[𝔼]) (residue 𝒪[K] a)) = _
      rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue,
        ResidueField.map_residue]
      rfl)

instance isAlgClosure_residueField_completedUnramifiedIntegers :
    letI : Module.IsTorsionFree 𝓀[K] (ResidueField 𝔹) := DivisionSemiring.to_moduleIsTorsionFree
    IsAlgClosure 𝓀[K] (ResidueField 𝔹) :=
  letI : Module.IsTorsionFree 𝓀[K] (ResidueField 𝔹) := DivisionSemiring.to_moduleIsTorsionFree
  ⟨isAlgClosed_residueField_completedUnramifiedIntegers K Ω,
    isAlgebraic_residueField_completedUnramifiedIntegers K Ω⟩

end Completed

section Frobenius

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

local notation "𝔹" => CompletedUnramifiedIntegers K Ω

def completedUnramifiedAlgEquiv : (𝔼 ≃ₐ[K] 𝔼) →* (𝔹 ≃ₐ[𝒪[K]] 𝔹) :=
  adicCompletionAlgEquiv.comp (integerAlgEquivOfIsAlgebraic K 𝔼)

variable {K Ω}

@[simp]
theorem completedUnramifiedAlgEquiv_algebraMap (ρ : 𝔼 ≃ₐ[K] 𝔼) (x : 𝒪[𝔼]) :
    completedUnramifiedAlgEquiv K Ω ρ (algebraMap 𝒪[𝔼] 𝔹 x) =
      algebraMap 𝒪[𝔼] 𝔹 (integerAlgEquivOfIsAlgebraic K 𝔼 ρ x) :=
  adicCompletionAlgEquiv_algebraMap _ x


variable [IsGalois K Ω]

variable (K Ω) in

def completedFrobenius : 𝔹 ≃ₐ[𝒪[K]] 𝔹 :=
  completedUnramifiedAlgEquiv K Ω (maximalUnramifiedExtensionFrobenius K Ω)

theorem completedFrobenius_algebraMap (x : 𝒪[𝔼]) :
    completedFrobenius K Ω (algebraMap 𝒪[𝔼] 𝔹 x) = algebraMap 𝒪[𝔼] 𝔹
      (integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x) :=
  completedUnramifiedAlgEquiv_algebraMap _ x


theorem residue_completedFrobenius (x : 𝔹) :
    residue 𝔹 (completedFrobenius K Ω x) = residue 𝔹 x ^ Nat.card 𝓀[K] := by
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_pow x 1
  rw [pow_one] at hr
  set σ := completedFrobenius K Ω
  have h1 : residue 𝔹 x = residue 𝔹 (algebraMap 𝒪[𝔼] 𝔹 r) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hr
  have h2 : residue 𝔹 (σ x) = residue 𝔹 (σ (algebraMap 𝒪[𝔼] 𝔹 r)) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
    exact fun hu ↦ hr (by simpa using hu.map σ.symm)
  rw [h2, h1, completedFrobenius_algebraMap, ← map_pow, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff, ← map_pow, ← map_sub, AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (frobenius_integer_sub_pow_mem_maximalIdeal r)

theorem mem_range_algebraMap_iff_completedFrobenius (b : 𝔹) :
    b ∈ (algebraMap 𝒪[K] 𝔹).range ↔ completedFrobenius K Ω b = b :=
  have := isAdicComplete_integer K
  mem_range_algebraMap_iff_fixed (map_maximalIdeal_completedUnramifiedIntegers K Ω)
    (completedFrobenius K Ω).toAlgHom (residue_completedFrobenius) b

variable (K Ω) in

theorem completedUnramifiedIntegers_spec :
    IsDiscreteValuationRing 𝔹 ∧ IsAdicComplete (maximalIdeal 𝔹) 𝔹 ∧
      Function.Injective (algebraMap 𝒪[K] 𝔹) ∧
      (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝔹) = maximalIdeal 𝔹 ∧
      (∀ π : 𝒪[K], Irreducible (algebraMap 𝒪[K] 𝔹 π) ↔ Irreducible π) ∧
      IsAlgClosed (ResidueField 𝔹) ∧ Algebra.IsAlgebraic 𝓀[K] (ResidueField 𝔹) ∧
      (∀ x : 𝔹, residue 𝔹 (completedFrobenius K Ω x) = residue 𝔹 x ^ Nat.card 𝓀[K]) ∧
      (∀ b : 𝔹, completedFrobenius K Ω b = b ↔ b ∈ (algebraMap 𝒪[K] 𝔹).range) :=
  ⟨inferInstance, inferInstance, algebraMap_completedUnramifiedIntegers_injective K Ω,
    map_maximalIdeal_completedUnramifiedIntegers K Ω,
    irreducible_algebraMap_completedUnramifiedIntegers_iff K Ω, inferInstance, inferInstance,
    residue_completedFrobenius, fun b ↦ (mem_range_algebraMap_iff_completedFrobenius b).symm⟩

end Frobenius

section Finite

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

local notation "𝔹" => CompletedUnramifiedIntegers K Ω

def integerToCompleted {L : IntermediateField K Ω} (h : L ≤ 𝔼) : 𝒪[L] →ₐ[𝒪[K]] 𝔹 :=
  (IsScalarTower.toAlgHom 𝒪[K] 𝒪[𝔼] 𝔹).comp (integerInclusion h)

variable {K Ω}

@[simp]
theorem integerToCompleted_apply {L : IntermediateField K Ω} (h : L ≤ 𝔼) (x : 𝒪[L]) :
    integerToCompleted K Ω h x = algebraMap 𝒪[𝔼] 𝔹 (integerInclusion h x) :=
  rfl

theorem integerToCompleted_injective {L : IntermediateField K Ω} (h : L ≤ 𝔼) :
    Function.Injective (integerToCompleted K Ω h) :=
  (algebraMap_integer_completedUnramifiedIntegers_injective K Ω).comp (integerInclusion_injective h)



end Finite

section FiniteFrobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

local notation "𝔹" => CompletedUnramifiedIntegers K Ω

theorem maximalUnramifiedExtensionFrobenius_inclusion {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (y : L) :
    letI := hL.1
    ((maximalUnramifiedExtensionFrobenius K Ω
      (IntermediateField.inclusion hL.le_maximalUnramifiedExtension y) : 𝔼) : Ω) =
      ((frobenius K L hL.ramificationIndex_eq_one y : L) : Ω) := by
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  obtain ⟨ξ, hξ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  rw [card_residueField_of_unramified K L h] at hξ
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have key : (maximalUnramifiedExtension K Ω).val.comp
      ((maximalUnramifiedExtensionFrobenius K Ω).toAlgHom.comp (IntermediateField.inclusion hle)) =
      L.val.comp (frobenius K L h).toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop) ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h1 : (IntermediateField.inclusion hle ξ) ^ (Nat.card 𝓀[K] ^ Module.finrank K L - 1) = 1 := by
      rw [← map_pow, hξ.pow_eq_one, map_one]
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm h1,
      frobenius_apply_of_pow_eq_one h hm hξ.pow_eq_one]
    simp
  have hk := congrArg (fun f : L →ₐ[K] Ω ↦ f y) key
  simpa only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] using hk

theorem completedFrobenius_integerToCompleted {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (x : 𝒪[L]) :
    letI := hL.1
    completedFrobenius K Ω (integerToCompleted K Ω hL.le_maximalUnramifiedExtension x) =
      integerToCompleted K Ω hL.le_maximalUnramifiedExtension
        (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one) x) := by
  have := hL.1
  rw [integerToCompleted_apply, integerToCompleted_apply, completedFrobenius_algebraMap]
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  exact maximalUnramifiedExtensionFrobenius_inclusion hL (x : L)

end FiniteFrobenius

section Check

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

example : IsAdicComplete (maximalIdeal (CompletedUnramifiedIntegers K (SeparableClosure K)))
    (CompletedUnramifiedIntegers K (SeparableClosure K)) :=
  inferInstance

example (b : CompletedUnramifiedIntegers K (SeparableClosure K)) :
    completedFrobenius K (SeparableClosure K) b = b ↔
      b ∈ (algebraMap 𝒪[K] (CompletedUnramifiedIntegers K (SeparableClosure K))).range :=
  (completedUnramifiedIntegers_spec K (SeparableClosure K)).2.2.2.2.2.2.2.2 b

example (π : 𝒪[K]) (hπ : Irreducible π) :
    IsDomain (CompletedUnramifiedIntegers K (SeparableClosure K)) ∧
      IsDiscreteValuationRing (CompletedUnramifiedIntegers K (SeparableClosure K)) ∧
      Irreducible (algebraMap 𝒪[K] (CompletedUnramifiedIntegers K (SeparableClosure K)) π) ∧
      IsAlgClosed (ResidueField (CompletedUnramifiedIntegers K (SeparableClosure K))) ∧
      ∀ x : CompletedUnramifiedIntegers K (SeparableClosure K),
        residue _ ((completedFrobenius K (SeparableClosure K)).toAlgHom x) =
          residue _ x ^ Nat.card (ResidueField 𝒪[K]) :=
  ⟨inferInstance, inferInstance,
    (irreducible_algebraMap_completedUnramifiedIntegers_iff K (SeparableClosure K) π).mpr hπ,
    inferInstance, residue_completedFrobenius⟩

end Check

end GroundTheory.LocalField
end
end
