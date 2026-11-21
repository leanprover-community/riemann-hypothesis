import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerOrd
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
import GroundTheory.ProfiniteCohomology.GaloisCohomology.BrauerInflation
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolUnramified

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global FiniteSubfield
  GroundTheory.Global.SemiLocal groupCohomology

open scoped Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section CoboundaryUnits

variable {Kv Ωv : Type} [Field Kv] [Field Ωv] [Algebra Kv Ωv] [IsGalois Kv Ωv]

theorem cohomologyπ_galUnits_eq_zero_of_coboundary (z : cocycles (galUnits.{0} Kv Ωv) 2)
    (b : Gal(Ωv/Kv) → Ωvˣ) (hb : IsLocallyConstant b)
    (hz : ∀ u : Fin 2 → Gal(Ωv/Kv), cochainOf _ (cocycleι _ 2 z) u =
      Additive.ofMul (galUnitsHom Kv Ωv (u 0) (b (u 1)) / b (u 0 * u 1) * b (u 0))) :
    cohomologyπ _ 2 z = 0 := by
  have hw_loc : IsLocallyConstant (fun g : Fin 1 → Gal(Ωv/Kv) => Additive.ofMul (b (g 0))) :=
    (hb.comp_continuous (continuous_apply 0)).comp Additive.ofMul
  have hzw : z = (cochainsComplex (galUnits.{0} Kv Ωv)).toCycles 1 2 (mkCochain _ _ hw_loc) := by
    apply cocycleι_injective
    apply cochainOf_injective
    funext u
    have h1 := congrFun (cochainOf_cocycleι_toCycles (A := galUnits.{0} Kv Ωv) (i := 1)
      (mkCochain _ _ hw_loc)) u
    refine (hz u).trans (Eq.trans ?_ h1.symm)
    rw [cochainOf_mkCochain, inhomogeneousCochains_d_one_apply, galUnits_ρ_apply]
    rfl
  rw [hzw]
  exact cohomologyπ_toCycles _ 1 2 _

omit [IsGalois Kv Ωv] in

theorem toMul_galUnitsZ_coboundary (σ : Gal(Ωv/Kv)) (a b c : Additive Ωvˣ) :
    Additive.toMul ((galUnitsZ Kv Ωv).ρ σ a - b + c) =
      σ • Additive.toMul a / Additive.toMul b * Additive.toMul c :=
  rfl

end CoboundaryUnits

section ClassZero

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

theorem cohomologyπ_two_eq_zero_iff_locallyConstant (z : cocycles A 2) :
    cohomologyπ A 2 z = 0 ↔ ∃ w : (Fin 1 → G) → A, IsLocallyConstant w ∧
      ∀ u : Fin 2 → G, cochainOf A (cocycleι A 2 z) u =
        A.ρ (u 0) (w fun _ => u 1) - w (fun _ => u 0 * u 1) + w (fun _ => u 0) := by
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (homologyπ_eq_zero_iff (cochainsComplex A) z).1 hz
    have e : (ComplexShape.up ℕ).prev 2 = 1 := CochainComplex.prev_nat_succ 1
    let w₁ := ((cochainsComplex A).XIsoOfEq e).hom.hom w
    have hw₁ : ((cochainsComplex A).d 1 2).hom w₁ = ((cochainsComplex A).iCycles 2).hom z := by
      rw [← hw]
      exact congrArg (fun φ => φ.hom w) ((cochainsComplex A).XIsoOfEq_hom_comp_d e 2)
    refine ⟨cochainOf A w₁, isLocallyConstant_cochainOf w₁, fun u => ?_⟩
    have h1 := congrArg (cochainOf A) hw₁
    rw [cochainOf_d] at h1
    have h2 := congrFun h1 u
    rw [inhomogeneousCochains_d_one_apply] at h2
    exact h2.symm
  · rintro ⟨w, hw, hwz⟩
    have hzw : z = (cochainsComplex A).toCycles 1 2 (mkCochain A w hw) := by
      apply cocycleι_injective
      apply cochainOf_injective
      funext u
      rw [hwz u, cochainOf_cocycleι_toCycles, cochainOf_mkCochain, inhomogeneousCochains_d_one_apply]
    rw [hzw]
    exact cohomologyπ_toCycles A 1 2 _

end ClassZero

section DTwo

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

theorem inhomogeneousCochains_d_two_apply' (f : (Fin 2 → G) → A) (u : Fin 3 → G) :
    (inhomogeneousCochains.d A 2).hom f u =
      A.ρ (u 0) (f ![u 1, u 2]) - f ![u 0 * u 1, u 2] + f ![u 0, u 1 * u 2] - f ![u 0, u 1] := by
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three]
  have h0 : Fin.contractNth (0 : Fin 3) (· * ·) u = ![u 0 * u 1, u 2] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp)]; rfl
  have h1 : Fin.contractNth (1 : Fin 3) (· * ·) u = ![u 0, u 1 * u 2] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl
  have h2 : Fin.contractNth (2 : Fin 3) (· * ·) u = ![u 0, u 1] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
  have h3 : (fun i : Fin 2 => u i.succ) = ![u 1, u 2] := by
    funext i
    fin_cases i <;> rfl
  rw [h0, h1, h2, h3]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_one, neg_smul, one_smul,
    Nat.reduceAdd, even_two, Even.neg_pow, one_pow]
  have : ((-1 : k) ^ 3) = -1 := by norm_num
  rw [this, neg_smul, one_smul]
  abel

end DTwo

section Level

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  (F : FiniteSubfield) [Fact (K ≤ F)] [Normal K.1 F.1]

theorem decompHom_smul_placeOfEmbedding'
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    decompHom (v.adicCompletion K.1) (embedLevel ι F) σ • placeOfEmbedding ι F =
      placeOfEmbedding ι F := by
  set τ := decompHom (v.adicCompletion K.1) (embedLevel ι F) σ
  set w₀ := placeOfEmbedding ι F
  have hu : w₀.1 = τ • (τ⁻¹ • w₀).1 := eq_smul_inv_smul v τ w₀
  let j := σ.symm.toAlgHom.comp
    ((completionEmbedding ι F).comp (galEquiv v τ (τ⁻¹ • w₀).1 w₀.1 hu).toAlgHom)
  have hj : ∀ x : F.1, j (algebraMap F.1 _ x) = ι x := by
    intro x
    change σ.symm (completionEmbedding ι F (galEquiv v τ (τ⁻¹ • w₀).1 w₀.1 hu
      (algebraMap F.1 _ x))) = ι x
    rw [galEquiv_algebraMap, completionEmbedding_algebraMap]
    have h := decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι F) σ x
    rw [embedLevel_apply, embedLevel_apply] at h
    rw [h, AlgEquiv.symm_apply_apply]
  have h := eq_placeOfEmbedding ι F j hj
  calc τ • w₀ = τ • (τ⁻¹ • w₀) := by rw [h]
    _ = w₀ := smul_inv_smul τ w₀

def placeDecompHom :
    Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →*
      MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal :=
  (decompHom (v.adicCompletion K.1) (embedLevel ι F)).codRestrict _ fun σ ↦
    MulAction.mem_stabilizer_iff.2
      (congrArg (fun u : PlacesOver F.1 v ↦ u.1.asIdeal) (decompHom_smul_placeOfEmbedding' ι F σ))

theorem coe_placeDecompHom (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    (placeDecompHom ι F σ : Gal(F.1/K.1)) = decompHom (v.adicCompletion K.1) (embedLevel ι F) σ :=
  rfl

theorem ι_placeDecompHom_apply
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) (x : F.1) :
    ι ((placeDecompHom ι F σ : Gal(F.1/K.1)) x : F.1) = σ (ι x) :=
  decompHom_apply (Kv := v.adicCompletion K.1) (embedLevel ι F) σ x

theorem continuous_placeDecompHom : Continuous (placeDecompHom ι F) :=
  (continuous_decompHom (embedLevel ι F)).subtype_mk _

theorem completionEmbedding_placeDecompHom_smul
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (y : (placeOfEmbedding ι F).1.adicCompletion F.1) :
    completionEmbedding ι F (placeDecompHom ι F σ • y) = σ (completionEmbedding ι F y) := by
  have : (completionEmbedding ι F).comp
      (decompositionAlgEquiv v (placeOfEmbedding ι F).1 (placeDecompHom ι F σ)).toAlgHom =
      σ.toAlgHom.comp (completionEmbedding ι F) := by
    apply algHom_ext_adicCompletion
    intro x
    change completionEmbedding ι F (decompositionAlgEquiv v (placeOfEmbedding ι F).1
      (placeDecompHom ι F σ) (algebraMap F.1 _ x)) = σ (completionEmbedding ι F (algebraMap F.1 _ x))
    rw [decompositionAlgEquiv_algebraMap, completionEmbedding_algebraMap,
      completionEmbedding_algebraMap, ι_placeDecompHom_apply]
  exact DFunLike.congr_fun this y

section CompField

@[irreducible]
def compField : IntermediateField (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
  (completionEmbedding ι F).fieldRange

omit [Normal K.1 F.1] in
theorem compField_def : compField ι F = (completionEmbedding ι F).fieldRange := by
  with_unfolding_all rfl

def compEquiv : (placeOfEmbedding ι F).1.adicCompletion F.1 ≃ₐ[v.adicCompletion K.1] compField ι F :=
  (AlgEquiv.ofInjectiveField (completionEmbedding ι F)).trans
    (IntermediateField.equivOfEq (compField_def ι F).symm)

omit [Normal K.1 F.1] in
@[simp]
theorem coe_compEquiv_apply (y : (placeOfEmbedding ι F).1.adicCompletion F.1) :
    ((compEquiv ι F y : compField ι F) : AlgebraicClosure (v.adicCompletion K.1)) =
      completionEmbedding ι F y :=
  rfl

instance finiteDimensional_compField : FiniteDimensional (v.adicCompletion K.1) (compField ι F) :=
  have : Module.Finite (v.adicCompletion K.1) ((placeOfEmbedding ι F).1.adicCompletion F.1) :=
    finite_adicCompletion v (placeOfEmbedding ι F).1
  LinearEquiv.finiteDimensional (compEquiv ι F).toLinearEquiv

instance isGalois_finiteSubfield_of_normal : IsGalois K.1 F.1 := ⟨⟩

instance normal_compField : Normal (v.adicCompletion K.1) (compField ι F) :=
  have : IsGalois (v.adicCompletion K.1) ((placeOfEmbedding ι F).1.adicCompletion F.1) :=
    isGalois_adicCompletion v (placeOfEmbedding ι F).1
  Normal.of_algEquiv (compEquiv ι F)

omit [Normal K.1 F.1] in
theorem ι_mem_compField (x : F.1) : ι x ∈ compField ι F := by
  rw [compField_def]
  exact ⟨algebraMap F.1 _ x, completionEmbedding_algebraMap ι F x⟩

def embedComp : F.1 →ₐ[K.1] compField ι F where
  toFun x := ⟨ι x, ι_mem_compField ι F x⟩
  map_one' := Subtype.ext (map_one ι)
  map_mul' x y := Subtype.ext (map_mul ι (x : ℚ̄) y)
  map_zero' := Subtype.ext (map_zero ι)
  map_add' x y := Subtype.ext (map_add ι (x : ℚ̄) y)
  commutes' a := Subtype.ext (ι.commutes a)

omit [Normal K.1 F.1] in
@[simp]
theorem coe_embedComp_apply (x : F.1) :
    ((embedComp ι F x : compField ι F) : AlgebraicClosure (v.adicCompletion K.1)) = ι x :=
  rfl

end CompField

end Level

section Inflation

variable {G Γ : Type} [Group G] [TopologicalSpace G] [CompactSpace G] [Group Γ]

theorem exists_int_coboundary_of_surjective (r : G →* Γ) (hr : Function.Surjective r)
    (β : Γ × Γ → ℤ) (h : G → ℤ) (hh : IsLocallyConstant h)
    (hβ : ∀ σ τ, h τ - h (σ * τ) + h σ = β (r σ, r τ)) :
    ∃ g : Γ → ℤ, ∀ a b, g b - g (a * b) + g a = β (a, b) := by

  have h1 : ∀ σ, β (r σ, 1) = h 1 := by
    intro σ
    have := hβ σ 1
    rw [map_one, mul_one] at this
    linarith
  have hmul : ∀ σ n, r n = 1 → h (σ * n) = h σ + h n - h 1 := by
    intro σ n hn
    have := hβ σ n
    rw [hn, h1] at this
    linarith

  have hfin : (Set.range h).Finite := hh.range_finite
  have hk : ∀ n, r n = 1 → h n = h 1 := by
    intro n hn
    have hpow : ∀ m : ℕ, h (n ^ m) - h 1 = m * (h n - h 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, hmul _ _ hn]
        push_cast
        linarith
    by_contra hne
    have hne' : h n - h 1 ≠ 0 := sub_ne_zero.2 hne
    have hinj : Function.Injective fun m : ℕ => h (n ^ m) := by
      intro m m' hmm
      have e1 := hpow m
      have e2 := hpow m'
      simp only at hmm
      rw [hmm] at e1
      have : (m : ℤ) * (h n - h 1) = m' * (h n - h 1) := by rw [← e1, ← e2]
      exact_mod_cast mul_right_cancel₀ hne' this
    exact Set.infinite_range_of_injective hinj (hfin.subset (Set.range_comp_subset_range _ _))
  have hconst : ∀ σ n, r n = 1 → h (σ * n) = h σ := by
    intro σ n hn
    rw [hmul σ n hn, hk n hn]
    ring
  have hfac : ∀ σ σ', r σ = r σ' → h σ = h σ' := by
    intro σ σ' he
    have hn : r (σ⁻¹ * σ') = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [← hconst σ (σ⁻¹ * σ') hn, mul_inv_cancel_left]
  choose s hs using hr
  refine ⟨fun a => h (s a), fun a b => ?_⟩
  have := hβ (s a) (s b)
  rw [hs a, hs b] at this
  rw [← this]
  show h (s b) - h (s (a * b)) + h (s a) = _
  rw [hfac (s (a * b)) (s a * s b) (by rw [map_mul, hs, hs, hs])]

end Inflation

section UnitsVanish

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

open AdicLiesOver

include v in

theorem isMulCoboundary₂_of_valuation (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (α : MulAction.stabilizer Gal(L/K) w.asIdeal × MulAction.stabilizer Gal(L/K) w.asIdeal →
      (w.adicCompletion L)ˣ) (hα : IsMulCocycle₂ α)
    (g : MulAction.stabilizer Gal(L/K) w.asIdeal → ℤ)
    (hg : ∀ a b, Valued.v (α (a, b) : w.adicCompletion L) = WithZero.exp (-(g b - g (a * b) + g a))) :
    IsMulCoboundary₂ α := by
  obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer K
  set π0 : w.adicCompletion L := algebraMap L (w.adicCompletion L) (algebraMap K L ϖ) with hπ0def
  have hπv : Valued.v π0 = WithZero.exp (-1) := by
    rw [hπ0def, show algebraMap L (w.adicCompletion L) (algebraMap K L ϖ) =
      ((algebraMap K L ϖ : L) : w.adicCompletion L) from rfl, w.valuedAdicCompletion_eq_valuation',
      ← HeightOneSpectrum.valuation_liesOver L v w ϖ, Ideal.ramificationIdx'_eq_ramificationIdx' v.asIdeal w.asIdeal
        (Ideal.map_ne_bot_of_ne_bot v.ne_bot), he, pow_one, hϖ]
  have hπ0 : π0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hπv
    exact WithZero.exp_ne_zero hπv.symm
  set π : (w.adicCompletion L)ˣ := Units.mk0 π0 hπ0
  have hπinv : ∀ (a : MulAction.stabilizer Gal(L/K) w.asIdeal) (n : ℤ), a • π ^ n = π ^ n := by
    intro a n
    rw [smul_zpow']
    congr 1
    apply Units.ext
    show decompositionAlgEquiv v w a π0 = π0
    rw [hπ0def, decompositionAlgEquiv_algebraMap, AlgEquiv.commutes]
  have hπpow : ∀ n : ℤ, Valued.v (((π ^ n : (w.adicCompletion L)ˣ)) : w.adicCompletion L) =
      WithZero.exp (-n) := by
    intro n
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
    change Valued.v π0 ^ n = _
    rw [hπv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

  obtain ⟨e, he_def⟩ : ∃ e : MulAction.stabilizer Gal(L/K) w.asIdeal ×
      MulAction.stabilizer Gal(L/K) w.asIdeal → ℤ, e = fun p => g p.2 - g (p.1 * p.2) + g p.1 :=
    ⟨_, rfl⟩
  have he_ab : ∀ a b, e (a, b) = g b - g (a * b) + g a := by intro a b; rw [he_def]
  have he_cocycle : ∀ a b c, e (a * b, c) + e (a, b) = e (b, c) + e (a, b * c) := by
    intro a b c
    rw [he_ab, he_ab, he_ab, he_ab, mul_assoc]
    ring

  obtain ⟨α₁, hα₁_def⟩ : ∃ α₁ : MulAction.stabilizer Gal(L/K) w.asIdeal ×
      MulAction.stabilizer Gal(L/K) w.asIdeal → (w.adicCompletion L)ˣ,
      α₁ = fun p => α p * π ^ (-e p) := ⟨_, rfl⟩
  have hα₁_ab : ∀ p, α₁ p = α p * π ^ (-e p) := by intro p; rw [hα₁_def]
  have hv₁ : ∀ p, Valued.v (α₁ p : w.adicCompletion L) = 1 := by
    rintro ⟨a, b⟩
    rw [hα₁_ab, Units.val_mul, map_mul, hg a b, hπpow, neg_neg, he_ab, ← WithZero.exp_add,
      neg_add_cancel, WithZero.exp_zero]
  have hα₁ : IsMulCocycle₂ α₁ := by
    intro a b c
    rw [hα₁_ab, hα₁_ab, hα₁_ab, hα₁_ab, smul_mul', hπinv]
    calc α (a * b, c) * π ^ (-e (a * b, c)) * (α (a, b) * π ^ (-e (a, b)))
        = (α (a * b, c) * α (a, b)) * π ^ (-(e (a * b, c) + e (a, b))) := by
          rw [neg_add, zpow_add, mul_mul_mul_comm]
      _ = (a • α (b, c) * α (a, b * c)) * π ^ (-(e (b, c) + e (a, b * c))) := by
          rw [hα a b c, he_cocycle]
      _ = a • α (b, c) * π ^ (-e (b, c)) * (α (a, b * c) * π ^ (-e (a, b * c))) := by
          rw [neg_add, zpow_add, mul_mul_mul_comm]
  have hmem : ∀ p, (α₁ p : w.adicCompletion L) ∈ w.adicCompletionIntegers L := fun p =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (K := L) (v := w)).2 (hv₁ p).le
  have hmem' : ∀ p, (((α₁ p)⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈
      w.adicCompletionIntegers L := by
    intro p
    refine (HeightOneSpectrum.mem_adicCompletionIntegers (K := L) (v := w)).2 (le_of_eq ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv₁ p, inv_one]
  let u : MulAction.stabilizer Gal(L/K) w.asIdeal × MulAction.stabilizer Gal(L/K) w.asIdeal →
      (w.adicCompletionIntegers L)ˣ := fun p =>
    ⟨⟨α₁ p, hmem p⟩, ⟨((α₁ p)⁻¹ : (w.adicCompletion L)ˣ), hmem' p⟩,
      Subtype.ext (Units.mul_inv (α₁ p)), Subtype.ext (Units.inv_mul (α₁ p))⟩
  let toFw : (w.adicCompletionIntegers L)ˣ →* (w.adicCompletion L)ˣ :=
    Units.map (w.adicCompletionIntegers L).subtype.toMonoidHom
  have htoFw_inj : Function.Injective toFw := fun x y h =>
    Units.ext (Subtype.ext (congrArg Units.val h))
  have htoFw_smul : ∀ (a : MulAction.stabilizer Gal(L/K) w.asIdeal) y, toFw (a • y) = a • toFw y :=
    fun _ _ => rfl
  have hu_coe : ∀ p, toFw (u p) = α₁ p := fun p => Units.ext rfl
  have hu : IsMulCocycle₂ u := by
    intro a b c
    apply htoFw_inj
    rw [map_mul, map_mul, htoFw_smul, hu_coe, hu_coe, hu_coe, hu_coe]
    exact hα₁ a b c

  have hz := isZero_groupCohomology_decomposition_integerUnits v w he (n := 2) (by norm_num)
  have h0 : (ConcreteCategory.hom (groupCohomology.H2π
      (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
        (w.adicCompletionIntegers L)ˣ))) (groupCohomology.cocyclesOfIsMulCocycle₂ hu) = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 hz).elim _ _
  rw [groupCohomology.H2π_eq_zero_iff] at h0
  obtain ⟨x, hx⟩ := groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂ _ h0
  refine ⟨fun a => toFw (x a) * π ^ g a, fun a b => ?_⟩
  have hxab : a • x b / x (a * b) * x a = u (a, b) := hx a b
  have hxab' := congrArg toFw hxab
  rw [map_mul, map_div, htoFw_smul, hu_coe, hα₁_ab] at hxab'
  simp only [smul_mul', hπinv]
  calc a • toFw (x b) * π ^ g b / (toFw (x (a * b)) * π ^ g (a * b)) * (toFw (x a) * π ^ g a)
      = (a • toFw (x b) / toFw (x (a * b)) * toFw (x a)) * π ^ e (a, b) := by
        rw [he_ab]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_zpow, add_zsmul, sub_zsmul]
        abel
    _ = α (a, b) := by
        rw [hxab', mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

end UnitsVanish

section Main

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  (F : FiniteSubfield) [Fact (K ≤ F)] [Normal K.1 F.1]

set_option synthInstance.maxHeartbeats 400000 in
instance mulDistribMulAction_gal_units_finiteSubfield :
    MulDistribMulAction Gal(F.1/K.1) F.1ˣ :=
  AlgEquiv.instMulDistribMulActionUnits

def ordPlace (f : F.1ˣ) : ℤ :=
  -WithZero.log ((placeOfEmbedding ι F).1.valuation F.1 (f : F.1))

set_option maxHeartbeats 2000000 in

theorem placeDecompHom_surjective : Function.Surjective (placeDecompHom ι F) := by
  intro d
  obtain ⟨τ, hτ⟩ : ∃ τ : compField ι F ≃ₐ[v.adicCompletion K.1] compField ι F, ∀ y,
      τ y = compEquiv ι F (decompositionAlgEquiv v (placeOfEmbedding ι F).1 d ((compEquiv ι F).symm y)) :=
    ⟨(compEquiv ι F).symm.trans ((decompositionAlgEquiv v (placeOfEmbedding ι F).1 d).trans
      (compEquiv ι F)), fun _ => rfl⟩
  refine ⟨τ.liftNormal (AlgebraicClosure (v.adicCompletion K.1)), Subtype.ext ?_⟩
  rw [coe_placeDecompHom, decompHom_eq_iff]
  intro x
  have e : ∀ y : F.1, embedLevel ι F y = algebraMap (compField ι F) (AlgebraicClosure (v.adicCompletion K.1))
      (compEquiv ι F (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) y)) := by
    intro y
    rw [IntermediateField.algebraMap_apply, coe_compEquiv_apply, completionEmbedding_algebraMap,
      embedLevel_apply]
  rw [e, e, AlgEquiv.liftNormal_commutes, hτ, AlgEquiv.symm_apply_apply,
    decompositionAlgEquiv_algebraMap]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem exists_mulCoboundary_of_ord (he : (placeOfEmbedding ι F).1.asIdeal.ramificationIdx (𝓞 K.1) = 1)
    (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) (hc : IsMulCocycle₂ c)
    (h : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) → ℤ) (hh : IsLocallyConstant h)
    (hhc : ∀ σ τ, h τ - h (σ * τ) + h σ = ordPlace ι F
      (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
        decompHom (v.adicCompletion K.1) (embedLevel ι F) τ))) :
    ∃ b : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →
        (AlgebraicClosure (v.adicCompletion K.1))ˣ,
      IsLocallyConstant b ∧ ∀ σ τ, σ • b τ / b (σ * τ) * b σ =
        Units.map (embedLevel ι F).toRingHom.toMonoidHom
          (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
            decompHom (v.adicCompletion K.1) (embedLevel ι F) τ)) := by
  have : CompactSpace Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) :=
    galois_compactSpace _ _

  obtain ⟨g, hg⟩ := exists_int_coboundary_of_surjective (placeDecompHom ι F)
    (placeDecompHom_surjective ι F)
    (fun p => ordPlace ι F (c ((p.1 : Gal(F.1/K.1)), (p.2 : Gal(F.1/K.1))))) h hh (fun σ τ => hhc σ τ)

  let alg : F.1ˣ →* ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ :=
    Units.map (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1)).toMonoidHom
  have halg_smul : ∀ (a : MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal) y,
      alg ((a : Gal(F.1/K.1)) • y) = a • alg y := by
    intro a y
    apply Units.ext
    change algebraMap F.1 _ ((a : Gal(F.1/K.1)) (y : F.1)) =
      decompositionAlgEquiv v (placeOfEmbedding ι F).1 a (algebraMap F.1 _ (y : F.1))
    rw [decompositionAlgEquiv_algebraMap]
  let α : MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal ×
      MulAction.stabilizer Gal(F.1/K.1) (placeOfEmbedding ι F).1.asIdeal →
      ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ :=
    fun p => alg (c ((p.1 : Gal(F.1/K.1)), (p.2 : Gal(F.1/K.1))))
  have hα : IsMulCocycle₂ α := by
    intro a b d
    have := congrArg alg (hc a b d)
    simp only [map_mul, halg_smul] at this
    exact this
  have hval : ∀ y : F.1ˣ, Valued.v ((alg y : ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ) :
      (placeOfEmbedding ι F).1.adicCompletion F.1) = WithZero.exp (-ordPlace ι F y) := by
    intro y
    change Valued.v ((y : F.1) : (placeOfEmbedding ι F).1.adicCompletion F.1) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ordPlace, neg_neg, WithZero.exp_log]
    exact (map_ne_zero _).2 y.ne_zero
  have hg' : ∀ a b, Valued.v (α (a, b) : (placeOfEmbedding ι F).1.adicCompletion F.1) =
      WithZero.exp (-(g b - g (a * b) + g a)) := by
    intro a b
    rw [hval, hg a b]
  obtain ⟨β, hβ⟩ := isMulCoboundary₂_of_valuation v (placeOfEmbedding ι F).1 he α hα g hg'

  let j : ((placeOfEmbedding ι F).1.adicCompletion F.1)ˣ →* (AlgebraicClosure (v.adicCompletion K.1))ˣ :=
    Units.map (completionEmbedding ι F).toRingHom.toMonoidHom
  have hj_smul : ∀ σ y, σ • j y = j (placeDecompHom ι F σ • y) := by
    intro σ y
    apply Units.ext
    exact (completionEmbedding_placeDecompHom_smul ι F σ (y : (placeOfEmbedding ι F).1.adicCompletion F.1)).symm
  refine ⟨fun σ => j (β (placeDecompHom ι F σ)),
    (IsLocallyConstant.of_discrete (fun d => j (β d))).comp_continuous (continuous_placeDecompHom ι F),
    fun σ τ => ?_⟩
  rw [hj_smul, ← map_div, ← map_mul, map_mul (placeDecompHom ι F), hβ]
  apply Units.ext
  change completionEmbedding ι F (algebraMap F.1 _ _) = _
  rw [completionEmbedding_algebraMap]
  rfl

def ordComp (y : Additive (compField ι F)ˣ) : ℤ :=
  -WithZero.log (Valued.v (((compEquiv ι F).symm (y.toMul : compField ι F)) :
    (placeOfEmbedding ι F).1.adicCompletion F.1))

omit [Normal K.1 F.1] in
set_option maxHeartbeats 2000000 in
theorem ordComp_add (y y' : Additive (compField ι F)ˣ) :
    ordComp ι F (y + y') = ordComp ι F y + ordComp ι F y' := by
  have h0 : ∀ z : Additive (compField ι F)ˣ, Valued.v (((compEquiv ι F).symm (z.toMul : compField ι F)) :
      (placeOfEmbedding ι F).1.adicCompletion F.1) ≠ 0 := fun z =>
    (map_ne_zero _).2 ((map_ne_zero _).2 (z.toMul).ne_zero)
  unfold ordComp
  rw [toMul_add, Units.val_mul, map_mul, map_mul, WithZero.log_mul (h0 y) (h0 y'), neg_add]

omit [Normal K.1 F.1] in
theorem ordComp_neg (y : Additive (compField ι F)ˣ) : ordComp ι F (-y) = -ordComp ι F y := by
  have := ordComp_add ι F y (-y)
  rw [add_neg_cancel] at this
  have h1 : ordComp ι F 0 = 0 := by
    simp [ordComp]
  linarith

omit [Normal K.1 F.1] in
theorem ordComp_sub (y y' : Additive (compField ι F)ˣ) :
    ordComp ι F (y - y') = ordComp ι F y - ordComp ι F y' := by
  rw [sub_eq_add_neg, ordComp_add, ordComp_neg, ← sub_eq_add_neg]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem ordComp_smul (γ : Gal(compField ι F/v.adicCompletion K.1)) (y : (compField ι F)ˣ) :
    ordComp ι F (Additive.ofMul (Units.map (γ : compField ι F →* compField ι F) y)) =
      ordComp ι F (Additive.ofMul y) := by
  obtain ⟨d, hd⟩ := (decompositionToLocal_bijective v (placeOfEmbedding ι F).1).2
    ((compEquiv ι F).trans (γ.trans (compEquiv ι F).symm))
  have key : (compEquiv ι F).symm (γ (y : compField ι F)) =
      decompositionAlgEquiv v (placeOfEmbedding ι F).1 d ((compEquiv ι F).symm (y : compField ι F)) := by
    have := DFunLike.congr_fun hd ((compEquiv ι F).symm (y : compField ι F))
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [ordComp, toMul_ofMul]
  change -WithZero.log (Valued.v ((compEquiv ι F).symm (γ (y : compField ι F)))) = _
  rw [key, valued_decompositionAlgEquiv]

theorem ordComp_embedComp (f : F.1ˣ) :
    ordComp ι F (Additive.ofMul (Units.map (embedComp ι F).toRingHom.toMonoidHom f)) = ordPlace ι F f := by
  have h : (compEquiv ι F).symm (embedComp ι F (f : F.1)) =
      algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) (f : F.1) := by
    apply (compEquiv ι F).injective
    rw [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_compEquiv_apply, completionEmbedding_algebraMap, coe_embedComp_apply]
  simp only [ordComp, ordPlace, toMul_ofMul]
  change -WithZero.log (Valued.v ((compEquiv ι F).symm (embedComp ι F (f : F.1)))) = _
  rw [h]
  change -WithZero.log (Valued.v ((f : F.1) : (placeOfEmbedding ι F).1.adicCompletion F.1)) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

abbrev compDecomp : Gal(compField ι F/v.adicCompletion K.1) →* Gal(F.1/K.1) :=
  decompHom (v.adicCompletion K.1) (embedComp ι F)

set_option maxHeartbeats 4000000 in

theorem compDecomp_restrictNormalHom
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    compDecomp ι F (AlgEquiv.restrictNormalHom (compField ι F) σ) =
      decompHom (v.adicCompletion K.1) (embedLevel ι F) σ := by
  symm
  rw [decompHom_eq_iff]
  intro x
  rw [embedLevel_apply, embedLevel_apply, ← coe_embedComp_apply, ← coe_embedComp_apply,
    decompHom_apply]
  exact AlgEquiv.restrictNormal_commutes σ (compField ι F) (embedComp ι F x)

theorem units_embedComp_galUnitsHom (γ : Gal(compField ι F/v.adicCompletion K.1)) (f : F.1ˣ) :
    Units.map (embedComp ι F).toRingHom.toMonoidHom (galUnitsHom K.1 F.1 (compDecomp ι F γ) f) =
      galUnitsHom (v.adicCompletion K.1) (compField ι F) γ
        (Units.map (embedComp ι F).toRingHom.toMonoidHom f) := by
  apply Units.ext
  exact decompHom_apply (embedComp ι F) γ (f : F.1)

def compCocycleFun (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) :
    Gal(compField ι F/v.adicCompletion K.1) × Gal(compField ι F/v.adicCompletion K.1) →
      Additive (compField ι F)ˣ :=
  fun p => Additive.ofMul (Units.map (embedComp ι F).toRingHom.toMonoidHom
    (c (compDecomp ι F p.1, compDecomp ι F p.2)))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem compCocycleFun_mem (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) (hc : IsMulCocycle₂ c) :
    compCocycleFun ι F c ∈ groupCohomology.cocycles₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F)) := by
  have hc' : ∀ g h j, c (g * h, j) * c (g, h) = galUnitsHom K.1 F.1 g (c (h, j)) * c (g, h * j) := hc
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h j
  have e := hc' (compDecomp ι F g) (compDecomp ι F h) (compDecomp ι F j)
  have m1 : compDecomp ι F (g * h) = compDecomp ι F g * compDecomp ι F h := map_mul _ g h
  have m2 : compDecomp ι F (h * j) = compDecomp ι F h * compDecomp ι F j := map_mul _ h j
  have s := units_embedComp_galUnitsHom ι F g (c (compDecomp ι F h, compDecomp ι F j))
  have key' : c (compDecomp ι F (g * h), compDecomp ι F j) * c (compDecomp ι F g, compDecomp ι F h) =
      galUnitsHom K.1 F.1 (compDecomp ι F g) (c (compDecomp ι F h, compDecomp ι F j)) *
        c (compDecomp ι F g, compDecomp ι F (h * j)) :=
    (congrArg (fun X => c (X, compDecomp ι F j) * c (compDecomp ι F g, compDecomp ι F h)) m1).trans
      (e.trans (congrArg (fun X => galUnitsHom K.1 F.1 (compDecomp ι F g)
        (c (compDecomp ι F h, compDecomp ι F j)) * c (compDecomp ι F g, X)) m2.symm))
  have key := congrArg (Units.map (embedComp ι F).toRingHom.toMonoidHom) key'
  have mm1 := map_mul (Units.map (embedComp ι F).toRingHom.toMonoidHom)
    (c (compDecomp ι F (g * h), compDecomp ι F j)) (c (compDecomp ι F g, compDecomp ι F h))
  have mm2 := map_mul (Units.map (embedComp ι F).toRingHom.toMonoidHom)
    (galUnitsHom K.1 F.1 (compDecomp ι F g) (c (compDecomp ι F h, compDecomp ι F j)))
    (c (compDecomp ι F g, compDecomp ι F (h * j)))
  exact congrArg Additive.ofMul (mm1.symm.trans (key.trans (mm2.trans (congrArg (· * _) s))))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem exists_compCocycle_coboundary
    (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) (hc : IsMulCocycle₂ c)
    (b : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →
      (AlgebraicClosure (v.adicCompletion K.1))ˣ) (hb : IsLocallyConstant b)
    (hbc : ∀ σ τ, σ • b τ / b (σ * τ) * b σ =
      Units.map (embedLevel ι F).toRingHom.toMonoidHom
        (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
          decompHom (v.adicCompletion K.1) (embedLevel ι F) τ))) :
    ∃ β' : Gal(compField ι F/v.adicCompletion K.1) → Additive (compField ι F)ˣ,
      (groupCohomology.d₁₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F))).hom β' =
        compCocycleFun ι F c := by
  have h := exists_cocycle_brauerInflation (F := v.adicCompletion K.1)
    (Ω := AlgebraicClosure (v.adicCompletion K.1)) (compField ι F)
    (⟨compCocycleFun ι F c, compCocycleFun_mem ι F c hc⟩ :
      groupCohomology.cocycles₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F)))
  obtain ⟨z, hz1, hz2⟩ := h
  have hz0 : cohomologyπ _ 2 z = 0 := by
    refine cohomologyπ_galUnits_eq_zero_of_coboundary z b hb fun u => ?_
    rw [hz2 u]
    apply Additive.toMul.injective
    apply Units.ext
    have q0 := compDecomp_restrictNormalHom ι F (u 0)
    have q1 := compDecomp_restrictNormalHom ι F (u 1)
    have e' := congrArg (fun x : (AlgebraicClosure (v.adicCompletion K.1))ˣ =>
      (x : AlgebraicClosure (v.adicCompletion K.1))) (hbc (u 0) (u 1))
    refine Eq.trans ?_ e'.symm
    have e3 : ι ((c (compDecomp ι F (AlgEquiv.restrictNormalHom (compField ι F) (u 0)),
        compDecomp ι F (AlgEquiv.restrictNormalHom (compField ι F) (u 1))) : F.1) : ℚ̄) =
        ι ((c (decompHom (v.adicCompletion K.1) (embedLevel ι F) (u 0),
          decompHom (v.adicCompletion K.1) (embedLevel ι F) (u 1)) : F.1) : ℚ̄) :=
      congrArg (fun p => ι ((c p : F.1) : ℚ̄)) (Prod.ext q0 q1)
    exact e3
  have hc'0 : (ConcreteCategory.hom (groupCohomology.H2π _))
      (⟨compCocycleFun ι F c, compCocycleFun_mem ι F c hc⟩ :
        groupCohomology.cocycles₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F))) = 0 := by
    apply brauerInflation_injective (compField ι F)
    rw [hz1, hz0, map_zero]
  rw [groupCohomology.H2π_eq_zero_iff] at hc'0
  exact hc'0

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem ordComp_coboundary_eq (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ)
    (β' : Gal(compField ι F/v.adicCompletion K.1) → Additive (compField ι F)ˣ)
    (hβ' : (groupCohomology.d₁₂ (galUnits.{0} (v.adicCompletion K.1) (compField ι F))).hom β' =
      compCocycleFun ι F c)
    (σ τ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)) -
        ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) (σ * τ))) +
        ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ)) =
      ordPlace ι F (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
        decompHom (v.adicCompletion K.1) (embedLevel ι F) τ)) := by
  have hmul : AlgEquiv.restrictNormalHom (compField ι F) (σ * τ) =
      AlgEquiv.restrictNormalHom (compField ι F) σ * AlgEquiv.restrictNormalHom (compField ι F) τ :=
    map_mul _ σ τ
  have key : (galUnits.{0} (v.adicCompletion K.1) (compField ι F)).ρ
      (AlgEquiv.restrictNormalHom (compField ι F) σ) (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)) -
      β' (AlgEquiv.restrictNormalHom (compField ι F) σ * AlgEquiv.restrictNormalHom (compField ι F) τ) +
      β' (AlgEquiv.restrictNormalHom (compField ι F) σ) =
      compCocycleFun ι F c (AlgEquiv.restrictNormalHom (compField ι F) σ,
        AlgEquiv.restrictNormalHom (compField ι F) τ) :=
    congrFun hβ' (AlgEquiv.restrictNormalHom (compField ι F) σ, AlgEquiv.restrictNormalHom (compField ι F) τ)
  have hs : ordComp ι F ((galUnits.{0} (v.adicCompletion K.1) (compField ι F)).ρ
      (AlgEquiv.restrictNormalHom (compField ι F) σ) (β' (AlgEquiv.restrictNormalHom (compField ι F) τ))) =
      ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)) :=
    ordComp_smul ι F (AlgEquiv.restrictNormalHom (compField ι F) σ)
      (Additive.toMul (β' (AlgEquiv.restrictNormalHom (compField ι F) τ)))
  have k1 := congrArg (ordComp ι F) key
  have k0 := (ordComp_add ι F _ _).trans (congrArg (· + ordComp ι F
    (β' (AlgEquiv.restrictNormalHom (compField ι F) σ))) ((ordComp_sub ι F _ _).trans
      (congrArg (· - ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ *
        AlgEquiv.restrictNormalHom (compField ι F) τ))) hs)))
  have k1 := k0.symm.trans k1
  have k2 : ordComp ι F (compCocycleFun ι F c (AlgEquiv.restrictNormalHom (compField ι F) σ,
      AlgEquiv.restrictNormalHom (compField ι F) τ)) = ordPlace ι F
      (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
        decompHom (v.adicCompletion K.1) (embedLevel ι F) τ)) :=
    (ordComp_embedComp ι F _).trans (congrArg (fun p => ordPlace ι F (c p))
      (Prod.ext (compDecomp_restrictNormalHom ι F σ) (compDecomp_restrictNormalHom ι F τ)))
  rw [hmul, k1, k2]

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_ord_coboundary_of_mulCoboundary
    (c : Gal(F.1/K.1) × Gal(F.1/K.1) → F.1ˣ) (hc : IsMulCocycle₂ c)
    (b : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →
      (AlgebraicClosure (v.adicCompletion K.1))ˣ) (hb : IsLocallyConstant b)
    (hbc : ∀ σ τ, σ • b τ / b (σ * τ) * b σ =
      Units.map (embedLevel ι F).toRingHom.toMonoidHom
        (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
          decompHom (v.adicCompletion K.1) (embedLevel ι F) τ))) :
    ∃ h : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) → ℤ,
      IsLocallyConstant h ∧ ∀ σ τ, h τ - h (σ * τ) + h σ = ordPlace ι F
        (c (decompHom (v.adicCompletion K.1) (embedLevel ι F) σ,
          decompHom (v.adicCompletion K.1) (embedLevel ι F) τ)) := by
  obtain ⟨β', hβ'⟩ := exists_compCocycle_coboundary ι F c hc b hb hbc
  exact ⟨fun σ => ordComp ι F (β' (AlgEquiv.restrictNormalHom (compField ι F) σ)),
    (IsLocallyConstant.of_discrete (fun γ => ordComp ι F (β' γ))).comp_continuous
      (InfiniteGalois.restrictNormalHom_continuous (compField ι F)),
    fun σ τ => ordComp_coboundary_eq ι F c β' hβ' σ τ⟩

end Main

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global groupCohomology

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (hv : v ∉ S)

def ordEmbMor :
    Rep.res (decompHomS (v.adicCompletion K.1) S ι) (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) ⟶
      trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ :=
  Rep.ofHom ⟨uliftIntLinearMap (ordEmb S ι hv), fun σ => by
    ext y
    exact ordEmb_decompHomS S ι hv σ (Additive.toMul y)⟩

theorem ordEmbMor_hom_apply (y : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    (ordEmbMor S ι hv).hom y = ordEmb S ι hv y := rfl

section Levels

theorem exists_galois_level_finset (T : Finset ℚ̄) (hT : ∀ y ∈ T, y ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    ∃ (N : FiniteSubfield) (_ : Fact (K ≤ N)), Normal K.1 N.1 ∧
      (∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) ∧ ∀ y ∈ T, y ∈ N.1 := by
  let A : IntermediateField K.1 ℚ̄ := IntermediateField.adjoin K.1 (T : Set ℚ̄)
  have : FiniteDimensional K.1 A :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let N' : IntermediateField K.1 ℚ̄ := IntermediateField.normalClosure K.1 A ℚ̄
  have hN'f : FiniteDimensional K.1 N' := inferInstance
  have hN'n : Normal K.1 N' := inferInstance
  have hN'le : N' ≤ maxUnramifiedOutside K.1 ℚ̄ S :=
    IntermediateField.normalClosure_le_iff_of_normal.2
      ((IntermediateField.adjoin_le_iff).2 fun y hy => hT y hy)
  have := K.2
  have hN'q : FiniteDimensional ℚ N' := Module.Finite.trans K.1 N'
  let N : FiniteSubfield := ⟨N'.restrictScalars ℚ, hN'q⟩
  have hKN : Fact (K ≤ N) := ⟨fun x hx => N'.algebraMap_mem ⟨x, hx⟩⟩
  refine ⟨N, hKN, ?_, fun x hx => hN'le hx, fun y hy => IntermediateField.le_normalClosure A
    (IntermediateField.subset_adjoin K.1 _ hy)⟩
  exact hN'n

variable (N : FiniteSubfield) [Fact (K ≤ N)] [Normal K.1 N.1]
  (hN : ∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

def levelIncl : N.1 →ₐ[K.1] maxUnramifiedOutside K.1 ℚ̄ S where
  toFun x := ⟨x, hN x x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def levelRes : galUnramifiedOutside K.1 ℚ̄ S →* Gal(N.1/K.1) :=
  decompHom K.1 (levelIncl S N hN)

theorem levelRes_apply (σ : galUnramifiedOutside K.1 ℚ̄ S) (x : N.1) :
    ((levelRes S N hN σ x : N.1) : ℚ̄) = ((σ ⟨x, hN x x.2⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
  congrArg Subtype.val (decompHom_apply (Kv := K.1) (levelIncl S N hN) σ x)


theorem levelRes_surjective : Function.Surjective (levelRes S N hN) := by
  intro γ
  refine ⟨(γ.liftNormal ℚ̄).restrictNormal (maxUnramifiedOutside K.1 ℚ̄ S), ?_⟩
  rw [levelRes, decompHom_eq_iff]
  intro x
  apply Subtype.val_injective
  change ((γ x : N.1) : ℚ̄) = (((γ.liftNormal ℚ̄).restrictNormal (maxUnramifiedOutside K.1 ℚ̄ S)
    ⟨x, hN x x.2⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
  rw [show (((γ.liftNormal ℚ̄).restrictNormal (maxUnramifiedOutside K.1 ℚ̄ S) ⟨x, hN x x.2⟩ :
      maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = γ.liftNormal ℚ̄ (algebraMap (maxUnramifiedOutside K.1 ℚ̄ S) ℚ̄
        ⟨x, hN x x.2⟩) from AlgEquiv.restrictNormal_commutes (γ.liftNormal ℚ̄)
          (maxUnramifiedOutside K.1 ℚ̄ S) ⟨x, hN x x.2⟩]
  exact (AlgEquiv.liftNormal_commutes γ ℚ̄ x).symm

theorem decompHom_embedLevel_eq (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) :
    decompHom (v.adicCompletion K.1) (embedLevel ι N) σ =
      levelRes S N hN (decompHomS (v.adicCompletion K.1) S ι σ) := by
  rw [decompHom_eq_iff]
  intro x
  rw [embedLevel_apply, embedLevel_apply, levelRes_apply]
  exact decompHom_apply (Kv := v.adicCompletion K.1) (ι.comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ
    ⟨x, hN x x.2⟩

end Levels

section LevelCocycle

def unitOfMem {N : FiniteSubfield} (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (hy : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1) : N.1ˣ :=
  Units.mk0 ⟨(y : maxUnramifiedOutside K.1 ℚ̄ S), hy⟩ fun h =>
    y.ne_zero (Subtype.ext (congrArg Subtype.val h : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
      ((0 : N.1) : ℚ̄)))


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem exists_level_cocycle (f : (Fin 2 → galUnramifiedOutside K.1 ℚ̄ S) →
      Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) (hf : IsLocallyConstant f)
    (hcoc : ∀ u : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S,
      (inhomogeneousCochains.d (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom f u = 0) :
    ∃ (N : FiniteSubfield) (_ : Fact (K ≤ N)) (_ : Normal K.1 N.1)
      (hN : ∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
      (c : Gal(N.1/K.1) × Gal(N.1/K.1) → N.1ˣ), IsMulCocycle₂ c ∧
      ∀ u : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S,
        (((f u).toMul : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
          ((c (levelRes S N hN (u 0), levelRes S N hN (u 1)) : N.1) : ℚ̄) := by
  classical
  obtain ⟨hc, -, ht⟩ := galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hf

  obtain ⟨E, hEf, hEU⟩ := (krullTopology_mem_nhds_one_iff K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
    (U : Set (galUnramifiedOutside K.1 ℚ̄ S))).1 (U.toOpenSubgroup.isOpen.mem_nhds U.one_mem')
  let bE := Module.finBasis K.1 E

  have hfin : (Set.range f).Finite := hf.range_finite
  let T : Finset ℚ̄ := (Finset.univ.image fun i => ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) ∪
    hfin.toFinset.image fun y => (((Additive.toMul y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)
  have hT : ∀ y ∈ T, y ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (bE i : maxUnramifiedOutside K.1 ℚ̄ S).2
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 h
      exact ((Additive.toMul z : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S).2
  obtain ⟨N, hKN, hNn, hN, hTN⟩ := exists_galois_level_finset S T hT

  have hres : ∀ σ σ' : galUnramifiedOutside K.1 ℚ̄ S, levelRes S N hN σ = levelRes S N hN σ' →
      σ⁻¹ * σ' ∈ U := by
    intro σ σ' h
    apply hEU
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hb : ∀ i, σ' (bE i : maxUnramifiedOutside K.1 ℚ̄ S) = σ (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
      intro i
      have hmem : ((bE i : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1 :=
        hTN _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
      have e := congrArg (fun τ : Gal(N.1/K.1) => ((τ ⟨_, hmem⟩ : N.1) : ℚ̄)) h
      simp only [levelRes_apply] at e
      exact Subtype.ext e.symm
    have hsum : x = ∑ i, (bE.repr ⟨x, hx⟩ i) • (bE i : maxUnramifiedOutside K.1 ℚ̄ S) := by
      have := congrArg (fun e : E => (e : maxUnramifiedOutside K.1 ℚ̄ S)) (bE.sum_repr ⟨x, hx⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
      exact this.symm
    have h1 : σ' x = σ x := by
      rw [hsum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : ∀ (τ : galUnramifiedOutside K.1 ℚ̄ S) (r : K.1) (y : maxUnramifiedOutside K.1 ℚ̄ S),
          τ (r • y) = r • τ y := fun τ r y => τ.toLinearEquiv.map_smul r y
      rw [hs, hs, hb i]
    rw [AlgEquiv.mul_apply, h1]
    exact σ.symm_apply_apply x
  have hfac : ∀ u u' : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S,
      (∀ i, levelRes S N hN (u i) = levelRes S N hN (u' i)) → f u = f u' :=
    fun u u' h => hU u u' fun i => hres _ _ (h i)
  have hval : ∀ u, (((f u).toMul : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S).1 ∈ N.1 :=
    fun u => hTN _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨f u, hfin.mem_toFinset.2 ⟨u, rfl⟩, rfl⟩))
  choose lift hlift using levelRes_surjective S N hN
  let c : Gal(N.1/K.1) × Gal(N.1/K.1) → N.1ˣ := fun p =>
    unitOfMem S (f ![lift p.1, lift p.2]).toMul (hval _)
  have hc_val : ∀ p, ((c p : N.1) : ℚ̄) =
      (((f ![lift p.1, lift p.2]).toMul : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S).1 :=
    fun p => rfl
  have hf2 : ∀ a b : galUnramifiedOutside K.1 ℚ̄ S,
      f ![a, b] = f ![lift (levelRes S N hN a), lift (levelRes S N hN b)] := by
    intro a b
    refine hfac _ _ fun i => ?_
    fin_cases i
    · exact (hlift _).symm
    · exact (hlift _).symm
  have hc_spec : ∀ u : Fin 2 → galUnramifiedOutside K.1 ℚ̄ S,
      (((f u).toMul : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S).1 =
        ((c (levelRes S N hN (u 0), levelRes S N hN (u 1)) : N.1) : ℚ̄) := by
    intro u
    have hu : u = ![u 0, u 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hc_val, hu, hf2]
    rfl
  refine ⟨N, hKN, hNn, hN, c, ?_, hc_spec⟩
  intro g h j
  have hd := hcoc ![lift g, lift h, lift j]
  rw [inhomogeneousCochains_d_two_apply'] at hd
  have e1 : f ![(![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 0 *
      (![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 1,
      (![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 2] =
      f ![lift (g * h), lift j] := by
    refine hfac _ _ fun i => ?_
    fin_cases i
    · change levelRes S N hN (lift g * lift h) = levelRes S N hN (lift (g * h))
      rw [map_mul, hlift, hlift, hlift]
    · rfl
  have e2 : f ![(![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 0,
      (![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 1 *
      (![lift g, lift h, lift j] : Fin 3 → galUnramifiedOutside K.1 ℚ̄ S) 2] =
      f ![lift g, lift (h * j)] := by
    refine hfac _ _ fun i => ?_
    fin_cases i
    · rfl
    · change levelRes S N hN (lift h * lift j) = levelRes S N hN (lift (h * j))
      rw [map_mul, hlift, hlift, hlift]
  rw [e1, e2] at hd
  have key : (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ (lift g) (f ![lift h, lift j]) +
      f ![lift g, lift (h * j)] = f ![lift (g * h), lift j] + f ![lift g, lift h] := by
    rw [← sub_eq_zero, ← hd]
    change _ = (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ (lift g) (f ![lift h, lift j]) -
      f ![lift (g * h), lift j] + f ![lift g, lift (h * j)] - f ![lift g, lift h]
    abel
  have key' := congrArg (fun y : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ =>
    (((Additive.toMul y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) key
  simp only [toMul_add, Units.val_mul, IntermediateField.coe_mul] at key'
  apply Units.ext
  apply Subtype.ext
  simp only [Units.val_mul, IntermediateField.coe_mul]
  rw [hc_val, hc_val, hc_val]
  have hg : (((g • c (h, j) : N.1ˣ) : N.1) : ℚ̄) = (((Additive.toMul
      ((galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ (lift g) (f ![lift h, lift j])) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) := by
    have e : (((g • c (h, j) : N.1ˣ) : N.1) : ℚ̄) =
        ((levelRes S N hN (lift g) (c (h, j) : N.1) : N.1) : ℚ̄) := by
      rw [hlift g]
      rfl
    rw [e, levelRes_apply]
    rfl
  rw [hg]
  exact key'.symm

end LevelCocycle

theorem ordEmb_eq_ordPlace (N : FiniteSubfield) [Fact (K ≤ N)]
    (hN : ∀ x ∈ N.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (u : N.1ˣ) (hyu : ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = ((u : N.1) : ℚ̄)) :
    ordEmb S ι hv (Additive.ofMul y) = ordPlace ι N u := by
  have hy : ((maxUnitsToUnits S y : ℚ̄ˣ) : ℚ̄) ∈ N.1 := by
    change ((y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) ∈ N.1
    rw [hyu]
    exact (u : N.1).2
  have hv' := valuation_placeOfEmbedding_eq S ι hv N hN (maxUnitsToUnits S y) hy
  have hu : (u : N.1) = ⟨(maxUnitsToUnits S y : ℚ̄), hy⟩ := Subtype.ext hyu.symm
  rw [ordEmb_apply, ordPlace, hu, hv', WithZero.log_exp, neg_neg]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem coboundary_iff_of_level (N : FiniteSubfield) [Fact (K ≤ N)] [Normal K.1 N.1]
    (he : (placeOfEmbedding ι N).1.asIdeal.ramificationIdx (𝓞 K.1) = 1)
    (c : Gal(N.1/K.1) × Gal(N.1/K.1) → N.1ˣ) (hc : IsMulCocycle₂ c)
    (a : (Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) →
      Additive (AlgebraicClosure (v.adicCompletion K.1))ˣ)
    (o : (Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) → ℤ)
    (ha : ∀ u, ((Additive.toMul (a u) : (AlgebraicClosure (v.adicCompletion K.1))ˣ) :
      AlgebraicClosure (v.adicCompletion K.1)) =
        ((Units.map (embedLevel ι N).toRingHom.toMonoidHom (c (decompHom (v.adicCompletion K.1)
          (embedLevel ι N) (u 0), decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1))) :
            (AlgebraicClosure (v.adicCompletion K.1))ˣ) : AlgebraicClosure (v.adicCompletion K.1)))
    (ho : ∀ u, o u = ordPlace ι N (c (decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 0),
      decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1)))) :
    (∃ w : (Fin 1 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) →
        Additive (AlgebraicClosure (v.adicCompletion K.1))ˣ, IsLocallyConstant w ∧
      ∀ u, a u = (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).ρ (u 0)
        (w fun _ => u 1) - w (fun _ => u 0 * u 1) + w (fun _ => u 0)) ↔
    (∃ w : (Fin 1 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)) → ℤ,
      IsLocallyConstant w ∧
      ∀ u, o u = (trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ).ρ (u 0)
        (w fun _ => u 1) - w (fun _ => u 0 * u 1) + w (fun _ => u 0)) := by
  have hconst : ∀ {X : Type} (w : (Fin 1 → Gal(AlgebraicClosure (v.adicCompletion K.1)/
      v.adicCompletion K.1)) → X), IsLocallyConstant w →
      IsLocallyConstant (fun σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) =>
        w fun _ => σ) :=
    fun w hw => hw.comp_continuous (continuous_pi fun _ => continuous_id)
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hbc : ∀ σ τ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
        σ • Additive.toMul (w fun _ => τ) / Additive.toMul (w fun _ => σ * τ) *
          Additive.toMul (w fun _ => σ) =
        Units.map (embedLevel ι N).toRingHom.toMonoidHom
          (c (decompHom (v.adicCompletion K.1) (embedLevel ι N) σ,
            decompHom (v.adicCompletion K.1) (embedLevel ι N) τ)) := by
      intro σ τ
      have h1 : a ![σ, τ] = (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).ρ σ
          (w fun _ => τ) - w (fun _ => σ * τ) + w (fun _ => σ) := hwz ![σ, τ]
      have h2 : Additive.toMul (a ![σ, τ]) = σ • Additive.toMul (w fun _ => τ) /
          Additive.toMul (w fun _ => σ * τ) * Additive.toMul (w fun _ => σ) :=
        (congrArg Additive.toMul h1).trans (toMul_galUnitsZ_coboundary σ _ _ _)
      apply Units.ext
      exact (congrArg Units.val h2.symm).trans (ha ![σ, τ])
    obtain ⟨h, hh, hhc⟩ := exists_ord_coboundary_of_mulCoboundary ι N c hc
      (fun σ => Additive.toMul (w fun _ => σ)) ((hconst w hw).comp Additive.toMul) hbc
    refine ⟨fun g => h (g 0), hh.comp_continuous (continuous_apply 0), fun u => ?_⟩
    rw [ho u, ← hhc (u 0) (u 1)]
    rfl
  · rintro ⟨w, hw, hwz⟩
    have hhc : ∀ σ τ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
        (w fun _ => τ) - (w fun _ => σ * τ) + (w fun _ => σ) =
        ordPlace ι N (c (decompHom (v.adicCompletion K.1) (embedLevel ι N) σ,
          decompHom (v.adicCompletion K.1) (embedLevel ι N) τ)) := by
      intro σ τ
      have h1 : o ![σ, τ] = (w fun _ => τ) - (w fun _ => σ * τ) + (w fun _ => σ) := hwz ![σ, τ]
      exact h1.symm.trans (ho ![σ, τ])
    obtain ⟨b, hb, hbc⟩ := exists_mulCoboundary_of_ord ι N he c hc (fun σ => w fun _ => σ)
      (hconst w hw) hhc
    refine ⟨fun g => Additive.ofMul (b (g 0)),
      (hb.comp_continuous (continuous_apply 0)).comp Additive.ofMul, fun u => ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    rw [ha u, ← hbc (u 0) (u 1)]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem gsLocalRes_eq_zero_iff (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    (gsLocalRes S ι 2).hom (cohomologyULiftIntAddEquiv _ 2 x) = 0 ↔
      (cohomologyMapAlong (decompHomS (v.adicCompletion K.1) S ι)
        (continuous_decompHomS (Kv := v.adicCompletion K.1) S ι) (ordEmbMor S ι hv) 2).hom x = 0 := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 2 x
  have hf : IsLocallyConstant (cochainOf _ (cocycleι _ 2 z)) := isLocallyConstant_cochainOf _
  have hcoc : ∀ u, (inhomogeneousCochains.d (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom
      (cochainOf _ (cocycleι _ 2 z)) u = 0 := fun u => congrFun (d_cocycleι z) u
  obtain ⟨N, hKN, hNn, hN, c, hc, hcf⟩ := exists_level_cocycle S _ hf hcoc
  have hU : Algebra.IsUnramifiedAt (𝓞 K.1) (placeOfEmbedding ι N).1.asIdeal :=
    isUnramifiedIn_of_subset_max S hv N hN _ inferInstance (placeOfEmbedding ι N).2
  have he : (placeOfEmbedding ι N).1.asIdeal.ramificationIdx (𝓞 K.1) = 1 :=
    Ideal.ramificationIdx_eq_one _ _

  have hA : (gsLocalRes S ι 2).hom (cohomologyULiftIntAddEquiv _ 2 (cohomologyπ _ 2 z)) =
      cohomologyπ _ 2 (cocyclesMapAlong (decompHomS (v.adicCompletion K.1) S ι)
        (continuous_decompHomS (Kv := v.adicCompletion K.1) S ι) (embUnitsMorZ S ι) 2
        (cocyclesULiftInt _ z)) := by
    rw [cohomologyULiftIntAddEquiv_cohomologyπ', gsLocalRes]
    exact cohomologyMapAlong_cohomologyπ _ _ _ _
  rw [hA, cohomologyMapAlong_cohomologyπ, cohomologyπ_two_eq_zero_iff_locallyConstant, cohomologyπ_two_eq_zero_iff_locallyConstant]
  simp only [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt]

  have hF : ∀ u : Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      (((Additive.toMul (cochainOf (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (cocycleι _ 2 z) (⇑(decompHomS (v.adicCompletion K.1) S ι) ∘ u)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
        ((c (decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 0),
          decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1)) : N.1) : ℚ̄) := by
    intro u
    rw [hcf, decompHom_embedLevel_eq S ι N hN, decompHom_embedLevel_eq S ι N hN]
    rfl
  have hord : ∀ u : Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      (ordEmbMor S ι hv).hom (cochainOf (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (cocycleι _ 2 z) (⇑(decompHomS (v.adicCompletion K.1) S ι) ∘ u)) =
        ordPlace ι N (c (decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 0),
          decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1))) :=
    fun u => (ordEmbMor_hom_apply S ι hv _).trans (ordEmb_eq_ordPlace S ι hv N hN _ _ (hF u))
  have hemb : ∀ u : Fin 2 → Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1),
      ((Additive.toMul ((embUnitsMorZ S ι).hom (cochainOf (galUnits.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (cocycleι _ 2 z)
        (⇑(decompHomS (v.adicCompletion K.1) S ι) ∘ u))) : (AlgebraicClosure (v.adicCompletion K.1))ˣ) :
          AlgebraicClosure (v.adicCompletion K.1)) =
        ((Units.map (embedLevel ι N).toRingHom.toMonoidHom (c (decompHom (v.adicCompletion K.1)
          (embedLevel ι N) (u 0), decompHom (v.adicCompletion K.1) (embedLevel ι N) (u 1))) :
            (AlgebraicClosure (v.adicCompletion K.1))ˣ) : AlgebraicClosure (v.adicCompletion K.1)) := by
    intro u
    rw [embUnitsMorZ_hom_apply]
    change ι _ = ι _
    exact congrArg ι (hF u)
  exact coboundary_iff_of_level ι N he c hc _ _ hemb hord

end

end GroundTheory.ProfCoh
end
