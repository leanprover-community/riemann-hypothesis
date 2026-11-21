import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt

section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH

open IsDedekindDomain

noncomputable abbrev Rv {R : Type*} [CommRing R] [IsDedekindDomain R] (F : Type*) [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) : Subring F :=
  (v.valuationSubringAtPrime F).toSubring

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] (v : HeightOneSpectrum R)

lemma val_eq_exp {x : F} (hx : x ≠ 0) : v.valuation F x = WithZero.exp (-(ordAt v x)) := by
  unfold ordAt
  rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)]

lemma mem_Rv_iff (x : F) : x ∈ Rv F v ↔ v.valuation F x ≤ 1 := by
  show x ∈ v.valuationSubringAtPrime F ↔ _
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v]
  exact Valuation.mem_valuationSubring_iff (v.valuation F) x

lemma mem_Rv_iff_ord {x : F} (hx : x ≠ 0) : x ∈ Rv F v ↔ 0 ≤ ordAt v x := by
  rw [mem_Rv_iff, val_eq_exp v hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  exact neg_nonpos

lemma ordAt_mul' {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy),
    neg_add]

lemma ordAt_zpow' {x : F} (k : ℤ) : ordAt v (x ^ k) = k * ordAt v x := by
  unfold ordAt
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul, mul_neg]

lemma ordAt_one' : ordAt v (1 : F) = 0 := by
  unfold ordAt
  rw [map_one, WithZero.log_one, neg_zero]

lemma ord_nonneg (a : Rv F v) (ha : (a : F) ≠ 0) : 0 ≤ ordAt v (a : F) := by
  exact (mem_Rv_iff_ord v ha).mp a.2

lemma isUnit_of_ord_zero (a : Rv F v) (ha : (a : F) ≠ 0) (h0 : ordAt v (a : F) = 0) : IsUnit a := by
  have hinv : ordAt v ((a : F)⁻¹) = 0 := by
    rw [← zpow_neg_one, ordAt_zpow', h0, mul_zero]
  have hmem : (a : F)⁻¹ ∈ Rv F v := (mem_Rv_iff_ord v (inv_ne_zero ha)).mpr hinv.ge
  have hab : a * ⟨_, hmem⟩ = 1 := Subtype.ext (mul_inv_cancel₀ ha)
  exact ⟨⟨a, ⟨_, hmem⟩, hab, by rw [mul_comm]; exact hab⟩, rfl⟩

lemma ord_zero_of_isUnit (a : Rv F v) (ha : IsUnit a) : ordAt v (a : F) = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have h1 : ((u : Rv F v) : F) * (((u⁻¹ : (Rv F v)ˣ) : Rv F v) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have hne1 : ((u : Rv F v) : F) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hne2 : (((u⁻¹ : (Rv F v)ˣ) : Rv F v) : F) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have hs := congrArg (ordAt v) h1
  rw [ordAt_mul' v hne1 hne2, ordAt_one'] at hs
  have ha1 := ord_nonneg v _ hne1
  have ha2 := ord_nonneg v _ hne2
  omega

lemma exists_ord_one : ∃ π : F, π ≠ 0 ∧ ordAt v π = 1 := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer F v
  have h0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨π, h0, ?_⟩
  unfold ordAt
  rw [hπ, WithZero.log_exp, neg_neg]

lemma irreducible_of_ord_one {π : F} (h0 : π ≠ 0) (h1 : ordAt v π = 1) :
    Irreducible (⟨π, (mem_Rv_iff_ord v h0).mpr (by omega)⟩ : Rv F v) := by
  rw [irreducible_iff]
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := ord_zero_of_isUnit v _ hu
    simp only at this
    omega
  · have hF : π = (a : F) * (b : F) := congrArg Subtype.val hab
    have ha0 : (a : F) ≠ 0 := fun h => h0 (by rw [hF, h, zero_mul])
    have hb0 : (b : F) ≠ 0 := fun h => h0 (by rw [hF, h, mul_zero])
    have hsum : ordAt v π = ordAt v (a : F) + ordAt v (b : F) := by rw [hF, ordAt_mul' v ha0 hb0]
    have hna := ord_nonneg v a ha0
    have hnb := ord_nonneg v b hb0
    by_cases hz : ordAt v (a : F) = 0
    · exact Or.inl (isUnit_of_ord_zero v a ha0 hz)
    · exact Or.inr (isUnit_of_ord_zero v b hb0 (by omega))

lemma eq_unit_mul_pow {π : F} (h0 : π ≠ 0) (h1 : ordAt v π = 1) (x : Rv F v) (hx : (x : F) ≠ 0) :
    ∃ u : (Rv F v)ˣ, x = (u : Rv F v) * (⟨π, (mem_Rv_iff_ord v h0).mpr (by omega)⟩ : Rv F v) ^
      (ordAt v (x : F)).toNat := by
  obtain ⟨n, hn⟩ : ∃ n, n = (ordAt v (x : F)).toNat := ⟨_, rfl⟩
  rw [← hn]
  have hnz : (n : ℤ) = ordAt v (x : F) := by rw [hn]; exact Int.toNat_of_nonneg (ord_nonneg v x hx)
  have hπn : π ^ n ≠ 0 := pow_ne_zero _ h0
  have hy0 : (x : F) / π ^ n ≠ 0 := div_ne_zero hx hπn
  have hyord : ordAt v ((x : F) / π ^ n) = 0 := by
    rw [div_eq_mul_inv, ordAt_mul' v hx (inv_ne_zero hπn), ← zpow_neg_one, ordAt_zpow',
      ← zpow_natCast, ordAt_zpow', h1]
    omega
  have hymem : (x : F) / π ^ n ∈ Rv F v := (mem_Rv_iff_ord v hy0).mpr hyord.ge
  have hu := isUnit_of_ord_zero v ⟨_, hymem⟩ hy0 hyord
  refine ⟨hu.unit, Subtype.ext ?_⟩
  rw [IsUnit.unit_spec]
  show (x : F) = (x : F) / π ^ n * π ^ n
  rw [div_mul_cancel₀ _ hπn]

lemma hasFactorization : IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization (Rv F v) := by
  obtain ⟨π, h0, h1⟩ := exists_ord_one (F := F) v
  refine ⟨_, irreducible_of_ord_one v h0 h1, ?_⟩
  intro x hx
  have hxF : (x : F) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨u, hu⟩ := eq_unit_mul_pow v h0 h1 x hxF
  exact ⟨_, u, by rw [hu, mul_comm]⟩

instance dvr_Rv : IsDiscreteValuationRing (Rv F v) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    (hasFactorization v)

lemma addVal_eq_ord (x : Rv F v) (hx : (x : F) ≠ 0) :
    IsDiscreteValuationRing.addVal (Rv F v) x = ((ordAt v (x : F)).toNat : ℕ∞) := by
  obtain ⟨π, h0, h1⟩ := exists_ord_one (F := F) v
  obtain ⟨u, hu⟩ := eq_unit_mul_pow v h0 h1 x hx
  conv_lhs => rw [hu]
  exact IsDiscreteValuationRing.addVal_def' u (irreducible_of_ord_one v h0 h1) _

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
end

section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open IsDedekindDomain QuotShiftPfH

private theorem ordAt_mul_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul ((v.valuation F).ne_zero_iff.mpr hx)
    ((v.valuation F).ne_zero_iff.mpr hy)]
  ring

private theorem ordAt_zpow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (x : F) (k : ℤ) :
    ordAt v (x ^ k) = k * ordAt v x := by
  unfold ordAt
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

private theorem ordAt_prod_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {ι : Type} (S : Finset ι)
    (f : ι → F) (hf : ∀ i, f i ≠ 0) : ordAt v (∏ i ∈ S, f i) = ∑ i ∈ S, ordAt v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    unfold ordAt
    rw [map_one]
    rfl
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordAt_mul_rationality v (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i), ih]

theorem exists_length_quotient_span_le (hL : QuotLocalStatement) {R F : Type} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (Q : Type)
    [AddCommGroup Q] [Module (Rv F v) Q] (ρ : ℕ) (hb : Nonempty (Module.Basis (Fin ρ) (Rv F v) Q))
    (c : Fin ρ → (Q →ₗ[Rv F v] F)) (s : Fin ρ → ℝ) (β : ℝ) (th : Fin ρ → Q)
    (hc : ∀ i q, c i q ≠ 0 → -β ≤ (ordAt v (c i q) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (th j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) = n ∧
      (n : ℝ) ≤ (ordAt v (Matrix.of fun i j => c i (th j)).det : ℝ) + ∑ i, s i + ρ * β := by
  classical

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rv F v)
  set π : F := (ϖ : F) with hπdef
  have hπ0 : π ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hπ1 : ordAt v π = 1 := by
    have h1 := (addVal_eq_ord v ϖ hπ0).symm.trans (IsDiscreteValuationRing.addVal_uniformizer hϖ)
    have h2 : (ordAt v π).toNat = 1 := by exact_mod_cast h1
    have h3 := ord_nonneg v ϖ hπ0
    omega

  have hne : ∀ i, ∃ q, c i q ≠ 0 := by
    intro i
    by_contra h
    push_neg at h
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [h])

  have hex : ∀ i, ∃ μ : ℤ, (∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = μ) ∧
      ∀ q, c i q ≠ 0 → μ ≤ ordAt v (c i q) := by
    intro i
    obtain ⟨lb, ⟨q, hq, rfl⟩, hlb⟩ := Int.exists_least_of_bdd
      (P := fun z => ∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = z)
      ⟨⌈-β - s i⌉, by
        rintro z ⟨q, hq, rfl⟩
        refine Int.ceil_le.mpr ?_
        have := hc i q hq
        linarith⟩
      (by obtain ⟨q, hq⟩ := hne i; exact ⟨_, q, hq, rfl⟩)
    exact ⟨_, ⟨q, hq, rfl⟩, fun q' hq' => hlb _ ⟨q', hq', rfl⟩⟩
  choose μ hμ1 hμ2 using hex
  have hμβ : ∀ i, -(μ i : ℝ) ≤ β + s i := by
    intro i
    obtain ⟨q, hq, hqμ⟩ := hμ1 i
    have := hc i q hq
    rw [hqμ] at this
    linarith

  have hmem : ∀ i q, π ^ (-μ i) * c i q ∈ Rv F v := by
    intro i q
    by_cases hq : c i q = 0
    · rw [hq, mul_zero]; exact (Rv F v).zero_mem
    · refine (mem_Rv_iff_ord v (mul_ne_zero (zpow_ne_zero _ hπ0) hq)).mpr ?_
      rw [ordAt_mul_rationality v (zpow_ne_zero _ hπ0) hq, ordAt_zpow, hπ1]
      have := hμ2 i q hq
      linarith
  let c' : Fin ρ → (Q →ₗ[Rv F v] Rv F v) := fun i =>
    { toFun := fun q => ⟨π ^ (-μ i) * c i q, hmem i q⟩
      map_add' := fun a b => by ext; simp [mul_add]
      map_smul' := fun r q => by
        ext
        simp only [LinearMap.map_smul, RingHom.id_apply, Subring.coe_mul, Subring.smul_def,
          smul_eq_mul]
        ring }
  have hmap : ((Matrix.of fun i j => c' i (th j)).map (Rv F v).subtype) =
      Matrix.diagonal (fun i => π ^ (-μ i)) * Matrix.of fun i j => c i (th j) := by
    ext i j
    simp [Matrix.diagonal_mul, c']
  have hdetF : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (∏ i, π ^ (-μ i)) * (Matrix.of fun i j => c i (th j)).det := by
    have := RingHom.map_det (Rv F v).subtype (Matrix.of fun i j => c' i (th j))
    simp only [RingHom.mapMatrix_apply] at this
    rw [show (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (Rv F v).subtype (Matrix.of fun i j => c' i (th j)).det from rfl, this, hmap,
      Matrix.det_mul, Matrix.det_diagonal]
  have hP0 : (∏ i, π ^ (-μ i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ hπ0
  have hdF0 : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) ≠ 0 := by
    rw [hdetF]; exact mul_ne_zero hP0 hdet
  have hdet' : (Matrix.of fun i j => c' i (th j)).det ≠ 0 := fun h => hdF0 (by rw [h]; rfl)
  have hlen := hL (Rv F v) Q ρ hb c' th hdet'
  rw [addVal_eq_ord v _ hdF0] at hlen
  have hord : ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      ∑ i, -μ i + ordAt v (Matrix.of fun i j => c i (th j)).det := by
    rw [hdetF, ordAt_mul_rationality v hP0 hdet, ordAt_prod_rationality v _ _ fun i => zpow_ne_zero _ hπ0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ordAt_zpow, hπ1, mul_one]
  have hnn := ord_nonneg v _ hdF0
  have htop : Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen
  refine ⟨(Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat,
    (ENat.coe_toNat htop).symm, ?_⟩
  have hle : (Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F)).toNat := by
    rw [← ENat.coe_toNat htop] at hlen
    exact_mod_cast hlen
  have hle' : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℝ) ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) : ℝ) := by
    have : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℤ) ≤
        ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) := by omega
    exact_mod_cast this
  rw [hord] at hle'
  push_cast at hle'
  have hsum : ∑ i, (-(μ i : ℝ)) ≤ ∑ i, (β + s i) := Finset.sum_le_sum fun i _ => hμβ i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
