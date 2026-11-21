import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecActRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Ufacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OkBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Strict
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.RankLeOfCardLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ToZModEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.EqOneOfPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ResH1SurjectiveOfIsomorphism
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.B1p
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.PsiLocalPairEqLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.CastToZModPowOne

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem galois_sqrt_sign {Ω : Type} [Field Ω] [CharZero Ω] (s : G ℚ Ω) {x : Ω} {n : ℤ} (hx : x ^ 2 = n) :
    s x = x ∨ s x = -x := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [← map_pow, hx, map_intCast]

private theorem decomposition_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {x : Ω} {k : ℤ}
    (hx : x ^ 2 = ((1 + 4 * k : ℤ) : Ω)) (hk : B.valuation (k : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) B) : s x = x := by
  refine (galois_sqrt_sign s hx).resolve_right fun h => ?_
  set y : Ω := (1 + x) / 2 with hy
  have h1 : s y = 1 - y := by rw [hy, map_div₀, map_add, map_one, h, map_ofNat]; ring
  have h2 : y * (1 - y) = -k := by
    push_cast at hx
    rw [hy]; linear_combination (-1 / 4 : Ω) * hx
  have h3 : B.valuation (1 - y) < 1 ↔ B.valuation y < 1 := by rw [← h1]; exact valuation_apply_lt_one_iff hs y
  have h4 : B.valuation y < 1 := by
    by_contra h5
    have h6 : 1 ≤ B.valuation (y * (1 - y)) := by
      rw [map_mul]; exact one_le_mul (not_lt.1 h5) (not_lt.1 (h3.not.2 h5))
    rw [h2, Valuation.map_neg] at h6
    exact absurd hk (not_lt.2 h6)
  have h7 := B.valuation.map_add_lt h4 (h3.2 h4)
  simp at h7

private theorem etaleSimplicialCochain_scheme_section_extension_naturality {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {p n : ℕ} (hp : B.valuation (p : Ω) < 1)
    (h : p.Coprime n) : ¬ B.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hm : ∀ (c : ℤ) (z : Ω), B.valuation z < 1 → B.valuation (c * z) < 1 := fun c z hz => by
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))).trans_lt hz
  have := B.valuation.map_add_lt (hm a _ hp) (hm b _ hn)
  rw [e, map_one] at this
  exact lt_irrefl _ this

private theorem inertia_fixes_sqrt_discriminant {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) {δ : Ω} {D : ℕ}
    (hδ : δ ^ 2 = -(D : Ω)) (hD : ¬ B.valuation ((4 * D : ℕ) : Ω) < 1) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) : s δ = δ := by
  refine (galois_sqrt_sign s (n := -D) (by rw [hδ]; simp)).resolve_right fun h => hD ?_
  have h1 : B.valuation δ ≤ 1 := by
    have : B.valuation δ ^ 2 ≤ 1 := by
      rw [← map_pow, hδ, Valuation.map_neg]; exact (B.valuation_le_one_iff _).2 (natCast_mem B D)
    exact (pow_le_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h2 := hs.2 δ h1
  have e : ((4 * D : ℕ) : Ω) = -((s δ - δ) ^ 2) := by rw [h]; push_cast; linear_combination (4 : Ω) * hδ
  rw [e, Valuation.map_neg, map_pow]
  exact pow_lt_one₀ zero_le' h2 two_ne_zero

private theorem gauss_sqrt_inertia_negates {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 3)
    (B : ValuationSubring Ω) (hB : B.valuation (p : Ω) < 1) :
    ∃ x : Ω, x ^ 2 = -(p : Ω) ∧ ∃ s ∈ Ine (F := ℚ) B, s x = -x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  have h2 : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  let ψ := AddChar.zmodChar p hζ.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Ω)
  have hχ : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)).2 (quadraticChar_ne_one h2)
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hm : χ (-1) = -1 := by
    show ((quadraticChar (ZMod p) (-1) : ℤ) : Ω) = -1
    rw [quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]; simp
  have hmem : (-1 : (ZMod p)ˣ) ∈ (Ine (F := ℚ) B).map (B1.cycN ℚ Ω p) := by
    rw [B1.cycIne Ω p p B hB, B3.pPart, MonoidHom.mem_ker]
    have : ordCompl[p] p = 1 := by rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
    have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨s, hs, hs'⟩ := hmem
  refine ⟨gaussSum χ ψ, by rw [gaussSum_sq hχ hq hψ, hm, ZMod.card]; simp, s, hs, ?_⟩
  have h3 := gaussSum_mulShift χ ψ (-1)
  rw [Units.val_neg, Units.val_one, hm, neg_one_mul, neg_eq_iff_eq_neg] at h3
  rw [← h3, gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul]
  congr 1
  · exact map_intCast s _
  · have h5 : ψ a ^ p = 1 := by rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    rw [B1.cycN_spec ℚ Ω p s h5, hs', ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, AddChar.mulShift_apply]
    simp

private theorem complex_conjugation_fixes_sqrt {Ω : Type} [Field Ω] [CharZero Ω] {τ : G ℚ Ω} (h : IsCC τ) {z : Ω} {n : ℕ} (hn : 0 < n)
    (hz : z ^ 2 = n) : τ z = z := by
  refine (galois_sqrt_sign τ (n := n) (by rw [hz]; simp)).resolve_right fun h1 => ?_
  obtain ⟨j, hj⟩ := h
  have h2 : starRingEnd ℂ (j z) = -j z := by rw [← map_neg, ← h1]; exact (hj z).symm
  have h3 := Complex.mul_conj (j z)
  rw [h2, mul_neg, ← sq, ← map_pow, hz, map_natCast] at h3
  have h4 : -(n : ℝ) = Complex.normSq (j z) := by exact_mod_cast h3
  have h5 := Complex.normSq_nonneg (j z)
  have h6 : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

theorem UpperTheory.V.Fr.exists_twistCharacter_continuousCohomology :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∃ H₀, FrobeniusSplitPrimeDatum η M H₀ := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  have hM := hG.M_ne
  obtain ⟨p, hlt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (4 * D + M) (q := 4 * M) (a := -1) (by omega)
    isCoprime_one_left.neg_left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hmod.dvd
  have ht' : -(p : ℤ) = 1 + 4 * (M * t) := by push_cast at ht; linear_combination ht
  obtain ⟨A, hA⟩ := (B3.placesQ Ω).1 p hp
  obtain ⟨x, hx, s, hs, hsx⟩ := gauss_sqrt_inertia_negates p (by omega) A hA
  have hsδ : s δ = δ := inertia_fixes_sqrt_discriminant A hδ (etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime (by omega) (by omega) hp)) hs
  have hz : (δ * x) ^ 2 = ((D * p : ℕ) : Ω) := by rw [mul_pow, hδ, hx]; push_cast; ring
  have hpos : 0 < D * p := Nat.mul_pos hD hp.pos
  have hz0 : δ * x ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero] at hz
    exact hpos.ne (by exact_mod_cast hz)
  have hne : -(δ * x) ≠ δ * x := fun h => hz0 (by linear_combination (-1 / 2 : Ω) * h)
  have hsz : s (δ * x) = -(δ * x) := by rw [map_mul, hsδ, hsx, mul_neg]
  have hmem : ∀ g : G ℚ Ω, g ∈ MulAction.stabilizer (G ℚ Ω) (δ * x) ↔ g (δ * x) = δ * x := fun g => Iff.rfl
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  refine ⟨MulAction.stabilizer (G ℚ Ω) (δ * x), stabilizer_isOpen_of_isIntegral _, ?_, fun τ hτ => complex_conjugation_fixes_sqrt hτ hpos hz,
    fun B' hB' => ?_, A, etaleSimplicialCochain_scheme_section_extension_naturality A hA (Nat.coprime_of_lt_prime hM (by omega) hp), fun h => hne (hsz.symm.trans (h hs))⟩
  · refine Subgroup.index_eq_two_iff.2 ⟨s, fun b => ?_⟩
    rw [hmem, hmem, AlgEquiv.mul_apply, hsz, map_neg]
    rcases galois_sqrt_sign b (n := (D * p : ℕ)) (hz.trans (Int.cast_natCast _).symm) with h | h
    · rw [h]; exact Or.inr ⟨rfl, hne⟩
    · rw [h, neg_neg]; exact Or.inl ⟨rfl, hne⟩
  · have hk : B'.valuation ((M * t : ℤ) : Ω) < 1 := by
      rw [Int.cast_mul, Int.cast_natCast, map_mul]
      exact mul_lt_one_of_lt_of_le hB' ((B'.valuation_le_one_iff _).2 (intCast_mem B' t))
    ext g
    refine and_congr_right fun hg => ?_
    have hgx : g x = x := decomposition_fixes_sqrt B' (by rw [← ht', hx]; simp) hk hg
    show g (δ * x) = δ * x ↔ η g = 1
    rw [map_mul, hgx, hη]
    rcases Int.units_eq_one_or (η g) with h | h
    · simp [h]
    · rw [h]
      refine iff_of_false (fun h' => hne ?_) (by decide)
      simpa using h'
end

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem ax_cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    {s : G ℚ Ω} (hs : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  apply Units.ext
  show PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val) = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ l = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).1 ht)
    simpa using this
  have hl1 : l ^ 1 ≠ 1 := by
    have := hl.out.one_lt
    rw [pow_one]
    omega
  rw [ZMod.val_one'' hl1, pow_one]
  exact hs _ ht'

theorem UpperTheory.V.Fr.auxw_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ Q : ℕ, Q ≠ 0 → ∃ w, FrobeniusWitnessPrime l η Ψ M w ∧ w ≡ 1 [MOD Q] := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ
  obtain ⟨a, hη, hbar⟩ := hG.cyc
  have hM := hG.M_ne
  have hlM := hG.l_dvd
  have hL : M ^ (a + 1) * Q ≠ 0 := mul_ne_zero (pow_ne_zero _ hM) hQ
  obtain ⟨w, hw, hwgt, hw1⟩ := Nat.exists_prime_gt_modEq_one (M ^ (a + 1) * Q) hL
  have hMaL : M ^ a ∣ M ^ (a + 1) * Q := Dvd.dvd.mul_right (pow_dvd_pow M (Nat.le_succ a)) Q
  have hlL : l ∣ M ^ (a + 1) * Q :=
    dvd_trans hlM (dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _))
  have hML : M ∣ M ^ (a + 1) * Q := dvd_trans (dvd_pow_self M (Nat.succ_ne_zero a)) (dvd_mul_right _ _)
  have hndvd : ∀ m, m ∣ M ^ (a + 1) * Q → ¬ w ∣ m := by
    intro m hm hwm
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hm
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL hm)) hwm
    omega
  refine ⟨w, ⟨hw, hndvd M hML, Nat.ModEq.of_dvd hlL hw1, ?_⟩, Nat.ModEq.of_dvd (dvd_mul_left Q _) hw1⟩
  intro B' hB' s hs
  haveI := Fact.mk hw
  have fix : ∀ m, m ∣ M ^ (a + 1) * Q → ∀ ζ : Ω, ζ ^ m = 1 → s ζ = ζ := by
    intro m hm
    have hcop : m.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).2 (hndvd m hm)).symm
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w B' hB' m hcop s hs
    intro ζ hζ
    rw [hk ζ hζ]
    have hwk : w ^ k ≡ 1 [MOD m] := by
      have := (Nat.ModEq.of_dvd hm hw1).pow k
      rwa [one_pow] at this
    rw [pow_eq_pow_mod _ hζ, show w ^ k % m = 1 % m from hwk, ← pow_eq_pow_mod 1 hζ, pow_one]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact hη s (fix _ hMaL)
  · exact hbar s (fix _ hMaL)
  · rw [MonoidHom.mem_ker]
    change (Units.map _) ((cycMod ℚ Ω l 1) s) = 1
    rw [ax_cycMod_one l (fix l hlL), map_one]
end

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem fix_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (Ω ≃ₐ[ℚ] Ω))
    (h : IsOpen (H : Set (Ω ≃ₐ[ℚ] Ω))) : (IntermediateField.fixedField H).fixingSubgroup = H :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen h⟩

private theorem commutator_le_ker_of_hom_int_units {Γ : Type*} [Group Γ] (η : Γ →* ℤˣ) : commutator Γ ≤ η.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

private theorem conj_ne_self_of_sq_eq_neg_natCast (z : ℂ) (D : ℕ) (hD : 0 < D) (h : z ^ 2 = -(D : ℂ)) :
    starRingEnd ℂ z ≠ z := by
  intro hc
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hc
  have h1 := congrArg Complex.re h
  simp [pow_two, him] at h1
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [mul_self_nonneg z.re]

theorem UpperTheory.V.Fr.field_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (U : Subgroup (G ℚ Ω)), UFacts l η Ψ M m U → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω), IsAbelianGalois ℚ L ∧ upl Ω L = U ∧ galOf ℚ L Ω = U ⊓ η.ker := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m U hU
  obtain ⟨D, δ, hD, -, hδ2, hδ⟩ := hG.quad
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ2
    omega
  have hker : ∀ s : G ℚ Ω, η s = 1 ↔ s δ = δ := by
    intro s
    constructor
    · intro h
      rw [hδ s, h]
      simp
    · intro h
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact h1
      · exfalso
        rw [hδ s, h1] at h
        simp at h
        have h2 : (2 : Ω) * δ = 0 := by linear_combination -h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
  have hint : IsIntegral ℚ δ := Algebra.IsIntegral.isIntegral δ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {δ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hkerO : IsOpen (η.ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {δ}))
    intro s hs
    rw [MonoidHom.mem_ker, hker]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs δ
      (IntermediateField.mem_adjoin_simple_self ℚ δ)
  have hHo : IsOpen ((U ⊓ η.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_inf]
    exact hU.isOpen.inter hkerO
  have hcomm : commutator (G ℚ Ω) ≤ U ⊓ η.ker := le_inf hU.ab (commutator_le_ker_of_hom_int_units η)
  set L := IntermediateField.fixedField (U ⊓ η.ker) with hLdef
  have hfix : L.fixingSubgroup = U ⊓ η.ker := fix_fix _ hHo
  haveI : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hHo)
  haveI : NumberField L := ⟨⟩
  have hN : (L.fixingSubgroup).Normal := by
    rw [hfix]
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n * g⁻¹ * n⁻¹ ∈ U ⊓ η.ker :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have he : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by
      group
    rw [he]
    exact Subgroup.mul_mem _ hc hn
  have hAb : @IsAbelianGalois ℚ L _ _ (IntermediateField.algebra' L) := by
    letI : Algebra ℚ L := IntermediateField.algebra' L
    haveI hg : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp hN
    haveI : IsMulCommutative Gal(L/ℚ) := ⟨⟨fun a b => by
      obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω a
      obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω b
      have hc : a' * b' * a'⁻¹ * b'⁻¹ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker := by
        rw [IntermediateField.restrictNormalHom_ker, hfix]
        exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b'))
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hc
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)⟩⟩
    exact ⟨⟩
  haveI : IsAbelianGalois ℚ L := by
    convert hAb <;> exact Subsingleton.elim _ _
  have hδL : δ ∈ L := by
    rw [IntermediateField.mem_fixedField_iff]
    intro s hs
    exact (hker s).mp (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hs).2)
  have hδL2 : (⟨δ, hδL⟩ : L) ^ 2 = -(D : L) := by
    apply Subtype.ext
    simpa using hδ2
  haveI : NumberField.IsTotallyComplex L := ⟨fun v => by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_iff]
    intro hv
    apply conj_ne_self_of_sq_eq_neg_natCast (v.embedding ⟨δ, hδL⟩) D hD
    · rw [← map_pow, hδL2]
      simp
    · have := RingHom.congr_fun hv ⟨δ, hδL⟩
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at this⟩
  obtain ⟨j, hj⟩ := hG.cc
  have hσU : σ ∈ U := hU.real σ hG.cc
  have hησ : η σ = -1 := by
    rcases Int.units_eq_one_or (η σ) with h | h
    · exfalso
      have hσδ : σ δ = δ := (hker σ).mp h
      apply conj_ne_self_of_sq_eq_neg_natCast (j δ) D hD
      · rw [← map_pow, hδ2]
        simp
      · rw [← hj, hσδ]
    · exact h
  have hcc : ∀ z : L, σ (z : Ω) = ((NumberField.IsCMField.complexConj L z : L) : Ω) := by
    intro z
    apply j.injective
    rw [hj]
    exact (NumberField.IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) z).symm
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · ext s
    change (∀ x ∈ NumberField.maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U
    constructor
    · intro h
      rw [← fix_fix U hU.isOpen, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hyL : y ∈ L := (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf =>
        (IntermediateField.mem_fixedField_iff _ _).mp hy f (Subgroup.mem_inf.mp hf).1
      have hre : (⟨y, hyL⟩ : L) ∈ NumberField.maximalRealSubfield L := by
        rw [← NumberField.IsCMField.complexConj_eq_self_iff]
        apply Subtype.ext
        rw [← hcc]
        exact (IntermediateField.mem_fixedField_iff _ _).mp hy σ hσU
      exact h _ hre
    · intro hs x hx
      have hσx : σ (x : Ω) = x := by
        rw [hcc, (NumberField.IsCMField.complexConj_eq_self_iff L x).mpr hx]
      show s (x : Ω) = x
      rcases Int.units_eq_one_or (η s) with h1 | h1
      · exact (IntermediateField.mem_fixedField_iff _ _).mp x.2 s (Subgroup.mem_inf.mpr ⟨hs, h1⟩)
      · have hm : σ * s ∈ U ⊓ η.ker := by
          refine Subgroup.mem_inf.mpr ⟨U.mul_mem hσU hs, ?_⟩
          rw [MonoidHom.mem_ker, map_mul, hησ, h1]
          rfl
        have := (IntermediateField.mem_fixedField_iff _ _).mp x.2 (σ * s) hm
        rw [AlgEquiv.mul_apply] at this
        apply σ.injective
        rw [this, hσx]
  · ext s
    change (∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x) ↔ s ∈ U ⊓ η.ker
    rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

private theorem tf (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] : Module.IsTorsionFree F Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

section SlopeTestRemainingChoices

attribute [local instance high] tf

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem deg_eq (l : ℕ) [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : locDeg w = (galOf ℚ F Ω).relIndex (Dec (F := ℚ) A) := by
  obtain ⟨h1, h2⟩ := @Loc.decEmb F Ω _ _ _ _ _ _ l _
  obtain ⟨j, rfl⟩ := h1 A w hA hw
  obtain ⟨-, φ, -, -, hr, -, -, hd⟩ := h2 j
  obtain ⟨-, φ₀, -, h0, hr0, -⟩ := (@Loc.decEmb ℚ Ω _ _ _ _ _ _ l _).2 j
  have hs : Function.Surjective φ₀ := fun s => (hr0 s).2 fun x => by simp
  rw [← hd w hA, ← Subgroup.index_comap_of_surjective _ hs, Subgroup.relIndex]
  congr 1
  ext g
  rw [Subgroup.mem_comap, hr, Subgroup.mem_subgroupOf, mem_galOf]
  exact forall_congr' fun x => by rw [h0]; exact j.injective.eq_iff

omit [CharZero Ω] [IsAlgClosure ℚ Ω] in
private theorem cc_ex [IsTotallyReal F] (w : InfinitePlace F) : ∃ c : G F Ω, IsCCAt w c := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois F Ω := {}
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let j : Ω →ₐ[F] ℂ := IsAlgClosed.lift
  have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
  let cj : ℂ →ₐ[F] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  refine ⟨(cj.comp j).restrictNormal' Ω, j.toRingHom, fun x => ?_, ?_⟩
  · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
  · rw [show j.toRingHom.comp (algebraMap F Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
    exact w.mk_embedding

private theorem kills_open {N : ℕ} (hN : N ≠ 0) {C : Type} [Group C] {χ : G ℚ Ω →* C} (h : Af.KillsMu N χ) :
    IsOpen (χ.ker : Set (G ℚ Ω)) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hf : {ζ : Ω | ζ ^ N = 1}.Finite :=
    (Polynomial.nthRootsFinset N (1 : Ω)).finite_toSet.subset fun ζ hζ =>
      (Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hN) _).2 hζ
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ N = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ N = 1}).fixingSubgroup) (fun s hs => h s fun ζ hζ => ?_)
    (IntermediateField.fixingSubgroup_isOpen _)
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ (IntermediateField.subset_adjoin _ _ hζ)

omit [IsAlgClosure ℚ Ω] in
private theorem eta_cc {η : G ℚ Ω →* ℤˣ} {σ : G ℚ Ω} (hσ : IsCC σ) {D : ℕ} {δ : Ω} (hD : 0 < D) (h2 : δ ^ 2 = -(D : Ω))
    (h : ∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) : η σ = -1 := by
  refine (Int.units_eq_one_or (η σ)).resolve_left fun h1 => ?_
  obtain ⟨j, hj⟩ := hσ
  have h3 : σ δ = δ := by rw [h, h1]; simp
  have h4 := hj δ
  rw [h3] at h4
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h4.symm
  have h5 := congrArg j h2
  rw [map_pow, hr, map_neg, map_natCast] at h5
  have h6 : r ^ 2 = -(D : ℝ) := by exact_mod_cast h5
  have h7 : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [sq_nonneg r]

omit [CharZero Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure F Ω] in
private theorem over_smul {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) (g : G F Ω) :
    IsPlaceOver (g • A) w := fun x => by
  have e : ∀ y : F, algebraMap F Ω y ∈ g • A ↔ algebraMap F Ω y ∈ A := fun y => by
    conv_lhs => rw [← g.commutes y]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  rw [← hA x, valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, e, e]

omit [IsAlgClosure F Ω] in
private theorem emb_smul (g : G F Ω) (A : ValuationSubring Ω) : galEmb ℚ F Ω g • A = g • A := rfl

private theorem conj_l (l : ℕ) [Fact l.Prime] {A B : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1)
    (hB : B.valuation (l : Ω) < 1) : ∃ g : G ℚ Ω, g • A = B := by
  obtain ⟨a1, a2, a3, -⟩ := places ℚ Ω l A
  obtain ⟨b1, b2, b3, -⟩ := places ℚ Ω l B
  obtain ⟨v, hv⟩ := a1 fun h => (a2 h).2 hA
  obtain ⟨u, hu⟩ := b1 fun h => (b2 h).2 hB
  have key : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := fun v h => by
    have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
      rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
      exact Nat.prime_iff_prime_int.1 Fact.out
    exact (((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal (mt Ideal.span_singleton_eq_bot.1 hp.ne_zero)).eq_of_le v.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).2 h) |>.symm
  have e : v = u := HeightOneSpectrum.ext ((key v ((a3 v hv).1 hA)).trans (key u ((b3 u hu).1 hB)).symm)
  exact exists_smul_eq_of_isPlaceOver hv (e ▸ hu)

private theorem place_ex (l : ℕ) [Fact l.Prime] {η : G ℚ Ω →* ℤˣ} {c : G F Ω} (hc : η (galEmb ℚ F Ω c) = -1)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (v : HeightOneSpectrum (𝓞 F)) (hv : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ ∃ γ : G ℚ Ω, η γ = 1 ∧ A = γ • B := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨γ, rfl⟩ := conj_l l hB (((places F Ω l A).2.2.1 v hA).2 hv)
  rcases Int.units_eq_one_or (η γ) with h | h
  · exact ⟨_, hA, γ, h, rfl⟩
  · exact ⟨_, over_smul hA c, galEmb ℚ F Ω c * γ, by rw [map_mul, hc, h]; simp, by rw [mul_smul, emb_smul]⟩

omit [CharZero Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure F Ω] in
private theorem tame_le (S : Set (HeightOneSpectrum (𝓞 F))) (K H : Subgroup (G F Ω)) [H.Normal] (hH : IsClosed (H : Set (G F Ω)))
    (h : ∀ v ∉ S, ∀ A, IsPlaceOver A v → Ine (F := F) A ⊓ K ≤ H) : GC.tameN S K ≤ H := by
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun s hs => ?_) hH
  simp only [Set.mem_iUnion] at hs
  obtain ⟨v, hv, A, hA, hs⟩ := hs
  exact h v hv A hA hs

private theorem clos_comap {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X]
    [IsTopologicalGroup Y] (e : X ≃ₜ* Y) (s : Set X) (t : Set Y) (h1 : ∀ x ∈ s, x = 1 ∨ e x ∈ t) (h2 : ∀ x, e x ∈ t → x ∈ s) :
    (Subgroup.normalClosure t).topologicalClosure.comap (e : X →* Y) = (Subgroup.normalClosure s).topologicalClosure := by
  have h : (Subgroup.normalClosure t).comap (e : X →* Y) = Subgroup.normalClosure s := by
    refine le_antisymm ?_ (Subgroup.normalClosure_le_normal fun x hx => ?_)
    · rw [show (e : X →* Y) = (e.toMulEquiv : X →* Y) from rfl, ← Subgroup.comap_normalClosure]
      exact Subgroup.normalClosure_mono h2
    · rcases h1 x hx with rfl | h
      · exact one_mem _
      · exact Subgroup.subset_normalClosure h
  ext x
  rw [← h]
  exact Set.ext_iff.1 (e.toHomeomorph.preimage_closure (Subgroup.normalClosure t : Set Y)) x

private theorem upl_eq (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] :
    upl Ω L = galOf ℚ (W.Lp L) Ω := by
  ext s
  exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

private theorem equiv_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure (W.Lp L) Ω] : ∃ e : G (W.Lp L) Ω ≃ₜ* upl Ω L, ∀ g, (e g).1 = galEmb ℚ (W.Lp L) Ω g := by
  have hE := (galEmbTop ℚ (W.Lp L) Ω).1
  have hr : (galEmb ℚ (W.Lp L) Ω).range = upl Ω L := (range_galEmb ℚ (W.Lp L) Ω).trans (upl_eq Ω L).symm
  let e : G (W.Lp L) Ω ≃* upl Ω L := (MonoidHom.ofInjective hE.injective).trans (MulEquiv.subgroupCongr hr)
  refine ⟨{ e with continuous_toFun := hE.continuous.subtype_mk _, continuous_invFun := hE.continuous_iff.2 ?_ }, fun _ => rfl⟩
  convert continuous_subtype_val using 1
  funext s
  exact congrArg Subtype.val (e.apply_symm_apply s)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.link_ex :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω), UFacts l η Ψ M m (upl Ω L) → IsAbelianGalois ℚ L → galOf ℚ L Ω = upl Ω L ⊓ η.ker → g₁ ∈ galOf ℚ L Ω → ∃ Φ : Frame l (ResidueField O), Linked l η Ψ σ g₁ B M L Φ := by
  intro Ω _ _ _ l hl O _ _ _ η Ψ σ B M Hb g m L _ _ _ _ g₁ U hab hgal hg₁
  classical
  haveI := tf L Ω
  haveI := tf (W.Lp L) Ω
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ,
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : IsGalois (W.Lp L) Ω := {}
  haveI := g.fin
  obtain ⟨e, he⟩ := equiv_ex Ω L
  have he' : ∀ s : upl Ω L, galEmb ℚ (W.Lp L) Ω (e.symm s) = s := fun s => by rw [← he, e.apply_symm_apply]
  obtain ⟨hDI, -, hcyc, -⟩ := galEmbFam ℚ (W.Lp L) Ω l
  have hcont := (galEmbTop ℚ (W.Lp L) Ω).1.continuous
  obtain ⟨D, δ, hD, -, hδ, hηδ⟩ := g.quad
  have hσ : η σ = -1 := eta_cc g.cc hD hδ hηδ
  have hσU : σ ∈ upl Ω L := U.real σ g.cc
  have hg : g₁ ∈ upl Ω L ⊓ η.ker := hgal ▸ hg₁
  obtain ⟨a, hk1, hk2⟩ := g.cyc
  have ho1 := kills_open (pow_ne_zero a g.M_ne) hk1
  have ho2 := kills_open (pow_ne_zero a g.M_ne) hk2
  set E := galEmb ℚ (W.Lp L) Ω with hE
  set K : Subgroup (G (W.Lp L) Ω) := (η.ker ⊓ (barChar O Ψ).ker).comap E with hK
  have hKo : IsOpen (K : Set (G (W.Lp L) Ω)) := (ho1.inter ho2).preimage hcont
  have hKi : ¬ l ∣ K.index := by
    have h1 : K = ((η.prod (barChar O Ψ)).comp E).ker := by rw [hK, ← MonoidHom.comap_ker, MonoidHom.ker_prod]
    rw [h1, Subgroup.index_ker]
    intro h
    have h2 := h.trans (Subgroup.card_subgroup_dvd_card _)
    rw [Nat.card_prod, hl.out.dvd_mul] at h2
    rcases h2 with h2 | h2
    · rw [Nat.card_eq_fintype_card, Fintype.card_units_int] at h2
      exact g.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h2)
    · haveI := Fintype.ofFinite (ResidueField O)
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l h2
      have h3 : ((x : ResidueField O) - 1) ^ l = 0 := by
        rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one, sub_self]
      have h4 : x = 1 := Units.ext (sub_eq_zero.1 (pow_eq_zero_iff hl.out.ne_zero |>.1 h3))
      rw [h4, orderOf_one] at hx
      exact hl.out.one_lt.ne hx
  have hfin : {v : HeightOneSpectrum (𝓞 (W.Lp L)) | ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 (W.Lp L))})
      (mt Ideal.span_singleton_eq_bot.1 (Nat.cast_ne_zero.2 hl.out.ne_zero))).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hval : ∀ {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 (W.Lp L))}, IsPlaceOver A v →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal) := fun {A v} h => (places (W.Lp L) Ω l A).2.2.1 v h
  set N := GC.tameN (S : Set (HeightOneSpectrum (𝓞 (W.Lp L)))) K with hN
  haveI : N.Normal := Subgroup.is_normal_topologicalClosure _
  haveI hNc : IsClosed (N : Set (G (W.Lp L) Ω)) := Subgroup.isClosed_topologicalClosure _
  have hNK : N ≤ K := tame_le _ _ _ (K.isClosed_of_isOpen hKo) fun _ _ _ _ => inf_le_right
  have hNc' : N ≤ (cycZ (W.Lp L) Ω l).ker :=
    tame_le _ _ _ (isClosed_singleton.preimage (continuous_cycZ _ _ l)) fun v hv A hA =>
      inf_le_left.trans ((places (W.Lp L) Ω l A).2.2.2 fun h => hv ((hS v).2 ((hval hA).1 h)))
  have hc : η (E (e.symm ⟨σ, hσU⟩)) = -1 := by rw [he']; exact hσ
  choose A hA hAγ using fun v : W.Vl l L => place_ex l hc g.over_l v.1 v.2
  have hAl : ∀ v, (A v).valuation (l : Ω) < 1 := fun v => (hval (hA v)).2 v.2
  have hAM : ∀ v, (A v).valuation (M : Ω) < 1 := fun v => by
    obtain ⟨k, hk⟩ := g.l_dvd
    rw [hk, Nat.cast_mul, map_mul]
    exact mul_lt_one_of_lt_of_le (hAl v) (valuation_natCast_le_one _ k)
  choose c hcc using fun w : InfinitePlace (W.Lp L) => cc_ex (Ω := Ω) w
  have hDec : ∀ (B' : ValuationSubring Ω) s, s ∈ Dec (F := W.Lp L) B' ↔ E s ∈ Dec (F := ℚ) B' := fun B' s => by
    rw [← (hDI B').1]; rfl
  have hIne : ∀ (B' : ValuationSubring Ω) s, s ∈ Ine (F := W.Lp L) B' ↔ E s ∈ Ine (F := ℚ) B' := fun B' s => by
    rw [← (hDI B').2]; rfl
  have hEU : ∀ s, E s ∈ upl Ω L := fun s => he s ▸ (e s).2
  let π : G (W.Lp L) Ω →* G (W.Lp L) Ω ⧸ N := QuotientGroup.mk' N
  let del : G (W.Lp L) Ω ⧸ N →* ℤˣ := QuotientGroup.lift N (η.comp E) fun s hs => (hNK hs).1
  let Φ : Frame l (ResidueField O) :=
    { Γ := G (W.Lp L) Ω ⧸ N
      td := (AlgebraTools.totallyDisconnected_quot _ N hNc).1
      del := del
      c := π (e.symm ⟨σ, hσU⟩)
      V := W.Vl l L
      fV := haveI : Finite (W.Vl l L) := hfin.to_subtype; Fintype.ofFinite _
      Gv := fun v => Dec (F := W.Lp L) (A v)
      cv := fun v => isCompact_iff_compactSpace.1 (isClosed_Dec (F := W.Lp L) (A v)).isCompact
      loc0 := fun v => (π.comp (Dec (F := W.Lp L) (A v)).subtype).codRestrict _ fun s =>
        U.split (A v) (hAM v) ⟨(hDec _ _).1 s.2, hEU _⟩
      Iv := fun v => (Ine (F := W.Lp L) (A v)).comap (Dec (F := W.Lp L) (A v)).subtype
      dv := fun v => locDeg v.1
      Inf := InfinitePlace (W.Lp L)
      cw := fun w => π (c w)
      eps := QuotientGroup.lift N (cycZ (W.Lp L) Ω l) hNc'
      Ψ := QuotientGroup.lift N ((barChar O Ψ).comp E) fun s hs => (hNK hs).2
      g0 := ⟨π (e.symm ⟨g₁, hg.1⟩), (congrArg η (he' ⟨g₁, hg.1⟩)).trans hg.2⟩ }
  let k : GalLink η Ψ σ g₁ B M L Φ :=
    { ab := hab
      gal := hgal
      unr := U.unr
      split := U.split
      teich := U.teich
      p := π.comp (e.symm : upl Ω L →* G (W.Lp L) Ω)
      p_cont := QuotientGroup.continuous_mk.comp e.symm.continuous
      p_surj := (QuotientGroup.mk'_surjective N).comp e.symm.surjective
      p_ker := by
        rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
        refine clos_comap e.symm _ _ ?_ fun x hx => ?_
        · rintro x ⟨B', hB', h1, h2, h3⟩
          obtain ⟨a1, a2, -⟩ := places (W.Lp L) Ω l B'
          have hx : e.symm x ∈ Ine (F := W.Lp L) B' := by rw [hIne, he']; exact h1
          by_cases ht : B' = ⊤
          · rw [(a2 ht).1, Subgroup.mem_bot] at hx
            exact Or.inl (e.symm.injective (hx.trans (map_one _).symm))
          · obtain ⟨v, hv⟩ := a1 ht
            refine Or.inr ?_
            simp only [Set.mem_iUnion]
            refine ⟨v, fun h => hB' ((hval hv).2 ((hS v).1 h)), B', hv, hx, ?_⟩
            show E (e.symm x) ∈ η.ker ⊓ (barChar O Ψ).ker
            rw [he']
            exact ⟨h2, h3⟩
        · simp only [Set.mem_iUnion] at hx
          obtain ⟨v, hv, B', hB', h1, h2⟩ := hx
          have h3 : E (e.symm x) ∈ η.ker ⊓ (barChar O Ψ).ker := h2
          have h4 := (hIne _ _).1 h1
          rw [he'] at h3 h4
          exact ⟨B', fun h => hv ((hS v).2 ((hval hB').1 h)), h4, h3.1, h3.2⟩
      del := fun s => congrArg η (he' s)
      eps := fun s => (DFunLike.congr_fun hcyc (e.symm s)).symm.trans (congrArg (cycZ ℚ Ω l) (he' s))
      psi := fun s => congrArg (barChar O Ψ) (he' s)
      c := ⟨hσU, rfl⟩
      g0 := ⟨hg.1, rfl⟩
      pl := A
      pl_conj := hAγ
      pl_all := fun B' hB' => by
        obtain ⟨a1, a2, -⟩ := places (W.Lp L) Ω l B'
        obtain ⟨v, hv⟩ := a1 fun h => (a2 h).2 hB'
        obtain ⟨u, hu⟩ := exists_smul_eq_of_isPlaceOver (hA ⟨v, (hval hv).1 hB'⟩) hv
        refine ⟨⟨v, (hval hv).1 hB'⟩, ⟨E u, hEU u, hu.symm⟩, ?_⟩
        rintro v' ⟨u', hu', h⟩
        have h1 := over_smul (hA v') (e.symm ⟨u', hu'⟩)
        rw [← emb_smul, he', ← h] at h1
        exact Subtype.ext (eq_of_isPlaceOver h1 hv)
      j := fun v => (e : G (W.Lp L) Ω →* upl Ω L).comp (Dec (F := W.Lp L) (A v)).subtype
      j_cont := fun v => e.continuous.comp continuous_subtype_val
      j_inj := fun v => e.injective.comp Subtype.val_injective
      j_range := fun v s => by
        refine ⟨?_, fun h => ⟨⟨e.symm s, by rw [hDec, he']; exact h⟩, e.apply_symm_apply s⟩⟩
        rintro ⟨t, rfl⟩
        exact he t.1 ▸ (hDec _ _).1 t.2
      j_loc := fun v s => (congrArg π (e.symm_apply_apply s.1)).symm
      j_ine := fun v s => (hIne _ s.1).trans (he s.1 ▸ Iff.rfl)
      dv := fun v => (deg_eq l (hA v) v.2).trans (by rw [upl_eq])
      mu := fun v => by
        obtain ⟨s, hs, h⟩ := U.mu (A v) (hAl v)
        refine ⟨⟨e.symm ⟨s, hs.2⟩, by rw [hDec, he']; exact Ine_le_Dec _ hs.1⟩, ?_⟩
        exact (congrArg Subtype.val (e.apply_symm_apply ⟨s, hs.2⟩)).symm ▸ h }
  refine ⟨Φ, k, S, π, fun v => (Dec (F := W.Lp L) (A v)).subtype, Subtype.val, Equiv.refl _, c,
    ⟨inferInstance, GC.gLink_quot l g.odd (fun v hv => (hS v).2 hv) inferInstance hKo hKi, fun w hw => (hS w).1 hw,
      ⟨hA, Subtype.val_injective, fun w => ⟨?_, fun h => ⟨⟨w, h⟩, rfl⟩⟩, fun v => continuous_subtype_val,
        fun v => Subtype.val_injective, fun v => Subgroup.range_subtype _⟩,
      fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, hcc, fun _ => rfl, ?_, hc, fun _ h => h.1, fun _ h => h.2⟩,
    fun s h => congrArg π ?_, fun v s => (he s.1).symm⟩
  · rintro ⟨v, rfl⟩
    exact v.2
  · exact (QuotientGroup.isQuotientMap_mk N).isOpen_preimage.1 (ho1.preimage hcont)
  · exact (e.symm_apply_eq.2 (Subtype.ext (he s).symm)).symm
end

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

namespace UpperTheory.V.Fr.DescentValuationAlt

private theorem smul_val_lt {Ω : Type} [Field Ω] [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  have fix : ∀ y : Ω, g y = y → (y ∈ g • A ↔ y ∈ A) := by
    intro y hy
    have hy' : g • y = y := hy
    constructor
    · intro h
      obtain ⟨s, hs, hgs⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists g y A).mp h
      have : s = y := by
        rw [← inv_smul_smul g s, hgs, inv_smul_eq_iff, hy']
      rwa [this] at hs
    · intro h
      have := ValuationSubring.smul_mem_pointwise_smul g y A h
      rwa [hy'] at this
  have vlt : ∀ (C : ValuationSubring Ω) (x : Ω), x ≠ 0 → (C.valuation x < 1 ↔ x ∈ C ∧ x⁻¹ ∉ C) := by
    intro C x hx
    haveI : Nontrivial C.ValueGroup := GroupWithZero.toNontrivial
    rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, map_inv₀,
      inv_le_one₀ ((Valuation.pos_iff _).mpr hx), lt_iff_le_not_ge]
  by_cases h0 : (n : Ω) = 0
  · rw [h0, map_zero]
    haveI : Nontrivial (g • A).ValueGroup := GroupWithZero.toNontrivial
    exact zero_lt_one
  · have hn : g (n : Ω) = n := map_natCast g n
    have hni : g ((n : Ω)⁻¹) = (n : Ω)⁻¹ := by rw [map_inv₀, hn]
    rw [vlt _ _ h0] at hA ⊢
    rw [fix _ hn, fix _ hni]
    exact hA

private theorem descend {U Γ k : Type} [Group U] [TopologicalSpace U] [IsTopologicalGroup U] [CompactSpace U]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ] [CommRing k] (p : U →* Γ) (hc : Continuous p)
    (hs : Function.Surjective p) (S : Set U) (hk : p.ker = (Subgroup.normalClosure S).topologicalClosure)
    (χ : Γ →* kˣ) (y : U → k) (hl : IsLocallyConstant y) (hy : ∀ s t, y (s * t) = y s + χ (p s) * y t)
    (hS : ∀ s ∈ S, y s = 0) :
    ∃ φ : Γ → k, IsLocallyConstant φ ∧ ∀ s, φ (p s) = y s := by
  have hy1 : y 1 = 0 := by
    have e := hy 1 1
    rw [mul_one, map_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  let H : Subgroup U :=
    { carrier := {t | p t = 1 ∧ y t = 0}
      one_mem' := ⟨map_one p, hy1⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        show p (a * b) = 1 ∧ y (a * b) = 0
        refine ⟨by rw [map_mul, ha1, hb1, one_mul], ?_⟩
        rw [hy, ha2, hb2, mul_zero, add_zero]
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        show p a⁻¹ = 1 ∧ y a⁻¹ = 0
        refine ⟨by rw [map_inv, ha1, inv_one], ?_⟩
        have e := hy a a⁻¹
        rw [mul_inv_cancel, hy1, ha2, ha1, map_one, Units.val_one, one_mul, zero_add] at e
        exact e.symm }
  have hH : H.Normal := ⟨fun t ht g => by
    obtain ⟨ht1, ht2⟩ := ht
    show p (g * t * g⁻¹) = 1 ∧ y (g * t * g⁻¹) = 0
    refine ⟨by rw [map_mul, map_mul, map_inv, ht1, mul_one, mul_inv_cancel], ?_⟩
    have e1 := hy (g * t) g⁻¹
    have e2 := hy g t
    have e3 := hy g g⁻¹
    rw [mul_inv_cancel, hy1] at e3
    rw [map_mul, ht1, mul_one] at e1
    rw [ht2, mul_zero, add_zero] at e2
    rw [e1, e2, ← e3]⟩
  have hcl : IsClosed (H : Set U) :=
    (isClosed_eq hc continuous_const).inter (hl.isClosed_fiber 0)
  have hKH : p.ker ≤ H := by
    rw [hk]
    apply Subgroup.topologicalClosure_minimal _ _ hcl
    haveI := hH
    apply Subgroup.normalClosure_le_normal
    intro s hsS
    have hps : p s = 1 := by
      rw [← MonoidHom.mem_ker, hk]
      exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hsS)
    exact ⟨hps, hS s hsS⟩
  have hfib : ∀ s t, p s = p t → y s = y t := by
    intro s t hst
    have hk' : s⁻¹ * t ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]
    obtain ⟨_, h2⟩ := hKH hk'
    have e := hy s (s⁻¹ * t)
    rw [mul_inv_cancel_left, h2, mul_zero, add_zero] at e
    exact e.symm
  have hq : Topology.IsQuotientMap p := (hc.isClosedMap).isQuotientMap hc hs
  refine ⟨fun γ => y (Function.surjInv hs γ), fun V => ?_, fun s => hfib _ _ (Function.surjInv_eq hs (p s))⟩
  have e : p ⁻¹' ((fun γ => y (Function.surjInv hs γ)) ⁻¹' V) = y ⁻¹' V := by
    ext s
    simp only [Set.mem_preimage]
    rw [hfib _ _ (Function.surjInv_eq hs (p s))]
  apply hq.isOpen_preimage.mp
  rw [e]
  exact hl V

end UpperTheory.V.Fr.DescentValuationAlt

open UpperTheory.V.Fr.DescentValuationAlt in
theorem UpperTheory.V.Fr.frobenius_galoisField_four_compatibility :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L) → Nontrivial (H1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) fun _ => ⊥) := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL a ha hS
  obtain ⟨k, -⟩ := hL
  obtain ⟨y, hyl, hyc, hyn, hyd, hyi⟩ := hS
  have hχ : ∀ s : upl Ω L, (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (k.p s)
      = ((barChar O Ψ)⁻¹ ^ a * etaO O η) s := by
    intro s
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply,
      MonoidHom.inv_apply, MonoidHom.inv_apply, k.psi]
    congr 1
    simp only [Frame.delK, etaO, MonoidHom.comp_apply, k.del]
  have hUc : IsClosed (upl Ω L : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen _ hU.isOpen
  haveI : CompactSpace (upl Ω L) := isCompact_iff_compactSpace.mp hUc.isCompact
  obtain ⟨φ, hφl, hφ⟩ := descend k.p k.p_cont k.p_surj _ k.p_ker (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))
    (fun s => y s) (hyl.comp_continuous continuous_subtype_val)
    (fun s t => by rw [hχ s]; exact hyc s t)
    (fun s hs => by
      obtain ⟨B', hB', hI, hη, hb⟩ := hs
      exact hyi B' hB' s (Subgroup.mem_inf.mpr ⟨hI, s.2⟩) hη hb)
  have hρ : ∀ (γ : Φ.Γ) (w : ResidueField O),
      (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ) w
        = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * w := fun γ w => rfl
  have hcoc : ∀ γ δ : Φ.Γ, φ (γ * δ)
      = φ γ + ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) γ : ResidueField O) * φ δ := by
    intro γ δ
    obtain ⟨s, rfl⟩ := k.p_surj γ
    obtain ⟨t, rfl⟩ := k.p_surj δ
    rw [← map_mul, hφ, hφ, hφ, hχ]
    exact hyc s t
  have hloc : ∀ v : Φ.V, ∃ b : ResidueField O, ∀ g : Φ.Gv v,
      φ (Φ.loc v g) = ((Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O)) (Φ.loc v g) : ResidueField O) * b - b := by
    intro v
    obtain ⟨γ, -, hγ⟩ := k.pl_conj v
    have hv : (k.pl v).valuation (l : Ω) < 1 := by
      rw [hγ]
      exact smul_val_lt γ B l hG.over_l
    obtain ⟨b, hb⟩ := hyd _ hv
    refine ⟨b, fun g => ?_⟩
    rw [k.j_loc, hφ, hχ]
    exact hb _ ((k.j_range v _).mp (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
  choose b hb using hloc
  let z : Z1C Φ.loc (chRep (Φ.Ψ⁻¹ ^ a * Φ.delK (ResidueField O))) (fun _ => ⊥) :=
    ⟨(φ, b), ⟨hφl, fun γ δ => by rw [hρ]; exact hcoc γ δ,
      fun v g => by rw [Submodule.mem_bot, hρ, ← hb v g, sub_self]⟩⟩
  refine ⟨⟨Submodule.Quotient.mk z, 0, fun h => ?_⟩⟩
  have hz := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [Submodule.mem_comap] at hz
  obtain ⟨X, hX1, -⟩ := hz
  apply hyn
  refine ⟨X, fun s hs => ?_⟩
  have e1 := hφ ⟨s, hs⟩
  have e2 := hX1 (k.p ⟨s, hs⟩)
  rw [hρ, hχ] at e2
  rw [← e2]
  exact e1.symm
end

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.clrk_tr :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (U : Subgroup (G ℚ Ω)), U ≤ galOf ℚ F Ω → GC.clRk l (U.comap (galEmb ℚ F Ω)) = GC.clRk l U := by
  intro Ω _ _ _ l _ F _ _ _ U hU
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  have hemb := (galEmbTop ℚ F Ω).1
  have hfam := (galEmbFam ℚ F Ω l).1
  let e : U.comap (galEmb ℚ F Ω) ≃ U :=
    { toFun := fun u => ⟨galEmb ℚ F Ω u.1, u.2⟩
      invFun := fun u => ⟨Kum.toGal F hU u, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Continuous e := (hemb.continuous.comp continuous_subtype_val).subtype_mk _
  have hc' : Continuous e.symm := (hemb.continuous_iff.2 continuous_subtype_val).subtype_mk _
  have hI : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Ine (F := ℚ) A ↔ σ ∈ Ine (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).2 σ
  have hD : ∀ (A : ValuationSubring Ω) (σ : G F Ω), galEmb ℚ F Ω σ ∈ Dec (F := ℚ) A ↔ σ ∈ Dec (F := F) A :=
    fun A σ => SetLike.ext_iff.1 (hfam A).1 σ
  have key : (Kum.XDual 1 U (ZMod l) (ZMod l)).map (LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).toLinearMap =
      Kum.XDual 1 (U.comap (galEmb ℚ F Ω)) (ZMod l) (ZMod l) := by
    ext φ
    constructor
    · rintro ⟨ψ, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨h1.comp_continuous hc, fun a b => h2 (e a) (e b), fun A u h => h3 A (e u) ((hI A _).2 h),
        fun A hA u h => h4 A hA (e u) ((hD A _).2 h)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨φ ∘ e.symm, ⟨h1.comp_continuous hc', fun a b => h2 (e.symm a) (e.symm b),
        fun A u h => h3 A (e.symm u) ((hI A _).1 h), fun A hA u h => h4 A hA (e.symm u) ((hD A _).1 h)⟩, rfl⟩
  unfold GC.clRk
  rw [← key]
  exact ((LinearEquiv.funCongrLeft (ZMod l) (ZMod l) e).submoduleMap _).rank_eq.symm
end

section
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem cycMod_emb (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra F Ω]
    (l : ℕ) [Fact l.Prime] (g : G F Ω) : cycMod ℚ Ω l 1 (galEmb ℚ F Ω g) = cycMod F Ω l 1 g := rfl

private theorem one_of_cast (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (x : ℤ_[l])
    (h : ZMod.castHom (dvd_refl l) k (PadicInt.toZMod x) = 1) : PadicInt.toZModPow 1 x = 1 := by
  have h1 : x - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    exact (ZMod.castHom (dvd_refl l) k).injective (h.trans (map_one _).symm)
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
  exact h1

private theorem rk_link {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (L : Type) [Field L]
    [NumberField L] [IsCMField L] [Algebra L Ω] (A A' : Subgroup (G ℚ Ω)) :
    GC.clRk l ((A ⊓ A').comap (galEmb ℚ (W.Lp L) Ω) ⊓ (cycMod (W.Lp L) Ω l 1).ker) =
      GC.clRk l (upl Ω L ⊓ A ⊓ A' ⊓ (cycMod ℚ Ω l 1).ker) := by
  have hU : upl Ω L ⊓ A ⊓ A' ⊓ (cycMod ℚ Ω l 1).ker ≤ galOf ℚ (W.Lp L) Ω :=
    fun g hg x => hg.1.1.1 x.1 x.2
  rw [← clrk_tr Ω l (W.Lp L) _ hU]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker]
  rw [cycMod_emb]
  constructor
  · rintro ⟨⟨ha, ha'⟩, hc⟩
    exact ⟨⟨⟨fun x hx => galEmb_mem ℚ (W.Lp L) Ω g ⟨x, hx⟩, ha⟩, ha'⟩, hc⟩
  · rintro ⟨⟨⟨_, ha⟩, ha'⟩, hc⟩
    exact ⟨⟨ha, ha'⟩, hc⟩

private theorem ok_link (P : GC.Hypotheses₂) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type}
    [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ : G ℚ Ω}
    {B : ValuationSubring Ω} {M : ℕ} {Hb : Subgroup (G ℚ Ω)} (hG : Gen l η Ψ σ B M Hb) (m C₀ : ℕ) (L : Type) [Field L]
    [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O))
    (hU : UFacts l η Ψ M m (upl Ω L)) (hL : Linked l η Ψ σ g₁ B M L Φ) (hg : barChar O Ψ g₁ ^ 2 ≠ 1)
    (hS : ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L))
    (hC : GC.clRk l (upl Ω L ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker) ≤ C₀) (hm : 3 * C₀ + 7 < l ^ m) :
    Φ.Ok C₀ ∧ Φ.Big C₀ := by
  haveI : IsAlgClosure (W.Lp L) Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) (W.Lp L)⟩
  have hb := ok_basic l η Ψ σ B M Hb hG m L g₁ Φ hU hL hg
  obtain ⟨h_del_open, h_csq, h_delc, h_loc, h_eps, h_Ψopen, h_Ψc, h_g0, h_card, h_cw, h_delcw,
    h_f2a, h_f2b, h_f2c, h_f3, h_f5, h_ΨN, h_dv, h_ne⟩ := hb
  have hf4 := frobenius_galoisField_four_compatibility l η Ψ σ B M Hb hG m L g₁ Φ hU hL 1 (Or.inl rfl) (hS 1 (Or.inl rfl))
  have hf4' := frobenius_galoisField_four_compatibility l η Ψ σ B M Hb hG m L g₁ Φ hU hL 2 (Or.inr rfl) (hS 2 (Or.inr rfl))
  rw [pow_one] at hf4
  obtain ⟨k, S, π, ι, pl, e, c, hF, hπ, hι⟩ := hL
  have hrk : GC.clRk l (((η.ker ⊓ (barChar O Ψ).ker).comap (galEmb ℚ (W.Lp L) Ω)) ⊓
      (cycMod (W.Lp L) Ω l 1).ker) ≤ C₀ := by
    rw [rk_link l L η.ker (barChar O Ψ).ker]
    exact hC
  have hom : ∀ v : Φ.V, ∃ s, (Φ.om (ResidueField O)) ((Φ.loc v) s) ≠ 1 := by
    intro v
    obtain ⟨g, hg'⟩ := k.mu v
    refine ⟨g, fun h => hg' ?_⟩
    rw [k.j_loc] at h
    simp only [Frame.om, MonoidHom.comp_apply, k.eps] at h
    have h1 := congrArg Units.val h
    simp only [Units.coe_map, Units.val_one, MonoidHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply] at h1
    apply Units.ext
    simp only [cycMod, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    exact one_of_cast l (ResidueField O) _ h1
  have hfin : Finite (ResidueField O) := hG.fin
  have hok : Φ.Ok C₀ :=
    { l_odd := hG.odd
      fin := hfin
      del_open := h_del_open
      c_sq := h_csq
      del_c := h_delc
      loc_cont := h_loc
      eps_cont := h_eps
      Ψ_open := h_Ψopen
      Ψ_c := h_Ψc
      baseSubgroup_spec := h_g0
      phi := GC.phi _ Ω l _ Φ S _ π ι k.pl pl e c hF
      card_inf := h_card
      cw_sq := h_cw
      del_cw := h_delcw
      f2a := h_f2a
      f2b := h_f2b
      f2c := h_f2c
      f3 := h_f3
      f4 := hf4
      f4' := hf4'
      f5 := h_f5
      Ψ_N := h_ΨN
      gen := GC.gen P _ Ω l _ Φ S _ π ι k.pl pl e c hF hom
      cl := GC.cl _ Ω l _ Φ S _ π ι k.pl pl e c hF
      ec := GC.ec P _ Ω l _ Φ S _ π ι k.pl pl e c hF
      b1p := GC.b1p _ Ω l _ Φ S _ π ι k.pl pl e c hF h_f3 C₀ hrk
      b1 := GC.b1 _ Ω l _ Φ S _ π ι k.pl pl e c hF h_f3 C₀ hrk
      h1 := GC.h1 P _ Ω l _ Φ S _ π ι k.pl pl e c hF hfin hom C₀ hrk }
  refine ⟨hok, ?_, ?_⟩
  · obtain ⟨v⟩ := h_ne
    have h1 : Φ.dv v ≤ Φ.d := by
      unfold Frame.d
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    have := h_dv v
    omega
  · intro v
    have := h_dv v
    omega

theorem UpperTheory.V.Fr.frame_ex :
    GC.Hypotheses₂ → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ Q : ℕ, Q ≠ 0 → HasFrameW l η Ψ σ B M Q := by
  intro P Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG Q hQ
  obtain ⟨H₀, h0⟩ := exists_twistCharacter_continuousCohomology l η Ψ σ B M Hb hG
  obtain ⟨w, hw, hwQ⟩ := auxw_ex l η Ψ σ B M Hb hG Q hQ
  obtain ⟨C₀, hC₀⟩ := b0 l η Ψ σ B M Hb hG H₀ w h0 hw
  have hl : l.Prime := Fact.out
  set m := 3 * C₀ + 7 with hm_def
  have hm : 3 * C₀ + 7 < l ^ m := Nat.lt_pow_self hl.one_lt
  have hU := ufacts l η Ψ σ B M Hb hG H₀ w h0 hw m
  obtain ⟨L, iF, iN, iC, iA, hab, hup, hgal⟩ := field_ex l η Ψ σ B M Hb hG m _ hU
  have hM : B.valuation (M : Ω) < 1 := by
    obtain ⟨t, ht⟩ := hG.l_dvd
    rw [ht, Nat.cast_mul, map_mul]
    have hle : B.valuation (t : Ω) ≤ 1 := B.valuation_le_one ⟨(t : Ω), natCast_mem B t⟩
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hle) hG.over_l
  obtain ⟨s, ⟨hsD, hsU⟩, hs2⟩ := hU.f3 B hG.over_l
  have hsη : s ∈ η.ker := hU.split B hM ⟨hsD, hsU⟩
  have hs : s ∈ galOf ℚ L Ω := by
    rw [hgal]
    exact ⟨hsU, hsη⟩
  rw [← hup] at hU
  obtain ⟨Φ, hL⟩ := link_ex l η Ψ σ B M Hb hG m L s hU hab (by rw [hgal, hup]) hs
  have hS : ∀ a : ℕ, a = 1 ∨ a = 2 → StrictCl l η Ψ ((barChar O Ψ)⁻¹ ^ a * etaO O η) (upl Ω L) := by
    intro a ha
    rw [hup]
    exact strict P l η Ψ σ B M Hb hG H₀ w h0 hw m a ha
  have hC : GC.clRk l (upl Ω L ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker) ≤ C₀ := by
    rw [hup]
    exact hC₀ m
  obtain ⟨hok, hbig⟩ := ok_link P l hG m C₀ L s Φ hU hL hs2 hS hC hm
  refine ⟨L, iF, iN, iC, iA, s, Φ, C₀, w, hL, hok, hbig, hw, hwQ, ?_⟩
  rw [hup]
  intro x hx
  exact hx.1.1.2
end
