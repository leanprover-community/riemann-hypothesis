import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfValLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed

section
open NumberField IsDedekindDomain

namespace GlobalTheory.WildOpenKernel

theorem eq_one_of_wild_prime {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M)
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P)
    (hop : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : φ σ ^ l = 1) : φ σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (by simp))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ n ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n)
      (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : φ σ ^ n = 1 := by
    have h2 : σ ^ n ∈ φ.ker := hsub hτ
    rw [MonoidHom.mem_ker, map_pow] at h2
    exact h2
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := φ σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

theorem eq_one_of_wild : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := by
  intro E Ω _ _ _ _ _ M _ φ P A m hA hop hm τ hτ ⟨N, hN⟩
  by_contra hne
  have hd : orderOf (φ τ) ∣ m ^ N := orderOf_dvd_of_pow_eq_one hN
  have hne1 : orderOf (φ τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
  have hlm : l ∣ m := hl.dvd_of_dvd_pow (dvd_trans ⟨k, hk⟩ hd)
  have hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hm
    obtain ⟨c, hc⟩ := hlm
    rw [hc]
    push_cast
    exact Ideal.mul_mem_right _ _ h
  have h1 : φ (τ ^ k) = 1 := by
    refine eq_one_of_wild_prime φ P A hA hop l hl hlv _
      (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
    rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  rw [map_pow] at h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have ho : orderOf (φ τ) ≠ 0 := fun h =>
    pow_ne_zero N hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ho (by simpa using hk)
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
  rw [hk] at h3
  have := hl.two_le
  have := Nat.pos_of_ne_zero hk0
  nlinarith

end GlobalTheory.WildOpenKernel
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openKerChar_wild_eq_one_of_pow_eq_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := by
  first | exact @GlobalTheory.WildOpenKernel.eq_one_of_wild | exact GlobalTheory.WildOpenKernel.eq_one_of_wild | (intros; apply GlobalTheory.WildOpenKernel.eq_one_of_wild <;> assumption)
end

section
open NumberField IsDedekindDomain

namespace GlobalTheory.TameJoint

theorem exists_pow_joint : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  intro E Ω _ _ _ _ _ M _ φ P A L γ π w hA hker hL hγ hw hγL hπ he σ hσ
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hn : 0 < L := Nat.pos_of_ne_zero hL0
  have hLA : ¬ A.valuation (L : Ω) < 1 := by
    intro h
    apply hL
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ L = 1 := by
    rw [hζ, div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
    rw [← he]; exact pow_ne_zero _ hπ
  have hred : ∀ {N : Type} [Monoid N] (x : N), x ^ L = 1 → ∀ a : ℕ, x ^ a = x ^ (a % L) := by
    intro N _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a L, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ L = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he' | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hL0).ne
    · exact he'
    · exact absurd hp (one_lt_pow₀ hg hL0).ne'

  have hfixζ : ∀ τ ∈ ReciprocityTheory.Gal.Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ L = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA h1 (one_pow L) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hopenH : ∀ (H : Subgroup (Formalism.ConjugateSelfDual.G E Ω)), IsOpen (H : Set (Formalism.ConjugateSelfDual.G E Ω)) →
      ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ H, τ * g ∈ U) → IsOpen U := by
    intro H hH U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hH.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hHo _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hfib : ∀ c : M, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | φ τ = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hker _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [map_mul, (MonoidHom.mem_ker).1 hg, mul_one]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range L, {τ | φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (hfib _).inter (hloc _)
  let Q : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ ReciprocityTheory.Gal.Ine (F := E) A ∧ ∃ a : ℕ, φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π
  have hQ : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), Q τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩
      · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero],
          by rw [hfixπ x hx, pow_zero, one_mul]⟩
    | one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      obtain ⟨hyI, b, hb, hbπ⟩ := ihy
      refine ⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩
      rw [AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]
      ring
    | inv x _ ihx =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      have hiI : x⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A := inv_mem hxI
      have hex : a * (L - 1) + a = a * L := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (L - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγL, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (L - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (L - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (L - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hQ τ hτ
    refine Set.mem_biUnion (x := a % L) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγL a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  simp only [T, Set.mem_iUnion] at hσT
  obtain ⟨a, -, h⟩ := hσT
  exact ⟨a, h⟩

end GlobalTheory.TameJoint
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_of_tameGenAt_of_char_pow_eq_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  first | exact @GlobalTheory.TameJoint.exists_pow_joint | exact GlobalTheory.TameJoint.exists_pow_joint | (intros; apply GlobalTheory.TameJoint.exists_pow_joint <;> assumption)
end

section
open NumberField IsDedekindDomain

namespace GlobalTheory.TameRootSurj

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem irreducible_X_pow_sub_C {E : Type} [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) {L : ℕ} (hL : 0 < L) {ϖ : 𝓞 E}
    (hmem : ϖ ∈ P.asIdeal) (hnot : ϖ ∉ P.asIdeal ^ 2) :
    Irreducible (X ^ L - C (ϖ : E)) := by
  have hmon : (X ^ L - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hL.ne'
  have hdeg : (X ^ L - C ϖ : (𝓞 E)[X]).natDegree = L := natDegree_X_pow_sub_C
  have hEis : (X ^ L - C ϖ : (𝓞 E)[X]).IsEisensteinAt P.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using P.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hL.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ L - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible P.isPrime hmon.isPrimitive (by rw [hdeg]; exact hL)
  have hmap : (X ^ L - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ L - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr

theorem main : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  intro E Ω _ _ _ _ _ P A L ϖ π hA hL h1 h2 hπ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0, eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · have hL1 : L = 1 := by omega
    subst hL1
    refine ⟨1, one_mem _, ?_⟩
    rw [AlgEquiv.one_apply, div_self hπ0]
    exact IsPrimitiveRoot.one
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero ((L : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hL0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  have hirr := irreducible_X_pow_sub_C P (Nat.pos_of_ne_zero hL0) h1 h2
  have hmon : (X ^ L - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hL0
  have hr1 : aeval π (X ^ L - C (ϖ : E)) = 0 := by simp [hπ]
  have hr2 : aeval (ζ * π) (X ^ L - C (ϖ : E)) = 0 := by simp [mul_pow, hζ.pow_eq_one, hπ]
  have hm1 := minpoly.eq_of_irreducible_of_monic hirr hr1 hmon
  have hm2 := minpoly.eq_of_irreducible_of_monic hirr hr2 hmon
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g π = ζ * π := by
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 (hm2.symm.trans hm1)
    exact ⟨g, hg⟩
  obtain ⟨-, hx2⟩ := GlobalTheory.InertiaMovesRoot.cong_on_adjoin hA hL2 h1 h2 hπ
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) π
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := 𝓞 E) H
    (primeBelow (F := E) A) g (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {π}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨π, IntermediateField.mem_adjoin_simple_self E π⟩)))
  refine ⟨k' * g * k, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong hc, ?_⟩
  have e1 : k π = π := hk
  have e2 : k' π = π := hk'
  have e3 : (k' * g * k) π / π = k' ζ := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1, hg, map_mul, e2, mul_div_cancel_right₀ _ hπ0]
  rw [e3]
  exact hζ.map_of_injective k'.injective

end GlobalTheory.TameRootSurj
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_tameChar_primitiveRoot_of_uniformizerRoot : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  first | exact @GlobalTheory.TameRootSurj.main | exact GlobalTheory.TameRootSurj.main | (intros; apply GlobalTheory.TameRootSurj.main <;> assumption)
end

section
open NumberField IsDedekindDomain

open Pointwise

namespace GlobalTheory.TameMove

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have h1 : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := by
    intro z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', h1, ← map_inv₀, h1,
    map_eq_zero_iff _ g.injective]

theorem val_smul_le_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem conj_mem_Ine_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := by
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • (g • A) = g • A
    have h : σ • A = A := hσ.1
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, h]
  · have hy : A.valuation (g⁻¹ x) ≤ 1 := by
      rw [← val_smul_le_one_iff A g, ReciprocityTheory.Gal.mul_inv_apply]; exact hx
    have e : (g * σ * g⁻¹) x - x = g (σ (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, ReciprocityTheory.Gal.mul_inv_apply]; rfl
    rw [e, val_smul_lt_one_iff]
    exact hσ.2 _ hy

theorem exists_mul_eq_of_not_mem_sq (P : HeightOneSpectrum (𝓞 E)) {ϖ ϖ₀ : 𝓞 E}
    (h₀ : ϖ₀ ∈ P.asIdeal) (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ s * ϖ₀ = t * ϖ := by
  have hle : Ideal.span {ϖ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hIP
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hI, pow_two]; exact Ideal.mul_mono_right hIP
    exact this (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  have hm : s * ϖ₀ ∈ Ideal.span {ϖ} := by
    rw [hI, mul_comm s]; exact Ideal.mul_mem_mul h₀ hsI
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨s, t, hsP, ht.symm⟩

theorem val_le_one (A : ValuationSubring Ω) (t : 𝓞 E) : A.valuation (algebraMap E Ω (t : E)) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  apply ReciprocityTheory.Gal.mem_of_isIntegral_int
  exact (NumberField.RingOfIntegers.isIntegral_coe t).map (algebraMap E Ω).toIntAlgHom

theorem val_eq_of_not_mem_sq (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {ϖ ϖ₀ : 𝓞 E} (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h₀ : ϖ₀ ∈ P.asIdeal) (h02 : ϖ₀ ∉ P.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ₀ : E)) := by
  have key : ∀ a b : 𝓞 E, a ∈ P.asIdeal → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 →
      A.valuation (algebraMap E Ω (a : E)) ≤ A.valuation (algebraMap E Ω (b : E)) := by
    intro a b ha hb hb2
    obtain ⟨s, t, hs, hst⟩ := exists_mul_eq_of_not_mem_sq P ha hb hb2
    have hvs : A.valuation (algebraMap E Ω (s : E)) = 1 :=
      le_antisymm (val_le_one A s) (not_lt.mp fun hlt => hs ((hA s).mp hlt))
    have e : algebraMap E Ω (s : E) * algebraMap E Ω (a : E) =
        algebraMap E Ω (t : E) * algebraMap E Ω (b : E) := by
      have := congrArg (fun z : 𝓞 E => algebraMap E Ω (z : E)) hst
      simpa using this
    have e2 := congrArg A.valuation e
    rw [Valuation.map_mul, Valuation.map_mul, hvs, one_mul] at e2
    rw [e2]
    calc A.valuation (algebraMap E Ω (t : E)) * A.valuation (algebraMap E Ω (b : E))
        ≤ 1 * A.valuation (algebraMap E Ω (b : E)) := mul_le_mul_left (val_le_one A t) _
      _ = _ := one_mul _
  exact le_antisymm (key _ _ h h₀ h02) (key _ _ h₀ h h2)

end GlobalTheory.TameMove

open Pointwise

namespace GlobalTheory.TameMove

theorem tameRep_move : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ P e σ u A₀ ϖ₀ π₀ hA₀ h₀ h02 hπ₀ hT
  obtain ⟨A, hA, hσ, ϖ, π, h, h2, hπ, hv⟩ := hT
  obtain ⟨g, rfl⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hA hA₀
  have hσ'I : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := conj_mem_Ine_smul hσ
  refine ⟨g, hσ'I, ?_⟩
  set B := g • A with hB
  set σ' := g * σ * g⁻¹ with hσ'
  set N := Formalism.ConjugateSelfDual.normV P - 1 with hN
  set U := (algebraMap E Ω (u : E)) ^ e with hU
  have hne : ∀ b : 𝓞 E, b ∉ P.asIdeal ^ 2 → algebraMap E Ω (b : E) ≠ 0 := by
    intro b hb hz
    apply hb
    have hb0 : b = 0 := by
      have : (b : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hz
      exact_mod_cast this
    rw [hb0]; exact Ideal.zero_mem _
  have hw : algebraMap E Ω (ϖ : E) ≠ 0 := hne ϖ h2
  have hw₀ : algebraMap E Ω (ϖ₀ : E) ≠ 0 := hne ϖ₀ h02
  have hN0 : N ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hπ₀
    have := (hA₀ ϖ₀).mpr h₀
    rw [← hπ₀, map_one] at this
    exact lt_irrefl _ this
  have hπ₀0 : π₀ ≠ 0 := by
    rintro rfl; rw [zero_pow hN0] at hπ₀; exact hw₀ hπ₀.symm

  have hπ' : (g π) ^ N = algebraMap E Ω (ϖ : E) := by
    rw [← map_pow, hπ]; exact AlgEquiv.commutes g _
  have hπ'0 : g π ≠ 0 := by
    intro hz; rw [hz, zero_pow hN0] at hπ'; exact hw hπ'.symm
  have hgg : g⁻¹ (g π) = π := by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have ha : B.valuation (σ' (g π) / g π - U) < 1 := by
    have e1 : σ' (g π) / g π - U = g (σ π / π - U) := by
      have e2 : σ' (g π) = g (σ π) := by
        show g (σ (g⁻¹ (g π))) = g (σ π)
        rw [hgg]
      have e3 : g U = U := by
        rw [hU, map_zpow₀]; congr 1; exact AlgEquiv.commutes g _
      rw [map_sub, map_div₀, e2, e3]
    rw [e1, hB, val_smul_lt_one_iff]; exact hv

  set x := g π / π₀ with hx
  have hxπ : g π = x * π₀ := by rw [hx, div_mul_cancel₀ _ hπ₀0]
  have hx0 : x ≠ 0 := div_ne_zero hπ'0 hπ₀0
  have hvx : B.valuation x = 1 := by
    have hxN : x ^ N = algebraMap E Ω (ϖ : E) / algebraMap E Ω (ϖ₀ : E) := by
      rw [hx, div_pow, hπ', hπ₀]
    have hvN : B.valuation x ^ N = 1 := by
      rw [← Valuation.map_pow, hxN, map_div₀, val_eq_of_not_mem_sq B P hA₀ h h2 h₀ h02,
        div_self ((Valuation.ne_zero_iff _).mpr hw₀)]
    rcases lt_trichotomy (B.valuation x) 1 with h1 | h1 | h1
    · exact absurd hvN (pow_lt_one₀ zero_le h1 hN0).ne
    · exact h1
    · exact absurd hvN (one_lt_pow₀ h1 hN0).ne'
  have hc : B.valuation (σ' x / x - 1) < 1 := by
    have e : σ' x / x - 1 = (σ' x - x) / x := by field_simp
    rw [e, map_div₀, hvx, div_one]
    exact hσ'I.2 x hvx.le

  have hb : (σ' π₀ / π₀) ^ N = 1 := by
    rw [div_pow, ← map_pow, hπ₀, AlgEquiv.commutes, div_self hw₀]
  have hvb : B.valuation (σ' π₀ / π₀) = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one B hN0 hb
  have hprod : σ' (g π) / g π = (σ' x / x) * (σ' π₀ / π₀) := by
    rw [hxπ, map_mul]; field_simp
  have e4 : σ' π₀ / π₀ - U = (σ' (g π) / g π - U) + -((σ' x / x - 1) * (σ' π₀ / π₀)) := by
    rw [hprod]; ring
  rw [e4]
  refine Valuation.map_add_lt _ ha ?_
  rw [Valuation.map_neg, Valuation.map_mul, hvb, mul_one]
  exact hc

end GlobalTheory.TameMove
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_inertia_tameChar_other_place : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TameMove.tameRep_move | exact GlobalTheory.TameMove.tameRep_move | (intros; apply GlobalTheory.TameMove.tameRep_move <;> assumption)
end

section
open NumberField IsDedekindDomain

namespace GlobalTheory.TamePowTeich

variable {Ω : Type} [Field Ω]

theorem valuation_pow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) : ∀ k : ℕ, A.valuation (x ^ k - y ^ k) < 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [h]
    apply Valuation.map_add_lt
    · rw [map_mul, hx, one_mul]; exact ih
    · rw [map_mul, map_pow, hy, one_pow, mul_one]; exact hxy

theorem valuation_zpow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) (e : ℤ) : A.valuation (x ^ e - y ^ e) < 1 := by
  cases e with
  | ofNat k => simpa using valuation_pow_sub_lt A hx hy hxy k
  | negSucc k =>
    simp only [zpow_negSucc]
    have hxk : A.valuation (x ^ (k + 1)) = 1 := by rw [map_pow, hx, one_pow]
    have hyk : A.valuation (y ^ (k + 1)) = 1 := by rw [map_pow, hy, one_pow]
    have hx0 : x ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxk; exact zero_ne_one hxk
    have hy0 : y ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hyk; exact zero_ne_one hyk
    rw [inv_sub_inv hx0 hy0, map_div₀, map_mul, hxk, hyk, mul_one, div_one, Valuation.map_sub_swap]
    exact valuation_pow_sub_lt A hx hy hxy (k + 1)

end GlobalTheory.TamePowTeich

open GlobalTheory.TamePowTeich in
theorem GlobalTheory.TamePowTeich.exists_zeta_pow_close : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ P A ζ hA hζ u e hu
  classical
  set n := Formalism.ConjugateSelfDual.normV P - 1 with hn_def
  letI : Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Formalism.ConjugateSelfDual.normV P = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    show Nat.card _ = _
    exact Nat.card_eq_fintype_card
  have hn : 0 < n := by
    have : 1 < Fintype.card (𝓞 E ⧸ P.asIdeal) := Fintype.one_lt_card
    omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero, hn_def, hcard]
    apply FiniteField.pow_card_sub_one_eq_one
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  set U : Ω := algebraMap E Ω (u : E) with hU
  have hUn : A.valuation (U ^ n - 1) < 1 := by
    have := (hA (u ^ n - 1)).2 hmem
    simpa [hU] using this
  have hUint : U ∈ A := by
    apply ReciprocityTheory.Gal.mem_of_isIntegral_int
    exact (u.isIntegral_coe).algebraMap
  have hU1 : A.valuation U = 1 := by
    apply le_antisymm ((A.valuation_le_one_iff U).2 hUint)
    rw [← not_lt]
    intro h
    exact hu ((hA u).1 h)
  have hζ1 : A.valuation ζ = 1 :=
    ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hn.ne' hζ.pow_eq_one

  have hprod : U ^ n - 1 = ∏ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), (U - μ) := by
    have := congrArg (Polynomial.eval U) (Polynomial.X_pow_sub_one_eq_prod hn hζ)
    simpa [Polynomial.eval_prod] using this
  have hex : ∃ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), A.valuation (U - μ) < 1 := by
    by_contra hcon
    push_neg at hcon
    have : 1 ≤ A.valuation (U ^ n - 1) := by
      rw [hprod, map_prod]
      exact Finset.one_le_prod' hcon
    exact absurd hUn (not_lt.2 this)
  obtain ⟨μ, hμ, hμU⟩ := hex
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hn 1).1 hμ)
  have hb1 : A.valuation (ζ ^ b) = 1 := by rw [map_pow, hζ1, one_pow]
  have hclose : A.valuation (ζ ^ b - U) < 1 := by
    rw [Valuation.map_sub_swap, hb]; exact hμU
  have key := valuation_zpow_sub_lt A hb1 hU1 hclose e

  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  refine ⟨((b * e) % (n : ℤ)).toNat, ?_⟩
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnonneg : 0 ≤ (b * e) % (n : ℤ) := Int.emod_nonneg _ hnz
  have hpow : (ζ ^ b) ^ e = ζ ^ ((b * e) % (n : ℤ)).toNat := by
    have h1 : ζ ^ ((b * e) % (n : ℤ)).toNat = ζ ^ ((b * e) % (n : ℤ)) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg]
    rw [h1, ← zpow_natCast ζ b, ← zpow_mul]
    conv_lhs => rw [← Int.emod_add_mul_ediv ((b : ℤ) * e) n]
    rw [zpow_add₀ hζ0, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]
  rw [← hpow]
  exact key
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeta_pow_close_to_unit_zpow : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TamePowTeich.exists_zeta_pow_close | exact GlobalTheory.TamePowTeich.exists_zeta_pow_close | (intros; apply GlobalTheory.TamePowTeich.exists_zeta_pow_close <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TameValChar

theorem L_wildKill : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := GlobalTheory.T.openKerChar_wild_eq_one_of_pow_eq_one

theorem L_joint : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := GlobalTheory.T.inertia_of_tameGenAt_of_char_pow_eq_one

theorem L_surj : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := GlobalTheory.T.exists_inertia_tameChar_primitiveRoot_of_uniformizerRoot

theorem L_move : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := GlobalTheory.T.exists_conj_inertia_tameChar_other_place

theorem L_teich : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := GlobalTheory.T.exists_zeta_pow_close_to_unit_zpow

theorem L_vone : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A P →
    ∀ u : 𝓞 E, u ∉ P.asIdeal → A.valuation (algebraMap E Ω (u : E)) = 1 := by
  intro E Ω _ _ _ _ P A hA u hu
  apply le_antisymm
  · rw [A.valuation_le_one_iff]
    apply ReciprocityTheory.Gal.mem_of_isIntegral_int
    exact (RingOfIntegers.isIntegral_coe u).algebraMap
  · exact not_lt.1 ((hA u).not.2 hu)

theorem two_le_normV_and_not_mem : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    2 ≤ Formalism.ConjugateSelfDual.normV P ∧ (((Formalism.ConjugateSelfDual.normV P - 1 : ℕ) : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro E _ _ P
  classical
  have hmax : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Formalism.ConjugateSelfDual.normV P = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    rw [Formalism.ConjugateSelfDual.normV, Nat.card_eq_fintype_card]
  have h2 : 2 ≤ Formalism.ConjugateSelfDual.normV P := by
    rw [hcard]; exact Fintype.one_lt_card
  refine ⟨h2, fun h => ?_⟩
  have h0 : (Ideal.Quotient.mk P.asIdeal) (((Formalism.ConjugateSelfDual.normV P - 1 : ℕ) : ℕ) : 𝓞 E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 h
  rw [map_natCast, Nat.cast_sub (by omega), hcard, FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub,
    neg_eq_zero] at h0
  exact one_ne_zero h0

section Small

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem not_val_lt_one {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {k : ℕ}
    (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) : ¬ A.valuation (k : Ω) < 1 := by
  intro h
  apply hk
  rw [← hA]
  simpa using h

theorem ne_zero_of_not_mem {P : HeightOneSpectrum (𝓞 E)} {k : ℕ} (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) : k ≠ 0 := by
  rintro rfl
  exact hk (by simp)

theorem ine_fix_root {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {k : ℕ}
    (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) {σ : Formalism.ConjugateSelfDual.G E Ω} (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) {ζ : Ω}
    (hζ : ζ ^ k = 1) : σ ζ = ζ := by
  refine ReciprocityTheory.Gal.eq_of_pow_eq_one A (not_val_lt_one hA hk) ?_ hζ
    (hσ.2 ζ (ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (ne_zero_of_not_mem hk) hζ).le)
  rw [← map_pow, hζ, map_one]

theorem frob_root {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {k : ℕ}
    (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) {τ : Formalism.ConjugateSelfDual.G E Ω} (hτ : Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV P) τ) {ζ : Ω}
    (hζ : ζ ^ k = 1) : τ ζ = ζ ^ Formalism.ConjugateSelfDual.normV P := by
  refine ReciprocityTheory.Gal.eq_of_pow_eq_one A (not_val_lt_one hA hk) ?_ ?_
    (hτ.2 ζ (ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (ne_zero_of_not_mem hk) hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem modEq_of_pow_eq {ζ : Ω} {k a b : ℕ} (h : IsPrimitiveRoot ζ k) (hk : k ≠ 0) (hab : ζ ^ a = ζ ^ b) :
    a ≡ b [MOD k] := by
  have hu : IsPrimitiveRoot (h.isUnit hk).unit k := IsPrimitiveRoot.coe_units_iff.mp (by simpa using h)
  rw [hu.eq_orderOf]
  apply pow_eq_pow_iff_modEq.1
  ext
  simpa using hab

theorem zpow_close {A : ValuationSubring Ω} {x y : Ω} (hy : A.valuation y = 1) (hxy : A.valuation (x - y) < 1)
    (e : ℤ) : A.valuation (x ^ e - y ^ e) < 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hw : A.valuation (x / y - 1) < 1 := by
    rw [show x / y - 1 = (x - y) / y by field_simp, map_div₀, hy, div_one]
    exact hxy
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one] at hw
    exact lt_irrefl _ hw
  have hmem : Units.mk0 (x / y) (div_ne_zero hx0 hy0) ∈ A.principalUnitGroup := by
    rw [ValuationSubring.mem_principalUnitGroup_iff]
    exact hw
  have hmem' := zpow_mem hmem e
  rw [ValuationSubring.mem_principalUnitGroup_iff] at hmem'
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hmem'
  have e1 : x ^ e - y ^ e = y ^ e * ((x / y) ^ e - 1) := by
    rw [div_zpow, mul_sub, mul_div_cancel₀ _ (zpow_ne_zero e hy0), mul_one]
  rw [e1, map_mul, map_zpow₀, hy, one_zpow, one_mul]
  exact hmem'

end Small

theorem main : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type} [CommGroup M]
    (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ),
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) →
    (∀ u u' : 𝓞 E, u ∉ P.asIdeal → u' ∉ P.asIdeal → NX.tameVal φ P e (u * u') = NX.tameVal φ P e u * NX.tameVal φ P e u') ∧
    ∀ u u' : 𝓞 E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → NX.tameVal φ P e u = NX.tameVal φ P e u' := by
  intro E Ω _ _ _ _ _ M _ φ P e m hopen hm hI
  classical
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨A0, hA0⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω P
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω P A0 hA0
  obtain ⟨hq2, hq1⟩ := two_le_normV_and_not_mem P
  set q := Formalism.ConjugateSelfDual.normV P with hqdef
  set n := q - 1 with hndef
  obtain ⟨N0, hN0⟩ := hI A0 hA0 γ hγ.1
  set L := n * m ^ N0 with hLdef
  have hL : ((L : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    rw [hLdef, Nat.cast_mul, Nat.cast_pow]
    exact P.isPrime.mul_notMem hq1 (fun h => hm (P.isPrime.mem_of_pow_mem _ h))
  have hL0 : L ≠ 0 := ne_zero_of_not_mem hL
  obtain ⟨ϖ0, hϖ0, hϖ0'⟩ : ∃ ϖ0 : 𝓞 E, ϖ0 ∈ P.asIdeal ∧ ϖ0 ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  have hϖ0ne : algebraMap E Ω (ϖ0 : E) ≠ 0 := by
    intro h
    apply hϖ0'
    have : ϖ0 = 0 := by
      have h' : ((ϖ0 : E)) = 0 := (map_eq_zero _).1 h
      exact_mod_cast h'
    rw [this]
    exact zero_mem _
  obtain ⟨π1, hπ1⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ0 : E)) (Nat.pos_of_ne_zero hL0)
  have hπ1ne : π1 ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0] at hπ1
    exact hϖ0ne hπ1.symm
  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A0.valuation (τ y / y - 1) < 1) → φ τ = 1 := fun τ hτ =>
    L_wildKill φ P A0 m hA0 hopen hm τ hτ (hI A0 hA0 τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
  have hγL : φ γ ^ L = 1 := by
    rw [hLdef, mul_comm, pow_mul, hN0, one_pow]
  have hJ := L_joint φ P A0 L γ π1 (ϖ0 : E) hA0 hopen hL hγ hw hγL hπ1ne hπ1
  set ζ1 := γ π1 / π1 with hζ1def
  have hγπ1 : γ π1 = ζ1 * π1 := by rw [hζ1def, div_mul_cancel₀ _ hπ1ne]
  have hζ1L : ζ1 ^ L = 1 := by
    rw [hζ1def, div_pow, ← map_pow, hπ1, AlgEquiv.commutes, div_self hϖ0ne]
  obtain ⟨σ0, hσ0, hprim⟩ := L_surj P A0 L ϖ0 π1 hA0 hL hϖ0 hϖ0' hπ1
  obtain ⟨b0, -, hb0⟩ := hJ σ0 hσ0
  have hζ1prim : IsPrimitiveRoot ζ1 L := by
    rw [hb0, mul_div_cancel_right₀ _ hπ1ne] at hprim
    have h1 : L ∣ orderOf ζ1 := hprim.eq_orderOf ▸ orderOf_pow_dvd b0
    have h2 : orderOf ζ1 ∣ L := orderOf_dvd_of_pow_eq_one hζ1L
    have h3 : orderOf ζ1 = L := Nat.dvd_antisymm h2 h1
    exact h3 ▸ IsPrimitiveRoot.orderOf ζ1

  obtain ⟨τ, hτ⟩ := ReciprocityTheory.Gal.exists_isFrob hA0
  have hσF : τ * γ * τ⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A0 := ReciprocityTheory.Gal.conj_mem_Ine hτ.1 hγ.1
  set η := (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 / π1 with hηdef
  have hη : η ^ L = 1 := by
    rw [hηdef, div_pow, ← map_pow, hπ1, AlgEquiv.commutes, div_self hϖ0ne]
  have hyη : (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 = η * π1 := by rw [hηdef, div_mul_cancel₀ _ hπ1ne]
  have hγη : γ η = η := ine_fix_root hA0 hL hγ.1 hη
  have hcalc : (τ * γ * τ⁻¹) π1 = ζ1 ^ q * π1 := by
    have e1 : (τ * γ * τ⁻¹) π1 = τ (γ ((τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1)) := rfl
    have e2 : γ ((τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1) = ζ1 * (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 := by
      rw [hyη, map_mul, hγη, hγπ1]; ring
    rw [e1, e2, map_mul, ReciprocityTheory.Gal.mul_inv_apply, frob_root hA0 hL hτ hζ1L]
  obtain ⟨b, hbφ, hbπ⟩ := hJ _ hσF
  have hφconj : φ (τ * γ * τ⁻¹) = φ γ := by
    rw [map_mul, map_mul, mul_comm (φ τ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [hcalc] at hbπ
  have hζq : ζ1 ^ q = ζ1 ^ b := mul_right_cancel₀ hπ1ne hbπ
  have hmod : q ≡ b [MOD L] := modEq_of_pow_eq hζ1prim hL0 hζq
  have hordγ : orderOf (φ γ) ∣ L := orderOf_dvd_of_pow_eq_one hγL
  have hγq : φ γ ^ q = φ γ ^ b := pow_eq_pow_iff_modEq.2 (hmod.of_dvd hordγ)
  have hγn : φ γ ^ n = 1 := by
    have h1 : φ γ ^ n * φ γ = φ γ := by
      rw [← pow_succ, show n + 1 = q by omega, hγq, ← hbφ, hφconj]
    exact mul_eq_right.1 h1

  set π0 := π1 ^ (m ^ N0) with hπ0def
  have hπ0 : π0 ^ n = algebraMap E Ω (ϖ0 : E) := by
    rw [hπ0def, ← pow_mul, mul_comm, ← hLdef]
    exact hπ1
  have hπ0ne : π0 ≠ 0 := pow_ne_zero _ hπ1ne
  set ζ0 := ζ1 ^ (m ^ N0) with hζ0def
  have hζ0prim : IsPrimitiveRoot ζ0 n := hζ1prim.pow (Nat.pos_of_ne_zero hL0) (by rw [hLdef, mul_comm])
  have hC : ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A0, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π0 = ζ0 ^ b * π0 := by
    intro σ hσ
    obtain ⟨b, h1, h2⟩ := hJ σ hσ
    refine ⟨b, h1, ?_⟩
    rw [hπ0def, map_pow, h2, hζ0def, mul_pow, ← pow_mul, ← pow_mul, mul_comm b]
  have hn1A : ¬ A0.valuation (n : Ω) < 1 := not_val_lt_one hA0 hq1
  have hordn : orderOf (φ γ) ∣ n := orderOf_dvd_of_pow_eq_one hγn
  have hK : ∀ (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (a : ℕ), Formalism.L2.NX.TameRep P e σ u →
      A0.valuation (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 → φ σ = φ γ ^ a := by
    intro σ u a hσ ha
    obtain ⟨g, hg, hgv⟩ := L_move P e σ u A0 ϖ0 π0 hA0 hϖ0 hϖ0' hπ0 hσ
    obtain ⟨b, hbφ, hbπ⟩ := hC _ hg
    have hφg : φ (g * σ * g⁻¹) = φ σ := by
      rw [map_mul, map_mul, mul_comm (φ g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [hbπ, mul_div_cancel_right₀ _ hπ0ne] at hgv
    have hab : ζ0 ^ a = ζ0 ^ b := by
      refine ReciprocityTheory.Gal.eq_of_pow_eq_one A0 hn1A ?_ ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, hζ0prim.pow_eq_one, one_pow]
      · rw [← pow_mul, mul_comm, pow_mul, hζ0prim.pow_eq_one, one_pow]
      · have e1 : ζ0 ^ a - ζ0 ^ b = (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) - (ζ0 ^ b - (algebraMap E Ω (u : E)) ^ e) := by
          ring
        rw [e1]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hgv)
    have hmod' : a ≡ b [MOD n] := modEq_of_pow_eq hζ0prim (ne_zero_of_not_mem hq1) hab
    rw [← hφg, hbφ]
    exact (pow_eq_pow_iff_modEq.2 (hmod'.of_dvd hordn)).symm
  have hγfix : γ ζ0 = ζ0 := ine_fix_root hA0 hq1 hγ.1 hζ0prim.pow_eq_one
  have hγpow : ∀ a : ℕ, (γ ^ a) π0 = ζ0 ^ a * π0 := by
    have hγπ0 : γ π0 = ζ0 * π0 := by
      rw [hπ0def, map_pow, hγπ1, mul_pow, hζ0def]
    intro a
    induction a with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hγπ0, map_mul, ih,
        ine_fix_root hA0 hq1 (pow_mem hγ.1 k) hζ0prim.pow_eq_one, pow_succ]
      ring
  have hX : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ a : ℕ, A0.valuation (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 ∧
      Formalism.L2.NX.TameRep P e (γ ^ a) u := by
    intro u hu
    obtain ⟨a, ha⟩ := L_teich P A0 ζ0 hA0 hζ0prim u e hu
    refine ⟨a, ha, A0, hA0, pow_mem hγ.1 a, ϖ0, π0, hϖ0, hϖ0', hπ0, ?_⟩
    rw [hγpow, mul_div_cancel_right₀ _ hπ0ne]
    exact ha
  have hval : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∀ a : ℕ,
      A0.valuation (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 → Formalism.L2.NX.tameVal φ P e u = φ γ ^ a := by
    intro u hu a ha
    obtain ⟨a', -, hrep⟩ := hX u hu
    have hex : ∃ σ, Formalism.L2.NX.TameRep P e σ u := ⟨_, hrep⟩
    rw [Formalism.L2.NX.tameVal, dif_pos hex]
    exact hK _ u a hex.choose_spec ha
  have hU : ∀ u : 𝓞 E, u ∉ P.asIdeal → A0.valuation ((algebraMap E Ω (u : E)) ^ e) = 1 := by
    intro u hu
    rw [map_zpow₀, L_vone P A0 hA0 u hu, one_zpow]
  have hζa : ∀ a : ℕ, A0.valuation (ζ0 ^ a) = 1 := fun a =>
    ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A0 (ne_zero_of_not_mem hq1)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ0prim.pow_eq_one, one_pow])
  refine ⟨fun u u' hu hu' => ?_, fun u u' hu huu' => ?_⟩
  · obtain ⟨a, ha, -⟩ := hX u hu
    obtain ⟨a', ha', -⟩ := hX u' hu'
    have huu : u * u' ∉ P.asIdeal := P.isPrime.mul_notMem hu hu'
    rw [hval u hu a ha, hval u' hu' a' ha', hval (u * u') huu (a + a'), pow_add]
    have e1 : ζ0 ^ (a + a') - (algebraMap E Ω ((u * u' : 𝓞 E) : E)) ^ e =
        ζ0 ^ a * (ζ0 ^ a' - (algebraMap E Ω (u' : E)) ^ e) +
          (algebraMap E Ω (u' : E)) ^ e * (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) := by
      have hc : ((u * u' : 𝓞 E) : E) = (u : E) * (u' : E) := by simp
      rw [hc, map_mul, mul_zpow, pow_add]
      ring
    rw [e1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, hζa, one_mul]; exact ha'
    · rw [map_mul, hU u' hu', one_mul]; exact ha
  · have hu' : u' ∉ P.asIdeal := by
      intro h
      apply hu
      have : u = (u - u') + u' := by ring
      rw [this]
      exact add_mem huu' h
    obtain ⟨a, ha, -⟩ := hX u hu
    rw [hval u hu a ha, hval u' hu' a ?_]
    have hclose : A0.valuation (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) < 1 := by
      have h0 := (hA0 (u - u')).2 huu'
      simpa [map_sub] using h0
    have h2 := zpow_close (L_vone P A0 hA0 u' hu') hclose e
    have e1 : ζ0 ^ a - (algebraMap E Ω (u' : E)) ^ e =
        (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) + ((algebraMap E Ω (u : E)) ^ e - (algebraMap E Ω (u' : E)) ^ e) := by
      ring
    rw [e1]
    exact Valuation.map_add_lt _ ha h2

end GlobalTheory.TameValChar
end
end
