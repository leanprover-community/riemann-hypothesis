import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalKummerNormsEqTopOfPow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMonStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCountPlacesNotLocalPowerLeIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupLocalKummerNormsNeTop
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnitStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangeProperties

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isField_tensor_of_coprime (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A]
    [Algebra F B] (h : Nat.Coprime (Module.finrank F A) (Module.finrank F B)) :
    IsField (A ⊗[F] B) := by
  refine IntermediateField.LinearDisjoint.isField_of_forall F A B ?_
  intro K _ _ fa fb
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  have ha : Module.finrank F A = Module.finrank F fa.fieldRange :=
    (AlgEquiv.ofInjectiveField fa).toLinearEquiv.finrank_eq
  have hb : Module.finrank F B = Module.finrank F fb.fieldRange :=
    (AlgEquiv.ofInjectiveField fb).toLinearEquiv.finrank_eq
  rwa [← ha, ← hb]

theorem coprime_finrank_cyclotomic (p : ℕ) (hp : p.Prime) (F A : Type) [Field F] [Field A]
    [Algebra F A] [IsCyclotomicExtension {p} F A] : Nat.Coprime (Module.finrank F A) p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Module.Finite F A := IsCyclotomicExtension.finite {p} F A
  have hζ := IsCyclotomicExtension.zeta_spec p F A
  have hdvd : minpoly F (IsCyclotomicExtension.zeta p F A) ∣ cyclotomic p F := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    haveI : NeZero (p : A) := hζ.neZero'
    exact (isRoot_cyclotomic_iff.mpr hζ)
  have hle := natDegree_le_of_dvd hdvd (cyclotomic_ne_zero p F)
  rw [natDegree_cyclotomic, Nat.totient_prime hp] at hle
  have hfr : Module.finrank F A = (minpoly F (IsCyclotomicExtension.zeta p F A)).natDegree := by
    rw [(hζ.powerBasis F).finrank, ← (hζ.powerBasis F).natDegree_minpoly,
      IsPrimitiveRoot.powerBasis_gen]
  have hpos : 0 < Module.finrank F A := Module.finrank_pos
  have h1 := hp.pos
  exact (Nat.coprime_of_lt_prime hpos.ne' (by omega) hp).symm

theorem exists_pushout_primitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → ∃ (F' E' : Type) (_ : Field F') (_ : NumberField F') (_ : Field E') (_ : NumberField E') (_ : Algebra F F') (_ : Algebra F' E') (_ : Algebra E E') (_ : Algebra F E') (_ : IsScalarTower F F' E') (_ : IsScalarTower F E E') (ζ : F'), Algebra.IsPushout F F' E E' ∧ IsTotallyComplex F' ∧ IsGalois F' E' ∧ IsPrimitiveRoot ζ p ∧ Module.finrank F' E' = p ∧ Nat.Coprime (Module.finrank F F') p := by
  intro p F E _ _ _ _ _ _ hp h2 hdeg
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let A : Type := CyclotomicField p F
  haveI : IsCyclotomicExtension {p} F A := CyclotomicField.isCyclotomicExtension p F
  haveI : NumberField A := IsCyclotomicExtension.numberField {p} F A
  have hco := coprime_finrank_cyclotomic p hp F A
  have hf : IsField (A ⊗[F] E) := isField_tensor_of_coprime F A E (by rwa [hdeg])
  letI : Field (A ⊗[F] E) := hf.toField
  letI : Algebra E (A ⊗[F] E) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Module.Finite A (A ⊗[F] E) := inferInstance
  haveI : NumberField (A ⊗[F] E) := NumberField.of_module_finite A (A ⊗[F] E)
  have hζ := IsCyclotomicExtension.zeta_spec p F A
  have hr : Module.finrank A (A ⊗[F] E) = p := by
    rw [Module.finrank_baseChange, hdeg]
  have h3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  refine ⟨A, A ⊗[F] E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsCyclotomicExtension.zeta p F A, inferInstance, ?_, ?_, hζ, hr, hco⟩
  · exact NumberField.nrRealPlaces_eq_zero_iff.mp
      (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt h3 hζ)
  · apply IsGalois.of_card_aut_eq_finrank
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
    · rw [Module.finrank_baseChange, ← IsGalois.card_aut_eq_finrank]
      refine Nat.card_le_card_of_injective
        (fun g : E ≃ₐ[F] E => (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) g)) ?_
      intro g h hgh
      ext x
      have := DFunLike.congr_fun hgh ((1 : A) ⊗ₜ[F] x)
      simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul] at this
      exact (algebraMap E (A ⊗[F] E)).injective this

end GlobalTheory.CNorm
end

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_eq_prime_of_generated {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (E K : Subgroup G) (x : G) (hxE : x ∈ E) (hxK : x ∉ K) (hxp : x ^ p ∈ K)
    (hgen : ∀ y ∈ E, ∃ k : ℕ, y / x ^ k ∈ K) : K.relIndex E = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c : E ⧸ K.subgroupOf E := QuotientGroup.mk (⟨x, hxE⟩ : E) with hc
  have ho : orderOf c = p := by
    apply orderOf_eq_prime
    · rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hxp
    · rw [hc, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxK
  have hall : ∀ y : E ⧸ K.subgroupOf E, y ∈ Submonoid.powers c := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hgen y y.2
    refine ⟨k, ?_⟩
    simp only [hc]
    rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa using hk
  rw [Subgroup.relIndex, Subgroup.index, ← ho]
  exact (orderOf_eq_card_of_forall_mem_powers hall).symm

theorem exists_independent_prime_relIndex_subgroups (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι]
    (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ) (hp : p.Prime)
    (hH : H.relIndex U = p ^ m) (h1 : ∀ i, good i → U ⊓ H ≤ K i)
    (h2 : ∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i)
    (h2' : ∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i)
    (h3 : ∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) (k : ℕ) (hk : k ≤ m) :
    ∃ T : Finset ι, T.card = k ∧ (∀ i ∈ T, good i) ∧
      (∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j) ∧
      ∃ D : Subgroup G, (∀ x, x ∈ D ↔ ∀ i ∈ T, x ∈ K i) ∧ D.relIndex U = p ^ k := by
  induction k with
  | zero =>
    refine ⟨∅, rfl, by simp, by simp, ⊤, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hT, hg, hA, D, hD, hDi⟩ := ih (by omega)
    have hx : ∃ x ∈ U, x ∈ D ∧ x ∉ H := by
      by_contra hcon
      push Not at hcon
      have heq : D ⊓ U = H ⊓ U := by
        ext x
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨a, b⟩
          exact ⟨hcon x b a, b⟩
        · rintro ⟨a, b⟩
          exact ⟨(hD x).2 fun i hi => h1 i (hg i hi) ⟨b, a⟩, b⟩
      have h4 : D.relIndex U = H.relIndex U := by
        rw [← Subgroup.inf_relIndex_right D U, heq, Subgroup.inf_relIndex_right]
      rw [hDi, hH] at h4
      have := Nat.pow_right_injective hp.two_le h4
      omega
    obtain ⟨x, hxU, hxD, hxH⟩ := hx
    obtain ⟨j, hj, hxj⟩ := h3 x hxU hxH
    have hjT : j ∉ T := fun h => hxj ((hD x).1 hxD j h)
    refine ⟨insert j T, by rw [Finset.card_insert_of_notMem hjT, hT], ?_, ?_, K j ⊓ D, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hj
      · exact hg i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨x, hxU, hxj, fun l hl hli => ?_⟩
        rcases Finset.mem_insert.1 hl with rfl | hl
        · exact absurd rfl hli
        · exact (hD x).1 hxD l hl
      · obtain ⟨u, huU, hui, hu⟩ := hA i hi
        obtain ⟨n, hn⟩ := h2' j hj x hxU hxj u huU
        refine ⟨u / x ^ n, U.div_mem huU (U.pow_mem hxU n), ?_, fun l hl hli => ?_⟩
        · intro h
          apply hui
          have := (K i).mul_mem h ((K i).pow_mem ((hD x).1 hxD i hi) n)
          simpa using this
        · rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hn
          · exact (K l).div_mem (hu l hl hli) ((K l).pow_mem ((hD x).1 hxD l hl) n)
    · intro y
      simp only [Subgroup.mem_inf, hD, Finset.forall_mem_insert]
    · have h5 : (K j).relIndex (D ⊓ U) = p :=
        relIndex_eq_prime_of_generated hp (D ⊓ U) (K j) x ⟨hxD, hxU⟩ hxj (h2 j hj x hxU)
          (fun y hy => h2' j hj x hxU hxj y hy.2)
      rw [← Subgroup.relIndex_inf_mul_relIndex, h5, hDi, pow_succ, mul_comm]

theorem exists_indep_prime_index : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι] (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ), p.Prime → H.relIndex U = p ^ m → (∀ i, good i → U ⊓ H ≤ K i) → (∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i) → (∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i) → (∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) → ∃ T : Finset ι, T.card = m ∧ (∀ i ∈ T, good i) ∧ ∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j := by
  intro p G ι _ _ U H K good m hp hH h1 h2 h2' h3
  obtain ⟨T, a, b, c, -⟩ :=
    exists_independent_prime_relIndex_subgroups p G ι U H K good m hp hH h1 h2 h2' h3 m le_rfl
  exact ⟨T, a, b, c⟩

end GlobalTheory.CNorm
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_not_mem_not_pow_completion :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → u ≠ 0 → (∀ r : F, r ^ p ≠ u) → ∃ v, v ∉ S₀ ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  classical
  intro p F _ _ _ ζ u S₀ hp hζ hu hns
  by_contra hcon
  push Not at hcon
  have hle : ∀ S, finNorm p F u S₀ ≤ finNorm p F u S := by
    intro S x hx
    rw [finNorm] at hx ⊢
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro v _
    by_cases hv : v ∈ S₀
    · exact hx v hv
    · haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      obtain ⟨r, hr⟩ := hcon v hv
      rw [GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F _ _ u r hp.pos hu hr]
      exact Subgroup.mem_top x
  have hidx := (GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ u S₀ hp hζ).1
  haveI : (finNorm p F u S₀).FiniteIndex := ⟨hidx⟩
  haveI : Fintype (Fˣ ⧸ finNorm p F u S₀) := Fintype.ofFinite _
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F
    (insert (Units.mk0 u hu)
      (Finset.univ.image (fun q : Fˣ ⧸ finNorm p F u S₀ => q.out))) S₀
  obtain ⟨S, hS, hadm⟩ := (GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).1 S₁
  have hX := hS₁ S hS
  refine GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ (Units.mk0 u hu) S hp hζ hadm
    (hX _ (Finset.mem_insert_self _ _)) hns ?_
  rw [eq_top_iff]
  intro x _
  have hy : (QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out ∈ sUnits F S :=
    hX _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz : ((QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out)⁻¹ * x ∈ finNorm p F u S₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have hx : x = (QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out *
      (((QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hy (hle S hz)

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_not_pow_adicCompletion : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → u ≠ 0 → (∀ r : F, r ^ p ≠ u) → ∃ v, v ∉ S₀ ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  atlas_forward_decl GlobalTheory.CNorm.exists_not_mem_not_pow_completion
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_place_pow_and_not_pow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → δ ≠ 0 → u ≠ 0 → (∀ r : F, r ^ p ≠ δ) → (∀ (k : ℕ) (r : F), u ≠ δ ^ k * r ^ p) → ∃ v, v ∉ S₀ ∧ (∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) δ) ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  classical
  intro p F _ _ _ ζ δ u S₀ hp hζ hδ hu hδs huδ
  obtain ⟨E, _, _, θ, σ, hq⟩ := exists_isKum p F ζ δ hp hζ hδs
  obtain ⟨hfd, -, -, -, -, hpow, -⟩ := GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p F E ζ δ θ σ hq
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  have huE : ∀ y : E, y ^ p ≠ algebraMap F E u := by
    intro y h
    obtain ⟨k, r, hr⟩ := hpow u y h
    exact huδ k r hr
  have h2 : (p : F) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨S, hS, hSu⟩ := exists_superset_mem_sUnits F
    {Units.mk0 (p : F) h2, Units.mk0 δ hδ, Units.mk0 u hu} S₀
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.exists_place_not_pow_adicCompletion p E (algebraMap F E ζ) (algebraMap F E u) SE hp
    (hζ.map_of_injective (algebraMap F E).injective) (by simpa using hu) huE
  obtain ⟨φ, hφ⟩ := exists_ringHom_adicCompletion_under F E w
  have hv : w.under (𝓞 F) ∉ S := fun h => hw ((hSE w).2 h)
  have hval : ∀ x : F, Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x)
      = (w.under (𝓞 F)).valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ x
  have hv2 : (w.under (𝓞 F)).valuation F (p : F) = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 (p : F) h2) (by simp)) _ hv
  have hvδ : (w.under (𝓞 F)).valuation F δ = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 δ hδ) (by simp)) _ hv
  have hvu : (w.under (𝓞 F)).valuation F u = 1 :=
    (mem_sUnits F S _).1 (hSu S subset_rfl (Units.mk0 u hu) (by simp)) _ hv
  have hunsq : ∀ r : (w.under (𝓞 F)).adicCompletion F,
      r ^ p ≠ algebraMap F ((w.under (𝓞 F)).adicCompletion F) u := by
    intro r h
    apply hwu (φ r)
    rw [← hφ, ← h, map_pow]
  refine ⟨w.under (𝓞 F), fun h => hv (hS h), ?_, hunsq⟩
  by_contra hδn
  push Not at hδn
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_unit p F (w.under (𝓞 F)) _ _ hp hv2
    ((hval δ).trans hvδ) ((hval u).trans hvu) hδn
  apply hwu (algebraMap E (w.adicCompletion E) θ ^ k * φ r)
  rw [← hφ, hr, map_mul, map_pow, map_pow, hφ, ← hq.pow, map_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm k p]

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_pow_and_not_pow' : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → δ ≠ 0 → u ≠ 0 → (∀ r : F, r ^ p ≠ δ) → (∀ (k : ℕ) (r : F), u ≠ δ ^ k * r ^ p) → ∃ v, v ∉ S₀ ∧ (∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) δ) ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  atlas_forward_decl GlobalTheory.CNorm.exists_place_pow_and_not_pow
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_sup_zpowers_chooseT (p : ℕ) {G : Type} [CommGroup G] (Q : Subgroup G) (d : G)
    (hp : p.Prime) (hd : d ^ p ∈ Q) (hn : d ∉ Q) :
    Q.relIndex (Q ⊔ Subgroup.zpowers d) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.relIndex_sup_left]
  have h := Subgroup.relIndex_ker (Subgroup.zpowers d) (QuotientGroup.mk' Q)
  rw [QuotientGroup.ker_mk', MonoidHom.map_zpowers, Nat.card_zpowers] at h
  rw [h]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hd
  · exact fun e => hn ((QuotientGroup.eq_one_iff _).1 e)

theorem mem_pows_sUnits_chooseT (p : ℕ) (hp : p ≠ 0) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) (hx : x ∈ sUnits F S) (r : F)
    (hr : r ^ p = (x : F)) : x ∈ pows p (sUnits F S) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hr, zero_pow hp])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_sUnits]
    intro v hv
    have h := (mem_sUnits F S x).1 hx v hv
    rw [← hr, map_pow] at h
    exact (pow_eq_one_iff_of_nonneg zero_le hp).1 h
  · ext
    simp [hr]

theorem exists_auxiliary_places_prime : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, ∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) ∧ ∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns
  classical
  have hQU : pows p (sUnits F S) ≤ sUnits F S := by
    rintro _ ⟨y, hy, rfl⟩
    exact (sUnits F S).pow_mem hy p
  have hdd : δ ^ p ∈ pows p (sUnits F S) := ⟨δ, hδ, rfl⟩
  have hdn : δ ∉ pows p (sUnits F S) := by
    rintro ⟨y, -, hy⟩
    exact hns (y : F) (by rw [← hy]; simp)
  have hHU : pows p (sUnits F S) ⊔ Subgroup.zpowers δ ≤ sUnits F S :=
    sup_le hQU ((Subgroup.zpowers_le).2 hδ)
  have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = S.card + Fintype.card (InfinitePlace F) :=
    ⟨S.card + Fintype.card (InfinitePlace F) - 1, by omega⟩
  have hidx : (pows p (sUnits F S) ⊔ Subgroup.zpowers δ).relIndex (sUnits F S) = p ^ m := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hHU
    have h2 : (pows p (sUnits F S)).relIndex (sUnits F S) = _ :=
      (pTor_pIdx_sUnits p F ζ S hp hζ).2
    rw [relIndex_sup_zpowers_chooseT p _ _ hp hdd hdn, h2, ← hm, pow_succ'] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F),
      Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := fun v x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hpw : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ),
      x ^ p ∈ powSub p (algebraMap F (v.adicCompletion F)) := fun v x =>
    ⟨algebraMap F (v.adicCompletion F) x, by rw [Units.val_pow_eq_pow_val, map_pow]⟩
  obtain ⟨T, hT, hgood, hA⟩ := exists_indep_prime_index p Fˣ (HeightOneSpectrum (𝓞 F)) (sUnits F S)
    (pows p (sUnits F S) ⊔ Subgroup.zpowers δ)
    (fun v => powSub p (algebraMap F (v.adicCompletion F)))
    (fun v => v ∉ S ∧ ∃ r : v.adicCompletion F,
      r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) m hp hidx
    (by
      rintro v ⟨-, hv⟩
      refine le_trans inf_le_right (sup_le ?_ ((Subgroup.zpowers_le).2 hv))
      rintro _ ⟨y, -, rfl⟩
      exact hpw v y)
    (fun v _ x _ => hpw v x)
    (by
      rintro v ⟨hv, -⟩ x hx hx' y hy
      obtain ⟨k, r, hr⟩ := GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit p F v (algebraMap F (v.adicCompletion F) x)
        (algebraMap F (v.adicCompletion F) y) hp (hS.2 v hv)
        (by rw [hval]; exact (mem_sUnits F S x).1 hx v hv)
        (by rw [hval]; exact (mem_sUnits F S y).1 hy v hv)
        (fun r hr => hx' ⟨r, hr⟩)
      refine ⟨k, r, ?_⟩
      have hx0 : algebraMap F (v.adicCompletion F) x ≠ 0 := by simp
      rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, map_div₀, map_pow, hr]
      field_simp)
    (by
      intro x hx hxH
      obtain ⟨v, h1, h2, h3⟩ := GlobalTheory.T.exists_place_pow_and_not_pow' p F ζ δ x S hp hζ δ.ne_zero x.ne_zero hns
        (fun k r h => hxH (by
          have h4 : x / δ ^ k ∈ pows p (sUnits F S) := by
            refine mem_pows_sUnits_chooseT p hp.ne_zero F S _
              ((sUnits F S).div_mem hx ((sUnits F S).pow_mem hδ k)) r ?_
            have hδ0 := δ.ne_zero
            rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, h]
            field_simp
          have h5 := Subgroup.mul_mem_sup h4 (Subgroup.pow_mem _ (Subgroup.mem_zpowers δ) k)
          rwa [div_mul_cancel] at h5))
      exact ⟨v, ⟨h1, h2⟩, fun ⟨r, hr⟩ => h3 r hr⟩)
  refine ⟨T, ?_, by rw [hT, hm], fun v hv => (hgood v hv).2, hA⟩
  rw [Finset.disjoint_right]
  exact fun v hv => (hgood v hv).1

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_places_with_pth_roots_and_separating_units : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, ∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) ∧ ∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
  atlas_forward_decl GlobalTheory.CNorm.exists_auxiliary_places_prime
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_of_mem_sUnits_union_of_mem_finPow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
      [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))),
      p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ →
      ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  intro p F _ _ _ _ ζ S T hp hζ hS hT y hy hyS
  by_contra hne
  have hne' : ∀ r : F, r ^ p ≠ (y : F) := fun r hr => hne ⟨r, hr⟩
  have hadm : AdmP p F (S ∪ T) :=
    (GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).2 S (S ∪ T) Finset.subset_union_left hS
  refine GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ y (S ∪ T) hp hζ hadm hy hne' ?_
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  unfold finNorm
  refine le_iInf₂ fun v hv => ?_
  rcases Finset.mem_union.1 hv with hv | hv
  · have h1 : y ∈ powSub p (algebraMap F (v.adicCompletion F)) :=
      (iInf₂_le (f := fun w (_ : w ∈ S) => powSub p (algebraMap F (w.adicCompletion F))) v hv) hyS
    obtain ⟨r, hr⟩ := h1
    have : CharZero (v.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
    rw [GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F (v.adicCompletion F) _ (y : F) r hp.pos y.ne_zero hr]
    exact le_top
  · exact le_trans
      (iInf₂_le (f := fun w (_ : w ∈ T) => powSub p (algebraMap F (w.adicCompletion F))) v hv)
      ((GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1 F (v.adicCompletion F) _ (y : F))

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_of_sUnit_localPower_at_places : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ → ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  atlas_forward_decl GlobalTheory.CNorm.pow_of_mem_sUnits_union_of_mem_finPow
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_union_sup_finPow_eq_top :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  intro p F _ _ _ S T hp hS hST hA
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS.1
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  have key : ∀ v ∈ T, ∃ w ∈ sUnits F S,
      w⁻¹ * (a * x) ∈ powSub p (algebraMap F (v.adicCompletion F)) ∧
        ∀ v' ∈ T, v' ≠ v → w ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
    intro v hv
    obtain ⟨u, hu, hnu, hu'⟩ := hA v hv
    obtain ⟨k, r, hr⟩ := GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit p F v (algebraMap F (v.adicCompletion F) (u : F))
      (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)) hp (hS.2 v (hTS v hv))
      (by rw [hval]; exact (mem_sUnits F S u).1 hu v (hTS v hv))
      (by rw [hval]; exact hy v hv) (fun r h => hnu ⟨r, h⟩)
    refine ⟨u ^ k, pow_mem hu k, ⟨r, ?_⟩, fun v' hv' hne => pow_mem (hu' v' hv' hne) k⟩
    have hu0 : algebraMap F (v.adicCompletion F) (u : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, hr, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
      map_pow, inv_mul_cancel_left₀ (pow_ne_zero k hu0)]
  choose! w hwS hw1 hw2 using key
  have huU : ∏ v ∈ T, w v ∈ sUnits F (S ∪ T) := by
    refine prod_mem fun t ht => ?_
    rw [mem_sUnits]
    intro v hv
    exact (mem_sUnits F S _).1 (hwS t ht) v fun h => hv (Finset.mem_union_left _ h)
  have hsq : (∏ v ∈ T, w v)⁻¹ * (a * x) ∈ finPow p F T := by
    simp only [finPow, Subgroup.mem_iInf]
    intro v hv
    rw [← Finset.mul_prod_erase T w hv, mul_inv, mul_right_comm]
    refine mul_mem (hw1 v hv) (inv_mem (prod_mem fun t ht => ?_))
    exact hw2 t (Finset.mem_of_mem_erase ht) v hv (Finset.ne_of_mem_erase ht).symm
  have hx : x = ((∏ v ∈ T, w v) * a⁻¹) * ((∏ v ∈ T, w v)⁻¹ * (a * x)) := by
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, inv_mul_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup (mul_mem huU (inv_mem haU)) hsq

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sUnits_union_sup_powers_eq_top_at_places : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  atlas_forward_decl GlobalTheory.CNorm.sUnits_union_sup_finPow_eq_top
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem index_eq_relIndex_mul_index_sup_normThm {G : Type} [CommGroup G] (U W : Subgroup G) :
    W.index = W.relIndex U * (U ⊔ W).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]

theorem inf_le_of_index_count_normThm {G : Type} [CommGroup G] (p : ℕ) (hp : 0 < p)
    (U W D N : Subgroup G) (s k t : ℕ)
    (hWD : W ≤ D) (hND : N ≤ D) (hk : k + 1 = 2 * s) (hW0 : W.index ≠ 0)
    (hW : W.index ≤ p ^ (2 * s)) (hWU : W.relIndex U = p ^ k) (hD : p ^ t ≤ D.index)
    (hN0 : N.relIndex U ≠ 0) (hN : p * N.relIndex U ≤ p ^ t) : D ⊓ U ≤ N := by
  have e1 := index_eq_relIndex_mul_index_sup_normThm U W
  have e2 := index_eq_relIndex_mul_index_sup_normThm U D
  have h4 : p ^ (2 * s) = p ^ k * p := by
    rw [← pow_succ, hk]
  have hUW0 : (U ⊔ W).index ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hW0 e1
  have hUW : (U ⊔ W).index ≤ p := by
    rw [e1, hWU, h4] at hW
    exact Nat.le_of_mul_le_mul_left hW (by positivity)
  have hUD : (U ⊔ D).index ≤ p :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hUW0)
      (Subgroup.index_dvd_of_le (sup_le_sup_left hWD U))) hUW
  have h3 : N.relIndex U ≤ D.relIndex U := by
    have : p * N.relIndex U ≤ p * D.relIndex U := by
      calc p * N.relIndex U ≤ D.relIndex U * (U ⊔ D).index := by
            rw [← e2]; exact hN.trans hD
        _ ≤ D.relIndex U * p := Nat.mul_le_mul_left _ hUD
        _ = p * D.relIndex U := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hp
  have e3 : N.relIndex (D ⊓ U) * D.relIndex U = N.relIndex U := by
    have := Subgroup.relIndex_inf_mul_relIndex N D U
    rwa [inf_eq_left.mpr hND] at this
  have hD0 : D.relIndex U ≠ 0 := by
    intro h; rw [h, mul_zero] at e3; exact hN0 e3.symm
  have hm0 : N.relIndex (D ⊓ U) ≠ 0 := by
    intro h; rw [h, zero_mul] at e3; exact hN0 e3.symm
  have hm : N.relIndex (D ⊓ U) ≤ 1 := by
    rw [← e3] at h3
    have : N.relIndex (D ⊓ U) * D.relIndex U ≤ 1 * D.relIndex U := by rwa [one_mul]
    exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hD0)
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem pows_le_finPow_normThm (p : ℕ) (F : Type) [Field F] [NumberField F] (U : Subgroup Fˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : pows p U ≤ finPow p F S := by
  rintro _ ⟨y, -, rfl⟩
  have h : ∀ {L : Type} [Field L] (φ : F →+* L), powMonoidHom p y ∈ powSub p φ := by
    intro L _ φ
    exact ⟨φ y, by simp⟩
  exact Subgroup.mem_iInf.mpr fun _ => Subgroup.mem_iInf.mpr fun _ => h _

theorem mem_pows_sUnits_normThm (p : ℕ) (hp : 0 < p) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Fˣ) (hy : y ∈ sUnits F S)
    (h : ∃ r : F, r ^ p = (y : F)) : y ∈ pows p (sUnits F S) := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hr, zero_pow hp.ne'])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · intro v hv
    have h1 := hy v hv
    have h2 : v.valuation F r ^ p = 1 := by
      rw [← map_pow, hr]; exact h1
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne').mp h2
  · ext
    simp [hr]

theorem sUnit_mem_kNorm_of_mem_finNorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∀ x ∈ sUnits F S, x ∈ finNorm p F δ S → x ∈ kNorm p (RingHom.id F) (δ : F) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns x hx hxl
  classical
  have hp0 := hp.pos
  obtain ⟨T, hST, hcard, hsq, hA⟩ := GlobalTheory.T.exists_places_with_pth_roots_and_separating_units p F ζ δ S hp hζ hS hδ hns
  have hsurj := GlobalTheory.T.sUnits_union_sup_powers_eq_top_at_places p F S T hp hS hST hA
  have hinj := GlobalTheory.T.pow_of_sUnit_localPower_at_places p F ζ S T hp hζ hS hsurj
  have hmono : sUnits F S ≤ sUnits F (S ∪ T) := fun y hy v hv =>
    hy v (fun h => hv (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inl h))
  have hS' : AdmP p F (S ∪ T) :=
    (exists_admissiblePlaces_superset_and_mono p F hp0).2 S (S ∪ T) Finset.subset_union_left hS
  obtain ⟨hN0, hN⟩ := GlobalTheory.T.first_inequality_sUnits_prime_degree p F ζ δ (S ∪ T) hp hζ hS' (hmono hδ) hns
  have ht : tNon p F δ (S ∪ T) = tNon p F δ S := by
    unfold tNon
    congr 1
    ext v
    simp only [Finset.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h, h'⟩
      · obtain ⟨r, hr⟩ := hsq v h
        exact absurd hr (h' r)
    · rintro ⟨h, h'⟩
      exact ⟨Or.inl h, h'⟩
  rw [ht] at hN
  obtain ⟨-, hD⟩ := GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ δ S hp hζ
  obtain ⟨hW0, hW⟩ := GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp0
  have hU := (pTor_pIdx_sUnits p F ζ (S ∪ T) hp hζ).2
  unfold pIdx at hU
  have hinf : finPow p F S ⊓ sUnits F (S ∪ T) = pows p (sUnits F (S ∪ T)) ⊓ sUnits F (S ∪ T) := by
    apply le_antisymm
    · rintro y ⟨h1, h2⟩
      exact ⟨mem_pows_sUnits_normThm p hp0 F _ y h2 (hinj y h2 h1), h2⟩
    · exact inf_le_inf_right _ (pows_le_finPow_normThm p F _ S)
  have hWU : (finPow p F S).relIndex (sUnits F (S ∪ T)) =
      p ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right, hU]
  obtain ⟨k1, k2⟩ := GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp0
  have hWD : finPow p F S ≤ finNorm p F δ S := iInf₂_mono fun _ _ => k1 _ _ _ _
  have hND : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S :=
    le_iInf₂ fun _ _ => k2 _ _ _ _
  refine inf_le_of_index_count_normThm p hp0 (sUnits F (S ∪ T)) (finPow p F S) (finNorm p F δ S)
    _ _ _ _ hWD hND ?_ hW0 hW hWU hD hN0 hN ⟨hxl, hmono hx⟩
  rw [Finset.card_union_of_disjoint hST]
  omega

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sUnit_mem_kummerNorms_of_local_norms : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∀ x ∈ sUnits F S, x ∈ finNorm p F δ S → x ∈ kNorm p (RingHom.id F) (δ : F) := by
  atlas_forward_decl GlobalTheory.CNorm.sUnit_mem_kNorm_of_mem_finNorm
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isUnit_of_norm_ne_zero {L A : Type} [Field L] [CommRing A] [Algebra L A]
    [Module.Finite L A] (y : A) (h : Algebra.norm L y ≠ 0) : IsUnit y := by
  have h1 : IsUnit (Algebra.lmul L A y) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (by rwa [Algebra.norm_apply] at h)
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp h1).surjective 1
  exact IsUnit.of_mul_eq_one z (by simpa using hz)

theorem IsKum.nonempty_tensor_equiv {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E]
    {ζ δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (L : Type) [Field L] [Algebra F L] :
    Nonempty ((L ⊗[F] E) ≃ₐ[L] AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) := by
  have hp := h.prime
  have hmin := h.minpoly_eq
  have hint : IsIntegral F θ :=
    ⟨X ^ p - C δ, monic_X_pow_sub_C δ hp.ne_zero, by simp [h.pow]⟩
  let pb : PowerBasis F E := PowerBasis.ofAdjoinEqTop hint h.gen
  have hgen : pb.gen = θ := PowerBasis.ofAdjoinEqTop_gen hint h.gen
  set g : L[X] := X ^ p - C (algebraMap F L δ) with hg
  have hroot : AdjoinRoot.root g ^ p = algebraMap F (AdjoinRoot g) δ := by
    have := AdjoinRoot.eval₂_root g
    rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    rw [IsScalarTower.algebraMap_apply F L (AdjoinRoot g)]
    exact this
  let ψ : E →ₐ[F] AdjoinRoot g := pb.lift (AdjoinRoot.root g) (by
    rw [hgen, hmin]; simp [hroot])
  have hψ : ψ θ = AdjoinRoot.root g := (congrArg _ hgen.symm).trans (pb.lift_gen _ _)
  let a : (L ⊗[F] E) →ₐ[L] AdjoinRoot g :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ψ (fun _ _ => Commute.all _ _)
  let b : AdjoinRoot g →ₐ[L] (L ⊗[F] E) :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId L _) ((1 : L) ⊗ₜ[F] θ) (by
      rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, Algebra.TensorProduct.tmul_pow,
        one_pow, h.pow]
      change _ = algebraMap L (L ⊗[F] E) (algebraMap F L δ)
      rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',])
  have hb : b (AdjoinRoot.root g) = (1 : L) ⊗ₜ[F] θ := AdjoinRoot.liftAlgHom_root ..
  have ha : a ((1 : L) ⊗ₜ[F] θ) = AdjoinRoot.root g := by
    simp [a, hψ]
  refine ⟨AlgEquiv.ofAlgHom a b ?_ ?_⟩
  · apply AdjoinRoot.algHom_ext
    simp [ha, hb]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply pb.algHom_ext
      rw [hgen]
      simp [ha, hb]

theorem mem_kNorm_of_tNorm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  intro p F E L _ _ _ _ _ _ ζ δ θ σ h x ⟨y, hy⟩
  obtain ⟨e⟩ := h.nonempty_tensor_equiv L
  have : Module.Finite L (AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) :=
    (AdjoinRoot.powerBasis' (monic_X_pow_sub_C _ h.prime.ne_zero)).finite
  have hn : Algebra.norm L (e y) = algebraMap F L x := by
    rw [Algebra.norm_eq_of_algEquiv, hy]
  have hu : IsUnit (e y) := isUnit_of_norm_ne_zero _ (by
    rw [hn]; exact (_root_.map_ne_zero _).mpr x.ne_zero)
  rw [mem_kNorm]
  exact ⟨hu.unit, hn⟩

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unitsLocalKummerNorms_of_baseChange_norm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  atlas_forward_decl GlobalTheory.CNorm.mem_kNorm_of_tNorm
end

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [Field E] [Algebra F E]
    [IsGalois F E] (ζ : F) (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hr : Module.finrank F E = p) :
    ∃ (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (hr ▸ hp.pos)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[F] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hr])
  have hK : (primitiveRoots (Module.finrank F E) F).Nonempty :=
    ⟨ζ, by rw [hr, mem_primitiveRoots hp.pos]; exact hζ⟩
  obtain ⟨θ, ⟨δ, hδ⟩, hθ⟩ := exists_root_adjoin_eq_top_of_isCyclic F E hK
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hδ.symm hθ
  rw [hr] at hirr hδ
  have hmin : (X ^ p - C δ : F[X]) = minpoly F θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hδ]) (monic_X_pow_sub_C _ hp.ne_zero)
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := F) (L := E) (x := algebraMap F E ζ * θ)
    (y := θ) (Algebra.IsAlgebraic.isAlgebraic θ) (by
      rw [← hmin]
      rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul,
        hδ, sub_self])
  refine ⟨δ, θ, σ, hp, hζ, (X_pow_sub_C_irreducible_iff_of_prime hp).1 hirr, hδ.symm, hσ, ?_⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic θ), hθ, IntermediateField.top_toSubalgebra]

theorem np_of_finrank_prime_of_isPrimitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsGalois F E] (ζ : F), p.Prime → IsPrimitiveRoot ζ p → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ _ ζ hp hζ hr x hx hloc
  classical
  obtain ⟨δ, θ, σ, hk⟩ := exists_isKum_of_finrank_prime p F E ζ hp hζ hr
  have hδ0 : δ ≠ 0 := fun h => hk.nonpow 0 (by rw [h, zero_pow hp.ne_zero])
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F {Units.mk0 δ hδ0, Units.mk0 x hx} ∅
  obtain ⟨S, hS, hadm⟩ := (exists_admissiblePlaces_superset_and_mono p F hp.pos).1 S₁
  have hfin : Units.mk0 x hx ∈ finNorm p F δ S := by
    simp only [finNorm, Subgroup.mem_iInf]
    intro v _
    exact GlobalTheory.T.mem_unitsLocalKummerNorms_of_baseChange_norm p F E (v.adicCompletion F) ζ δ θ σ hk (Units.mk0 x hx) (hloc.1 v)
  have hx' := GlobalTheory.T.sUnit_mem_kummerNorms_of_local_norms p F ζ (Units.mk0 δ hδ0) S hp hζ hadm (hS₁ S hS _ (by simp))
    hk.nonpow (Units.mk0 x hx) (hS₁ S hS _ (by simp)) hfin
  obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ _).1 hx'
  obtain ⟨-, -, -, -, -, ⟨e⟩, -⟩ := kummer_galois p F E ζ δ θ σ hk
  refine ⟨e.symm y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv]
  exact hy

end GlobalTheory.CNorm
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem tNorm_baseChange_of_ringHom (F F' E E' K K' : Type) [Field F] [Field F'] [Field E]
    [Field E'] [Algebra F F'] [Algebra F E] [Algebra F' E'] [Algebra E E'] [Algebra F E']
    [IsScalarTower F F' E'] [IsScalarTower F E E'] [Algebra.IsPushout F F' E E']
    [FiniteDimensional F E] [Field K] [Algebra F K] [Field K'] [Algebra F' K'] (φ : K →+* K')
    (hφ : ∀ x : F, φ (algebraMap F K x) = algebraMap F' K' (algebraMap F F' x)) (x : F)
    (h : TNorm F E K x) : TNorm F' E' K' (algebraMap F F' x) := by
  letI : Algebra F K' := ((algebraMap F' K').comp (algebraMap F F')).toAlgebra
  haveI : IsScalarTower F F' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨y₀, hy₀⟩ := h
  let ψ : K →ₐ[F] K' := { φ with commutes' := hφ }
  let y : K' ⊗[F] E := Algebra.TensorProduct.map ψ (AlgHom.id F E) y₀
  have hy : Algebra.norm K' y = algebraMap F K' x := by
    rw [tensor_norm_map ψ y₀, hy₀, AlgHom.commutes]
  let e₁ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F] E :=
    Algebra.TensorProduct.cancelBaseChange F F' K' K' E
  let e₂ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F'] E' :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.IsPushout.equiv F F' E E')
  refine ⟨(e₁.symm.trans e₂) y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv, hy, ← IsScalarTower.algebraMap_apply]

theorem exists_norm_eq_of_coprime_pow {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {m n : ℕ} (hc : Nat.Coprime m n) {x : F} (hx : x ≠ 0) {a b : E}
    (ha : Algebra.norm F a = x ^ m) (hb : Algebra.norm F b = x ^ n) :
    ∃ y : E, Algebra.norm F y = x := by
  refine ⟨a ^ (Nat.gcdA m n) * b ^ (Nat.gcdB m n), ?_⟩
  rw [map_mul, Algebra.norm_zpow, Algebra.norm_zpow, ha, hb, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ hx, ← Nat.gcd_eq_gcd_ab, hc]
  simp

theorem np_of_odd_prime_degree : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E],
    p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ hp h2 hd x hx hl
  obtain ⟨F', E', _, _, _, _, _, _, _, _, _, _, ζ, hpo, htc, hg, hζ, hd', hc⟩ :=
    exists_pushout_primitiveRoot p F E hp h2 hd
  have hl' : LocNorm F' E' (algebraMap F F' x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F F' w
      exact tNorm_baseChange_of_ringHom F F' E E' _ _ φ hφ x (hl.1 _)
    · exfalso
      let ψ : F' →+* ℂ := Complex.ofRealHom.comp (algebraMap F' ℝ)
      apply IsTotallyComplex.complexEmbedding_not_isReal ψ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      simp [ψ]
  obtain ⟨b, hb⟩ :=
    np_of_finrank_prime_of_isPrimitiveRoot p F' E' ζ hp hζ hd' _ (by simpa using hx) hl'
  have h1 : Algebra.norm F (Algebra.norm E b) = x ^ Module.finrank F F' := by
    rw [Algebra.norm_norm, ← Algebra.norm_norm (S := F'), hb, Algebra.norm_algebraMap]
  have h3 : Algebra.norm F (algebraMap F E x) = x ^ p := by
    rw [Algebra.norm_algebraMap, hd]
  exact exists_norm_eq_of_coprime_pow hc hx h1 h3

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.np_of_odd_prime_degree' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  atlas_forward_decl GlobalTheory.CNorm.np_of_odd_prime_degree
end
