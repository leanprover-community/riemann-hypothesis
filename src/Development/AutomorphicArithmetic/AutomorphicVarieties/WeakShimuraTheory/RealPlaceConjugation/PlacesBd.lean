import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DecInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SupIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbIndex

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem addClosed_index (l : ℕ) [Fact l.Prime] (A : AddSubgroup ℤ_[l])
    (hA : IsClosed (A : Set ℤ_[l])) (a : ℤ_[l]) (ha : a ∈ A) (h0 : a ≠ 0) : A.index ≠ 0 := by
  have key : ∀ x : ℤ_[l], a * x ∈ A := by
    intro x
    refine PadicInt.denseRange_intCast.induction_on x ?_ ?_
    · exact hA.preimage (continuous_const.mul continuous_id)
    · intro m
      have hm : a * (m : ℤ_[l]) = m • a := by rw [zsmul_eq_mul, mul_comm]
      rw [hm]
      exact A.zsmul_mem ha m
  have hspec := PadicInt.unitCoeff_spec h0
  set w := PadicInt.unitCoeff h0
  set n := a.valuation
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let f := (PadicInt.toZModPow (p := l) n).toAddMonoidHom
  have hle : f.ker ≤ A := by
    intro x hx
    have hx' : x ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := hx
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx'
    obtain ⟨y, rfl⟩ := hx'
    have hw : (w : ℤ_[l]) * ↑w⁻¹ = 1 := Units.mul_inv w
    have heq : (l : ℤ_[l]) ^ n * y = a * (↑w⁻¹ * y) := by
      conv_rhs => rw [hspec]
      linear_combination (-((l : ℤ_[l]) ^ n * y)) * hw
    rw [heq]
    exact key _
  have hfin : f.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  intro hA0
  apply hfin
  exact Nat.eq_zero_of_zero_dvd (hA0 ▸ AddSubgroup.index_dvd_of_le hle)

open GroundTheory.Global.Cyclotomic in
theorem UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) → (∃ u ∈ H, ¬ IsOfFinOrder u) → H.index ≠ 0 := by
  intro l _ H hH hu
  obtain ⟨u, huH, hu⟩ := hu
  set L := padicUnitsLog l with hL
  have hB : IsClosed ((H.map L : Subgroup (Multiplicative ℤ_[l])) : Set (Multiplicative ℤ_[l])) := by
    rw [Subgroup.coe_map]
    exact ((hH.isCompact).image (continuous_padicUnitsLog l)).isClosed
  let A : AddSubgroup ℤ_[l] := Subgroup.toAddSubgroup' (H.map L)
  have hAc : IsClosed (A : Set ℤ_[l]) := hB
  have haA : Multiplicative.toAdd (L u) ∈ A := by
    rw [Subgroup.mem_toAddSubgroup']
    exact ⟨u, huH, rfl⟩
  have ha0 : Multiplicative.toAdd (L u) ≠ 0 := by
    intro h
    apply hu
    have h1 : L u = 1 := by
      rw [← ofAdd_toAdd (L u), h]
      rfl
    rw [hL, padicUnitsLog_eq_one_iff] at h1
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, torsionExponent_pos l, h1⟩
  have hAi : A.index ≠ 0 := addClosed_index l A hAc _ haA ha0
  have hMi : (H.map L).index ≠ 0 := hAi
  have hK : (H ⊔ L.ker).index ≠ 0 := by
    rw [← Subgroup.comap_map_eq, Subgroup.index_comap_of_surjective _ (padicUnitsLog_surjective l)]
    exact hMi
  have hker : L.ker ≤ rootsOfUnity (torsionExponent l) ℤ_[l] := by
    intro x hx
    rw [mem_rootsOfUnity]
    rw [MonoidHom.mem_ker, hL, padicUnitsLog_eq_one_iff] at hx
    exact hx
  have hcard : Nat.card L.ker ≠ 0 := by
    haveI : NeZero (torsionExponent l) := ⟨(torsionExponent_pos l).ne'⟩
    haveI : Finite L.ker := Finite.of_injective (Subgroup.inclusion hker) (Subgroup.inclusion_injective hker)
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  have hrel : H.relIndex (H ⊔ L.ker) ≠ 0 := by
    rw [sup_comm, Subgroup.relIndex_sup_right]
    intro h0
    apply hcard
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_card H L.ker)
  rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ L.ker)]
  exact mul_ne_zero hrel hK
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.index_cyclotomicKer_sup_decompositionGroup_ne_zero :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → ((cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A).index ≠ 0 := by
  intro Ω _ _ _ l _ p A hp hA
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hg : ∃ g ∈ Dec (F := ℚ) A, ¬ IsOfFinOrder (cycZ ℚ Ω l g) := by
    by_cases hlp : l = p
    · subst hlp
      obtain ⟨g, hg, hf⟩ := UpperTheory.V.Base.decInf ℚ Ω l ⊤ isOpen_univ A hA
      exact ⟨g, hg.2, hf⟩
    · obtain ⟨-, -, γ, hγ, -, hc⟩ := UpperTheory.V.Chr.decCyc Ω p A hp hA
      refine ⟨γ, hγ, fun hf => ?_⟩
      obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
      have h3 := congrArg (Units.val : ℤ_[l]ˣ → ℤ_[l]) e
      rw [Units.val_pow_eq_pow_val, hc l hlp, Units.val_one] at h3
      have h4 : p ^ n = 1 := by exact_mod_cast h3
      exact (Nat.one_lt_pow hn.ne' hp.one_lt).ne' h4
  obtain ⟨g, hg, hf⟩ := hg
  have hcl : IsClosed (((Dec (F := ℚ) A).map (cycZ ℚ Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
    ((isClosed_Dec (F := ℚ) A).isCompact.image (continuous_cycZ ℚ Ω l)).isClosed
  have h0 := UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder l _ hcl ⟨_, ⟨g, hg, rfl⟩, hf⟩
  have e : (cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A = ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).comap (cycZ ℚ Ω l) := by
    rw [Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  exact fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

open scoped Pointwise in
private theorem val_smul_fix {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) (v : G ℚ Ω) (x : Ω)
    (hx : v x = x) : (v • B).valuation x < 1 ↔ B.valuation x < 1 := by
  have key : ∀ A : ValuationSubring Ω, A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
    intro A
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · have e := (A.valuation).one_lt_val_iff (inv_ne_zero h)
      rw [inv_inv] at e
      rw [← e, ← not_le, A.valuation_le_one_iff]
      simp [h]
  have mem : x⁻¹ ∈ v • B ↔ x⁻¹ ∈ B := by
    have hv : v x⁻¹ = x⁻¹ := by rw [map_inv₀, hx]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change v z = x⁻¹ at hzx
      have hz' : z = x⁻¹ := v.injective (hzx.trans hv.symm)
      exact hz' ▸ hz
    · intro h
      exact ⟨x⁻¹, h, hv⟩
  rw [key, key, mem]

theorem UpperTheory.V.Ws.ncard_placesDividing_le_of_orbitBound :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (V : Subgroup (G ℚ Ω)) (p n : ℕ), p ≠ 0 → V ≤ F.fixingSubgroup → OrbLe V p n → (plDvd F p).ncard ≤ n := by
  intro Ω _ _ _ F _ V p n hp hV hO
  obtain ⟨T, hT, hTp, hTA⟩ := hO
  have po : ∀ (w : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      (placeOf Ω w).valuation (algebraMap F Ω (y : F)) < 1 ↔ y ∈ w.asIdeal := by
    intro w y
    have h := isPlaceOver_placeOf Ω w
    unfold IsPlaceOver at h
    exact h y
  have fix : ∀ σ ∈ V, ∀ y : 𝓞 F, σ (algebraMap F Ω (y : F)) = algebraMap F Ω (y : F) := by
    intro σ hσ y
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).1 (hV hσ) _ (by simp)
  open scoped Pointwise in
  have hup : ∀ w ∈ plDvd F p, ∃ B ∈ T, ∃ σ ∈ V, σ • B = placeOf Ω w := by
    intro w hw
    apply hTA
    have hw' : ((p : 𝓞 F)) ∈ w.asIdeal := hw
    simpa using (po w p).2 hw'
  choose! f hfT σ hσV hσ using hup
  have hinj : Set.InjOn f (plDvd F p) := by
    intro w1 h1 w2 h2 he
    apply HeightOneSpectrum.ext
    ext y
    rw [← po w1 y, ← po w2 y, ← hσ w1 h1, ← hσ w2 h2,
      val_smul_fix _ _ _ (fix _ (hσV w1 h1) y), val_smul_fix _ _ _ (fix _ (hσV w2 h2) y), he]
  calc (plDvd F p).ncard ≤ (T : Set (ValuationSubring Ω)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun w hw => hfT w hw) hinj T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ n := hT
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem plDvd_eq (F : Type) [Field F] (N : ℕ) (hN : N ≠ 0) :
    plDvd F N = ⋃ p ∈ N.primeFactors, plDvd F p := by
  ext v
  simp only [plDvd, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · have key : ∀ M : ℕ, M ≠ 0 → ((M : 𝓞 F) ∈ v.asIdeal) →
        ∃ p ∈ M.primeFactors, (p : 𝓞 F) ∈ v.asIdeal := by
      intro M
      induction M using Nat.strong_induction_on with
      | _ M ih =>
        intro hM hv
        by_cases h1 : M = 1
        · subst h1
          rw [Nat.cast_one] at hv
          exact (v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hv)).elim
        · obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
          rw [Nat.cast_mul] at hv
          rcases v.isPrime.mem_or_mem hv with h | h
          · exact ⟨p, Nat.mem_primeFactors.2 ⟨hp, dvd_mul_right p m, hM⟩, h⟩
          · have hm0 : m ≠ 0 := by
              rintro rfl
              simp at hM
            have hlt : m < p * m := by
              have := hp.two_le
              have := Nat.pos_of_ne_zero hm0
              nlinarith
            obtain ⟨q, hq, hqv⟩ := ih m hlt hm0 h
            have hq' := Nat.mem_primeFactors.1 hq
            exact ⟨q, Nat.mem_primeFactors.2 ⟨hq'.1, hq'.2.1.mul_left p, hM⟩, hqv⟩
    exact key N hN
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨m, hm⟩ := (Nat.mem_primeFactors.1 hp).2.1
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv

theorem UpperTheory.V.Ws.exists_uniform_bound_ncard_placesDividing :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)) (N : ℕ), U.Normal → IsOpen (U : Set (G ℚ Ω)) → N ≠ 0 → ∃ g : ℕ, ∀ (F : IntermediateField ℚ Ω) [NumberField F], cycU l U ≤ F.fixingSubgroup → (plDvd F N).ncard ≤ g := by
  intro Ω _ _ _ l _ U N hUn hUo hN
  haveI := hUn
  haveI : (cycU l U).Normal := by
    unfold cycU
    infer_instance
  have hUi : U.index ≠ 0 := by
    haveI := Subgroup.quotient_finite_of_isOpen U hUo
    exact Subgroup.index_ne_zero_of_finite
  have hUle : ∀ {X : Type} (s : Finset ℕ) (f : ℕ → Set X),
      (⋃ p ∈ s, f p).ncard ≤ ∑ p ∈ s, (f p).ncard := by
    intro X s f
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)
  have hb : ∀ p : ℕ, ∃ n, p.Prime → OrbLe (cycU l U) p n := by
    intro p
    by_cases hA : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1
    · obtain ⟨A₀, hA₀⟩ := hA
      refine ⟨(cycU l U ⊔ Dec A₀).index, fun hp => ?_⟩
      have hK := index_cyclotomicKer_sup_decompositionGroup_ne_zero Ω l p A₀ hp hA₀
      have hs := supIndex (G ℚ Ω) (cycZ ℚ Ω l).ker U (Dec A₀) hUi hK
      exact orbIndex Ω p (cycU l U) A₀ hp hA₀ hs.1
    · exact ⟨0, fun _ => ⟨∅, by simp, by simp, fun A hA' => (hA ⟨A, hA'⟩).elim⟩⟩
  choose nf hnf using hb
  refine ⟨∑ p ∈ N.primeFactors, nf p, fun F _ hF => ?_⟩
  rw [plDvd_eq F N hN]
  refine (hUle _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hpp := (Nat.mem_primeFactors.1 hp).1
  exact ncard_placesDividing_le_of_orbitBound Ω F (cycU l U) p (nf p) hpp.ne_zero hF (hnf p hpp)
end
