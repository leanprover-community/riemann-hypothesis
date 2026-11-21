import Mathlib
import Formalism.FlagUnipotentLattices.LatticeDeterminantIndexSq
import Formalism.FlagUnipotentLattices.SignaturePreservingEntryNorms

open Module NumberField nonZeroDivisors Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false






















theorem euler_product_log_bound : EulerLog := by
  intro ι s e X h0 h1 he
  have hL : 0 ≤ -Real.log (1 - X) := by
    have : Real.log (1 - X) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have hpow : X ^ e p ≤ X := by
    calc X ^ e p ≤ X ^ 1 := pow_le_pow_of_le_one h0.le h1.le (he p hp)
      _ = X := pow_one X
  have h2 : Real.log (1 - X) ≤ Real.log (1 - X ^ e p) := Real.log_le_log (by linarith) (by linarith)
  have h3 : (1 : ℝ) ≤ e p := by exact_mod_cast he p hp
  nlinarith


theorem minkowski_constant_bound : MinkConst := by
  intro f
  have hN : (2 * f).factorial * 2 ^ f ≤ (2 * f) ^ (2 * f) := by
    have h1 : (2 * f).factorial = f.factorial * (f + 1).ascFactorial f := by
      rw [Nat.factorial_mul_ascFactorial]; congr 1; ring
    have h2 : f.factorial ≤ f ^ f := Nat.factorial_le_pow f
    have h3 : (f + 1).ascFactorial f ≤ (f + f) ^ f := Nat.ascFactorial_le_pow_add f f
    calc (2 * f).factorial * 2 ^ f ≤ (f ^ f * (f + f) ^ f) * 2 ^ f := by
          rw [h1]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h3)
      _ = (2 * f) ^ (2 * f) := by
          rw [two_mul f, pow_add, ← two_mul, mul_pow 2 f f]; ring
  have hR : ((2 * f).factorial : ℝ) * 2 ^ f ≤ ((2 * f : ℕ) : ℝ) ^ (2 * f) := by exact_mod_cast hN
  have hpi := Real.pi_pos
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp
  have hpos : (0 : ℝ) < ((2 * f : ℕ) : ℝ) ^ (2 * f) := by positivity
  rw [div_le_iff₀ hpos, div_pow, div_pow]
  have h4 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f := by rw [← mul_pow]; norm_num
  rw [h4]
  have hpf : (0 : ℝ) < Real.pi ^ f := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpf]
  nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) f]



















set_option backward.isDefEq.respectTransparency false in
open NumberField.Units in
theorem s5a4_torsion_real {F : Type} [Field F] [NumberField F]
    (hr : ∀ w : InfinitePlace F, w.IsReal) (x : (𝓞 F)ˣ) (hx : x ∈ torsion F) :
    x = 1 ∨ x = -1 := by
  by_cases hc : 2 < orderOf x
  · exfalso
    rw [← orderOf_units, ← orderOf_submonoid] at hc
    have h0 := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
      (IsPrimitiveRoot.orderOf ((x : 𝓞 F) : F))
    obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
    haveI : Nonempty {w : InfinitePlace F // w.IsReal} := ⟨⟨w0, hr w0⟩⟩
    rw [InfinitePlace.nrRealPlaces] at h0
    exact ((@Fintype.card_eq_zero_iff _ (_)).1 h0).false ⟨w0, hr w0⟩
  · have hc' : orderOf x ≤ 2 := not_lt.mp hc
    interval_cases hi : orderOf x
    · exact absurd ((CommGroup.mem_torsion x).1 hx) (orderOf_eq_zero_iff.mp hi)
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · right
      rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]

open NumberField.Units in
theorem units_square_index : UnitsSquareIndex := by
  intro F _ _ hr
  classical
  set S : Subgroup (𝓞 F)ˣ := (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range with hS
  obtain ⟨θ, hθd⟩ : ∃ θ : (𝓞 F)ˣ →* Multiplicative (Fin (rank F) → ZMod 2), ∀ x, θ x =
      Multiplicative.ofAdd (fun i =>
        (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2)) :=
   ⟨{ toFun := fun x => Multiplicative.ofAdd (fun i =>
        (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2))
      map_one' := by
        simp only [QuotientGroup.mk_one, ofMul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply,
          Int.cast_zero]; rfl
      map_mul' := by
        intro x y
        simp only [QuotientGroup.mk_mul, ofMul_mul, map_add, Finsupp.coe_add, Pi.add_apply,
          Int.cast_add]; rfl }, fun _ => rfl⟩
  have hθ : ∀ (x ζ : (𝓞 F)ˣ) (e : Fin (rank F) → ℤ), ζ ∈ torsion F →
      x = ζ * ∏ i, (fundSystem F i) ^ (e i) →
      θ x = Multiplicative.ofAdd (fun i => ((e i : ℤ) : ZMod 2)) := by
    intro x ζ e hζ hx
    have := fun_eq_repr F hζ hx
    rw [hθd, ← this]
  have hsurj : Function.Surjective θ := by
    intro v
    refine ⟨1 * ∏ i, (fundSystem F i) ^ (((Multiplicative.toAdd v i).val : ℕ) : ℤ), ?_⟩
    rw [hθ _ 1 _ (one_mem _) rfl]
    apply Multiplicative.toAdd.injective
    funext i
    simp
  have hsq : ∀ a : Multiplicative (Fin (rank F) → ZMod 2), a ^ 2 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    funext i
    rw [sq]
    show Multiplicative.toAdd a i + Multiplicative.toAdd a i = 0
    exact CharTwo.add_self_eq_zero _
  have hker : θ.ker = S ⊔ torsion F := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨ζ, e⟩, hxe, _⟩ := exist_unique_eq_mul_prod F x
      simp only at hxe
      rw [MonoidHom.mem_ker, hθ x ζ e ζ.2 hxe] at hx
      have h2 : ∀ i, (2 : ℤ) ∣ e i := by
        intro i
        have := congrFun (congrArg Multiplicative.toAdd hx) i
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (e i) 2).mp this
      choose e' he' using h2
      have : x = (∏ i, (fundSystem F i) ^ (e' i)) ^ 2 * ζ := by
        rw [hxe, mul_comm, ← Finset.prod_pow]
        congr 1
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [he' i, mul_comm, zpow_mul]; rfl
      rw [this]
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ζ.2
    · apply sup_le
      · rintro _ ⟨y, rfl⟩
        rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hsq]
      · intro ζ hζ
        rw [MonoidHom.mem_ker, hθ ζ ζ (fun _ => 0) hζ (by simp)]
        simp; rfl
  have hST : S ⊓ torsion F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, hx⟩
    have hx' : y ^ 2 ∈ torsion F := hx
    have hy : y ∈ torsion F := by
      rw [torsion, CommGroup.mem_torsion] at hx' ⊢
      exact hx'.of_pow (by norm_num)
    show y ^ 2 ∈ (⊥ : Subgroup (𝓞 F)ˣ)
    rw [Subgroup.mem_bot]
    rcases s5a4_torsion_real hr y hy with h | h <;> simp [h]
  have hT : Nat.card (torsion F) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨-1, neg_one_mem_torsion⟩, ?_, ?_⟩
    · intro h
      have h1 : (1 : (𝓞 F)ˣ) = -1 := congrArg Subtype.val h
      have h2 : ((1 : 𝓞 F) : F) = -1 := by
        have := congrArg (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) h1
        simpa using this
      norm_num at h2
    · apply Set.eq_univ_of_forall
      intro x
      rcases s5a4_torsion_real hr x.1 x.2 with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  have hrank : rank F + 1 = finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 : InfinitePlace.nrComplexPlaces F = 0 := by
      rw [InfinitePlace.nrComplexPlaces, Fintype.card_eq_zero_iff]
      exact ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (hr w.1)⟩
    have h4 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    rw [rank]; omega
  show S.index = _
  rw [← Subgroup.relIndex_mul_index (le_sup_left : S ≤ S ⊔ torsion F), Subgroup.relIndex_sup_left,
    ← Subgroup.inf_relIndex_right, hST, Subgroup.relIndex_bot_left, hT, ← hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← hrank, pow_succ,
    mul_comm]


theorem s5a4_tuple_count (n : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    (((Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊)).filter
      (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤ X * (1 + Real.log X) ^ n := by
  classical
  set P := Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊) with hP
  have hpos : ∀ t ∈ P, ∀ i, 0 < t i := by
    intro t ht i
    have := (Fintype.mem_piFinset.mp ht) i
    exact (Finset.mem_Icc.mp this).1
  have h1 : ((P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤
      ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    calc ∑ t ∈ P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X), ((1 : ℕ) : ℝ)
        ≤ ∑ t ∈ P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X), X * ∏ i, ((t i : ℝ))⁻¹ := by
          apply Finset.sum_le_sum
          intro t ht
          obtain ⟨htP, hle⟩ := Finset.mem_filter.mp ht
          have hp : (0 : ℝ) < ∏ i, (t i : ℝ) :=
            Finset.prod_pos (fun i _ => by exact_mod_cast hpos t htP i)
          rw [Finset.prod_inv_distrib, Nat.cast_one, ← div_eq_mul_inv, le_div_iff₀ hp, one_mul]
          push_cast at hle; exact hle
      _ ≤ ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro t _ _
          have : (0 : ℝ) ≤ ∏ i, ((t i : ℝ))⁻¹ := Finset.prod_nonneg (fun i _ => by positivity)
          nlinarith
  have h2 : ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ = X * (∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹) ^ n := by
    have := Finset.prod_univ_sum (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊)
      (fun (_ : Fin n) (j : ℕ) => ((j : ℝ))⁻¹)
    rw [← Finset.mul_sum, hP, ← this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h3 : ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹ ≤ 1 + Real.log X := by
    have := harmonic_floor_le_one_add_log X hX
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have h4 : 0 ≤ ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹ := Finset.sum_nonneg (fun j _ => by positivity)
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := by gcongr

theorem s5a4_prime_norm {K : Type} [Field K] [NumberField K] (Q : Ideal (𝓞 K)) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) : ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ k ≤ finrank ℚ K ∧ (p : 𝓞 K) ∈ Q ∧
      Ideal.absNorm Q = p ^ k := by
  have hN0 : Ideal.absNorm Q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hQ0
  have hN1 : Ideal.absNorm Q ≠ 1 := fun h => hQ.ne_top (Ideal.absNorm_eq_one_iff.mp h)

  have hex : ∀ m : ℕ, m ≠ 0 → (m : 𝓞 K) ∈ Q → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q := by
    intro m
    induction m using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _ h; exact absurd ((Ideal.eq_top_iff_one Q).mpr (by simpa using h)) hQ.ne_top
    | prime p hp => intro _ h; exact ⟨p, hp, h⟩
    | mul a b iha ihb =>
      intro hab h
      rw [Nat.cast_mul] at h
      rcases hQ.mem_or_mem h with h | h
      · exact iha (left_ne_zero_of_mul hab) h
      · exact ihb (right_ne_zero_of_mul hab) h
  obtain ⟨p, hp, hpQ⟩ := hex _ hN0 (Ideal.absNorm_mem Q)
  have hle : Ideal.span {(p : 𝓞 K)} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hpQ
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ finrank ℚ K := by
      have h := Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ)
      rw [RingOfIntegers.rank] at h
      simpa using h
    rw [this]; simp [Int.natAbs_pow]
  rw [hnp] at hdvd
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨p, k, hp, ?_, hk, hpQ, hkeq⟩
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h, pow_zero] at hkeq; exact absurd hkeq hN1
  · exact h

theorem s5a4_prime_unique {K : Type} [Field K] [NumberField K] (Q : Ideal (𝓞 K)) (hQ : Q.IsPrime)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpQ : (p : 𝓞 K) ∈ Q) (hqQ : (q : 𝓞 K) ∈ Q) : p = q := by
  by_contra hne
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (1 : 𝓞 K) ∈ Q := by
    have e : (1 : 𝓞 K) = (u : 𝓞 K) * (p : 𝓞 K) + (v : 𝓞 K) * (q : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this ⊢; exact this.symm
    rw [e]; exact Q.add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hqQ)
  exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)

open UniqueFactorizationMonoid in
theorem s5a4_primes_over {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ s : Finset (Ideal (𝓞 K)), s.card ≤ finrank ℚ K ∧
      ∀ Q : Ideal (𝓞 K), Q.IsPrime → (p : 𝓞 K) ∈ Q → Q ∈ s := by
  classical
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hI : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
  refine ⟨(normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset, ?_, ?_⟩
  · refine (Multiset.toFinset_card_le _).trans ?_
    have hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ finrank ℚ K := by
      rw [Ideal.absNorm_span_singleton]
      have : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ finrank ℚ K := by
        have h := Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ)
        rw [RingOfIntegers.rank] at h
        simpa using h
      rw [this]; simp [Int.natAbs_pow]
    have h1 : ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm).prod =
        p ^ finrank ℚ K := by
      rw [← hnp, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
    have h2 : p ^ Multiset.card ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm) ≤
        ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm).prod := by
      apply Multiset.pow_card_le_prod
      intro x hx
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨hQp, hle⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hQ
      have hpQ : (p : 𝓞 K) ∈ Q := hle (Ideal.mem_span_singleton_self _)
      have hQ0 : Q ≠ ⊥ := fun h => hp0 (by rw [h] at hpQ; exact hpQ)
      obtain ⟨q, k, hq, hk, _, hqQ, hN⟩ := s5a4_prime_norm Q hQp hQ0
      rw [hN, s5a4_prime_unique Q hQp p q hp hq hpQ hqQ]
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ k := Nat.pow_le_pow_right hq.pos hk
    rw [h1, Multiset.card_map] at h2
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  · intro Q hQ hpQ
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI]
    exact ⟨hQ, (Ideal.span_singleton_le_iff_mem Q).mpr hpQ⟩

theorem s5a4_index (K : Type) [Field K] [NumberField K] :
    ∃ ι : Ideal (𝓞 K) → Fin (finrank ℚ K), ∀ p : ℕ, p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → ι Q = ι Q' → Q = Q' := by
  classical
  have hn : 0 < finrank ℚ K := finrank_pos
  have h1 : ∀ p : ℕ, ∃ f : Ideal (𝓞 K) → Fin (finrank ℚ K), p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → f Q = f Q' → Q = Q' := by
    intro p
    by_cases hp : p.Prime
    · obtain ⟨s, hs, hmem⟩ := s5a4_primes_over (K := K) p hp
      refine ⟨fun Q => if h : Q ∈ s then Fin.castLE hs (s.equivFin ⟨Q, h⟩) else ⟨0, hn⟩, ?_⟩
      intro _ Q Q' hQ hQ' hpQ hpQ' he
      simp only [dif_pos (hmem Q hQ hpQ), dif_pos (hmem Q' hQ' hpQ')] at he
      have := s.equivFin.injective (Fin.castLE_injective hs he)
      exact congrArg Subtype.val this
    · exact ⟨fun _ => ⟨0, hn⟩, fun h => absurd h hp⟩
  choose f hf using h1
  let π : Ideal (𝓞 K) → ℕ := fun Q => if h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q then h.choose else 0
  have hπ : ∀ (Q : Ideal (𝓞 K)) (p : ℕ), Q.IsPrime → p.Prime → (p : 𝓞 K) ∈ Q → π Q = p := by
    intro Q p hQ hp hpQ
    have h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q := ⟨p, hp, hpQ⟩
    simp only [π, dif_pos h]
    exact s5a4_prime_unique Q hQ _ _ h.choose_spec.1 hp h.choose_spec.2 hpQ
  refine ⟨fun Q => f (π Q) Q, ?_⟩
  intro p hp Q Q' hQ hQ' hpQ hpQ' he
  simp only [hπ Q p hQ hp hpQ, hπ Q' p hQ' hp hpQ'] at he
  exact hf p hp Q Q' hQ hQ' hpQ hpQ' he

theorem s5a4_val {K : Type} [Field K] [NumberField K] (ι : Ideal (𝓞 K) → Fin (finrank ℚ K))
    (hι : ∀ p : ℕ, p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → ι Q = ι Q' → Q = Q')
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 K) ∈ P)
    (hk : Ideal.absNorm P = p ^ k) (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥) [DecidableEq (Ideal (𝓞 K))] :
    (((s.filter (fun Q => ι Q = ι P)).map Ideal.absNorm).prod).factorization p =
      k * s.count P := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons Q s ih =>
    have ih' := ih (fun Q' h => hs Q' (Multiset.mem_cons_of_mem h))
    obtain ⟨hQ, hQ0⟩ := hs Q (Multiset.mem_cons_self Q s)
    by_cases hi : ι Q = ι P
    · rw [Multiset.filter_cons_of_pos (p := fun Q => ι Q = ι P) s hi, Multiset.map_cons, Multiset.prod_cons]
      have hN0 : Ideal.absNorm Q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hQ0
      have hpr0 : ((s.filter (fun Q => ι Q = ι P)).map Ideal.absNorm).prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        intro h0
        obtain ⟨Q', hQ', h0'⟩ := Multiset.mem_map.mp h0
        exact (hs Q' (Multiset.mem_cons_of_mem (Multiset.mem_filter.mp hQ').1)).2
          (Ideal.absNorm_eq_zero_iff.mp h0')
      rw [Nat.factorization_mul hN0 hpr0, Finsupp.add_apply, ih']
      by_cases hQP : Q = P
      · subst hQP
        rw [Multiset.count_cons_self, hk, hp.factorization_pow, Finsupp.single_eq_same]; ring
      · obtain ⟨q, j, hq, _, _, hqQ, hj⟩ := s5a4_prime_norm Q hQ hQ0
        have hqp : q ≠ p := by
          rintro rfl
          exact hQP (hι q hq Q P hQ hP hqQ hpP hi)
        rw [Multiset.count_cons_of_ne (Ne.symm hQP), hj, hq.factorization_pow,
          Finsupp.single_eq_of_ne (Ne.symm hqp), zero_add]
    · have hQP : Q ≠ P := fun h => hi (by rw [h])
      rw [Multiset.filter_cons_of_neg (p := fun Q => ι Q = ι P) s hi, Multiset.count_cons_of_ne (Ne.symm hQP), ih']

theorem s5a4_fiber_prod {α : Type} {n : ℕ} (g : α → Fin n) (f : α → ℕ) (s : Multiset α) :
    ∏ i, ((s.filter (fun a => g a = i)).map f).prod = (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have : ∀ i, (((a ::ₘ s).filter (fun a => g a = i)).map f).prod =
        (if g a = i then f a else 1) * ((s.filter (fun a => g a = i)).map f).prod := by
      intro i
      by_cases h : g a = i
      · rw [Multiset.filter_cons_of_pos (p := fun a => g a = i) s h, Multiset.map_cons, Multiset.prod_cons, if_pos h]
      · rw [Multiset.filter_cons_of_neg (p := fun a => g a = i) s h, if_neg h, one_mul]
    simp only [this, Finset.prod_mul_distrib, ih, Finset.prod_ite_eq, Finset.mem_univ, if_true,
      Multiset.map_cons, Multiset.prod_cons]

open UniqueFactorizationMonoid in
theorem ideal_count_bound : IdealCountBound := by
  intro K _ _ X hX
  classical
  have hfin : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊).subset (fun I hI => Nat.le_floor hI.2)
  refine ⟨hfin, ?_⟩
  obtain ⟨ι, hι⟩ := s5a4_index K
  let τ : Ideal (𝓞 K) → (Fin (finrank ℚ K) → ℕ) := fun I i =>
    (((normalizedFactors I).filter (fun Q => ι Q = i)).map Ideal.absNorm).prod
  have hprod : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ∏ i, τ I i = Ideal.absNorm I := by
    intro I hI
    simp only [τ]
    rw [s5a4_fiber_prod ι (fun Q => Ideal.absNorm Q) (normalizedFactors I)]
    conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self hI, map_multiset_prod]
  have hfac : ∀ I : Ideal (𝓞 K), ∀ Q ∈ normalizedFactors I, Q.IsPrime ∧ Q ≠ ⊥ := by
    intro I Q hQ
    have := prime_of_normalized_factor Q hQ
    exact ⟨Ideal.isPrime_of_prime this, this.ne_zero⟩
  have hinj : ∀ I J : Ideal (𝓞 K), I ≠ ⊥ → J ≠ ⊥ → τ I = τ J → I = J := by
    intro I J hI hJ h
    have : normalizedFactors I = normalizedFactors J := by
      ext P
      by_cases hP : P.IsPrime ∧ P ≠ ⊥
      · obtain ⟨p, k, hp, hk1, _, hpP, hk⟩ := s5a4_prime_norm P hP.1 hP.2
        have h1 := s5a4_val ι hι P hP.1 p k hp hpP hk (normalizedFactors I) (hfac I)
        have h2 := s5a4_val ι hι P hP.1 p k hp hpP hk (normalizedFactors J) (hfac J)
        have h3 : τ I (ι P) = τ J (ι P) := congrFun h _
        simp only [τ] at h3
        rw [h3, h2] at h1
        exact (Nat.eq_of_mul_eq_mul_left hk1 h1).symm
      · rw [Multiset.count_eq_zero_of_notMem (fun h => hP (hfac I P h)),
          Multiset.count_eq_zero_of_notMem (fun h => hP (hfac J P h))]
    rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ, this]
  have hcard : hfin.toFinset.card ≤ ((Fintype.piFinset (fun _ : Fin (finrank ℚ K) =>
      Finset.Icc 1 ⌊X⌋₊)).filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card := by
    apply Finset.card_le_card_of_injOn τ
    · intro I hI
      obtain ⟨hI0, hIX⟩ := hfin.mem_toFinset.mp hI
      have hN0 : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI0
      rw [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset, hprod I hI0]
      refine ⟨fun i => ?_, hIX⟩
      have hd : τ I i ∣ Ideal.absNorm I := by
        rw [← hprod I hI0]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_ne_zero (fun h0 => hN0 (by rw [h0] at hd; exact Nat.eq_zero_of_zero_dvd hd)),
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd).trans (Nat.le_floor hIX)⟩
    · intro I hI J hJ h
      exact hinj I J (hfin.mem_toFinset.mp hI).1 (hfin.mem_toFinset.mp hJ).1 h
  rw [Set.ncard_eq_toFinset_card _ hfin]
  calc ((hfin.toFinset.card : ℕ) : ℝ) ≤ _ := by exact_mod_cast hcard
    _ ≤ _ := s5a4_tuple_count (finrank ℚ K) X hX

theorem class_number_bound : ClassNumberBound := by
  intro E _ _ hc
  classical
  set D : ℝ := Real.sqrt |(discr E : ℝ)| with hD
  have hD1 : 1 ≤ D := by
    rw [hD, Real.one_le_sqrt]
    have h0 : discr E ≠ 0 := discr_ne_zero E
    have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs h0
    exact_mod_cast this
  obtain ⟨hfin, hcount⟩ := ideal_count_bound E D hD1
  refine le_trans ?_ hcount

  have hr2 : finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have h3 : InfinitePlace.nrRealPlaces E = 0 := by
      rw [InfinitePlace.nrRealPlaces, Fintype.card_eq_zero_iff]
      exact ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.mpr w.2) (hc w.1)⟩
    omega
  have hM : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      (((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E) * D) ≤ D := by
    have h1 := minkowski_constant_bound (InfinitePlace.nrComplexPlaces E)
    rw [← hr2] at h1
    have h2 : (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces E ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      rw [div_le_one Real.pi_pos]; exact Real.two_le_pi
    have h3 : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      (((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E) * D) =
      ((4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E * ((finrank ℚ E).factorial : ℝ) /
        (finrank ℚ E : ℝ) ^ (finrank ℚ E)) * D := by ring
    rw [h3]
    calc _ ≤ 1 * D := by
          apply mul_le_mul_of_nonneg_right (h1.trans h2) (by linarith)
      _ = D := one_mul D
  choose I hI1 hI2 using exists_ideal_in_class_of_norm_le (K := E)
  have hinj : Function.Injective (fun C : ClassGroup (𝓞 E) => ((I C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E))) := by
    intro C C' h
    have : I C = I C' := Subtype.ext h
    rw [← hI1 C, ← hI1 C', this]
  have hle : Fintype.card (ClassGroup (𝓞 E)) ≤ hfin.toFinset.card := by
    rw [← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun C : ClassGroup (𝓞 E) => ((I C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)))
    · intro C _
      rw [Finset.mem_coe, hfin.mem_toFinset]
      exact ⟨nonZeroDivisors.ne_zero (I C).2, (hI2 C).trans hM⟩
    · exact hinj.injOn
  rw [Set.ncard_eq_toFinset_card _ hfin, classNumber]
  exact_mod_cast hle

end Formalism.HermitianLatticeCounting.P
