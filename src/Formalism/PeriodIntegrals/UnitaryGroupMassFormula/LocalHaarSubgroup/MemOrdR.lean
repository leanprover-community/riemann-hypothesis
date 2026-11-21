import Mathlib
import Formalism.PeriodIntegrals.LocHaarRR

section
noncomputable section

open ValuativeRel MeasureTheory Topology Polynomial

namespace PI.LocHaarRRW

section General

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V]

theorem exists_haar_of_subgroup [SigmaCompactSpace V] (R : AddSubgroup V)
    (h0 : (R : Set V) ∈ 𝓝 (0 : V)) {C : Set V} (hC : IsCompact C) (hRC : (R : Set V) ⊆ C) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (R : Set V) = 1 := by
  have hRo : IsOpen (R : Set V) := AddSubgroup.isOpen_of_mem_nhds R h0
  have hRc : IsClosed (R : Set V) := R.isClosed_of_isOpen hRo
  have hRk : IsCompact (R : Set V) := hC.of_isClosed_subset hRc hRC
  let K0 : TopologicalSpace.PositiveCompacts V :=
    { carrier := R, isCompact' := hRk,
      interior_nonempty' := by rw [hRo.interior_eq]; exact ⟨0, R.zero_mem⟩ }
  refine ⟨Measure.addHaarMeasure K0, inferInstance, inferInstance, ?_⟩
  exact Measure.addHaarMeasure_self

end General

section Field

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isCompact_integer : IsCompact (𝒪[K] : Set K) :=
  isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K])

theorem isOpen_integer' : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer

variable {K} in
theorem inv_mem_integer {x : K} (hx : x ∉ 𝒪[K]) : x⁻¹ ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff] at hx ⊢
  rw [map_inv₀]
  push Not at hx
  exact inv_le_one_of_one_le₀ hx.le

theorem sigmaCompactSpace_lf : SigmaCompactSpace K := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨⟨fun n => (fun y : K => ((ϖ : K) ^ n)⁻¹ * y) '' (𝒪[K] : Set K),
    fun n => (isCompact_integer K).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  rw [Set.mem_iUnion]
  by_cases hx : x ∈ 𝒪[K]
  · exact ⟨0, x, hx, by simp⟩
  · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
    have hxi : x⁻¹ ∈ 𝒪[K] := inv_mem_integer hx
    have hne : (⟨x⁻¹, hxi⟩ : 𝒪[K]) ≠ 0 := by
      intro h
      apply hx0
      have := congrArg (fun z : 𝒪[K] => (z : K)) h
      simpa using this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    have h1 : x⁻¹ = (u : K) * (ϖ : K) ^ n := by
      have := congrArg (fun z : 𝒪[K] => (z : K)) hu
      simpa using this
    set y : K := (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) : K) with hy
    have h2 : (u : K) * y = 1 := by
      rw [hy]; exact congrArg Subtype.val u.mul_inv
    have hp : ((ϖ : K) ^ n) ≠ 0 := pow_ne_zero _ hϖ0
    refine ⟨n, y, SetLike.coe_mem _, ?_⟩
    show ((ϖ : K) ^ n)⁻¹ * y = x
    have h3 : x⁻¹ * (((ϖ : K) ^ n)⁻¹ * y) = 1 := by
      rw [h1]
      calc (u : K) * (ϖ : K) ^ n * (((ϖ : K) ^ n)⁻¹ * y)
          = ((u : K) * y) * ((ϖ : K) ^ n * ((ϖ : K) ^ n)⁻¹) := by ring
        _ = 1 := by rw [h2, mul_inv_cancel₀ hp, one_mul]
    have h4 := inv_eq_of_mul_eq_one_right h3
    rw [inv_inv] at h4
    exact h4.symm

end Field

section Lin

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {M V : Type*} [AddCommGroup M] [Module K M] [TopologicalSpace M] [IsModuleTopology K M]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]

def homeoOfLin (e : M ≃ₗ[K] V) : M ≃ₜ V :=
  haveI := IsModuleTopology.toContinuousAdd K V
  haveI := IsModuleTopology.toContinuousAdd K M
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

end Lin

section Alg

variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]

theorem memO_of_integral {y : K} (h : IsIntegral 𝒪[K] y) : y ∈ 𝒪[K] :=
  (Valuation.integer.integers _).mem_of_integral h

theorem integral_of_memO {y : K} (h : y ∈ 𝒪[K]) : IsIntegral 𝒪[K] y := by
  have : algebraMap 𝒪[K] K ⟨y, h⟩ = y := rfl
  exact this ▸ isIntegral_algebraMap

theorem memO_of_integral_V [Nontrivial V] {y : K} (h : IsIntegral 𝒪[K] (algebraMap K V y)) :
    y ∈ 𝒪[K] :=
  memO_of_integral ((isIntegral_algebraMap_iff (algebraMap K V).injective).1 h)

theorem integral_V_of_memO [Nontrivial V] {y : K} (h : y ∈ 𝒪[K]) :
    IsIntegral 𝒪[K] (algebraMap K V y) :=
  (isIntegral_algebraMap_iff (algebraMap K V).injective).2 (integral_of_memO h)

theorem pair_indep [Nontrivial V] {θ : V} (hθ : θ ∉ (algebraMap K V).range) (s t : K)
    (h : s • (1 : V) + t • θ = 0) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at h
    exact ⟨h, rfl⟩
  · exfalso
    apply hθ
    refine ⟨-(t⁻¹ * s), ?_⟩
    have h1 : t • θ = -(s • (1 : V)) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h)
    have h2 : θ = t⁻¹ • (t • θ) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, h1, smul_neg, smul_smul, ← neg_smul, Algebra.algebraMap_eq_smul_one]

theorem exists_sq [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V] :
    ∃ θ : V, ∃ d : K, θ ∉ (algebraMap K V).range ∧ θ * θ = algebraMap K V d ∧ d ≠ 0 ∧
      d ∈ 𝒪[K] := by
  have hpos : 0 < Module.finrank K V := by rw [hr]; norm_num
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  haveI : Module.Finite K V := Module.finite_of_finrank_pos hpos
  set ι := algebraMap K V with hι
  obtain ⟨θ0, hθ0⟩ : ∃ θ0 : V, θ0 ∉ ι.range := by
    by_contra hall
    push Not at hall
    have htop : (⊤ : Submodule K V) = Submodule.span K {1} := by
      ext x
      simp only [Submodule.mem_top, true_iff, Submodule.mem_span_singleton]
      obtain ⟨c, rfl⟩ := hall x
      exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩
    have h1 := finrank_span_singleton (K := K) (one_ne_zero : (1 : V) ≠ 0)
    rw [← htop, finrank_top, hr] at h1
    norm_num at h1
  have hli : LinearIndependent K ![(1 : V), θ0] :=
    LinearIndependent.pair_iff.mpr (pair_indep hθ0)
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ0 := by simp [b]
  have hb := b.sum_repr (θ0 * θ0)
  rw [Fin.sum_univ_two, hb0, hb1] at hb
  set α := b.repr (θ0 * θ0) 0
  set β := b.repr (θ0 * θ0) 1
  have hsq : θ0 * θ0 = ι α + ι β * θ0 := by
    rw [← hb, Algebra.smul_def, Algebra.smul_def, mul_one]
  have h2 : ι β = 2 * ι (β / 2) := by
    rw [← map_ofNat ι 2, ← map_mul]; congr 1; field_simp
  set θ1 := θ0 - ι (β / 2) with hθ1def
  have hθ1 : θ1 * θ1 = ι (α + (β / 2) ^ 2) := by
    rw [hθ1def, map_add, map_pow]
    linear_combination hsq + θ0 * h2
  have hθ1r : θ1 ∉ ι.range := by
    rintro ⟨c, hc⟩
    apply hθ0
    refine ⟨c + β / 2, ?_⟩
    rw [map_add, hc, hθ1def]; ring
  have hd1 : α + (β / 2) ^ 2 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hθ1
    have hn : IsNilpotent θ1 := ⟨2, by rw [pow_two]; exact hθ1⟩
    apply hθ1r
    exact ⟨0, by rw [map_zero, IsReduced.eq_zero θ1 hn]⟩
  set d1 := α + (β / 2) ^ 2
  by_cases hdO : d1 ∈ 𝒪[K]
  · exact ⟨θ1, d1, hθ1r, hθ1, hd1, hdO⟩
  · refine ⟨ι d1⁻¹ * θ1, d1⁻¹, ?_, ?_, inv_ne_zero hd1, inv_mem_integer hdO⟩
    · rintro ⟨c, hc⟩
      apply hθ1r
      refine ⟨d1 * c, ?_⟩
      rw [map_mul, hc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd1, map_one, one_mul]
    · calc ι d1⁻¹ * θ1 * (ι d1⁻¹ * θ1) = ι d1⁻¹ * ι d1⁻¹ * (θ1 * θ1) := by ring
        _ = ι d1⁻¹ := by
          rw [hθ1, ← map_mul, ← map_mul]; congr 1; field_simp

end Alg

end PI.LocHaarRRW
end
end

section
noncomputable section

open ValuativeRel Topology Polynomial

namespace PI.LocHaarRRW

section None

variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]

theorem key_bound [Nontrivial V] [Module.Finite K V] {θ : V} {d : K}
    (hθr : θ ∉ (algebraMap K V).range) (hθ : θ * θ = algebraMap K V d) (hdO : d ∈ 𝒪[K])
    {a b : K} (hx : IsIntegral 𝒪[K] (algebraMap K V a + algebraMap K V b * θ)) :
    2 * a ∈ 𝒪[K] ∧ 2 * b * d ∈ 𝒪[K] := by
  obtain ⟨hxi, hx'⟩ : IsIntegral 𝒪[K] (algebraMap K V a + algebraMap K V b * θ) ∧
      IsIntegral 𝒪[K] (algebraMap K V a - algebraMap K V b * θ) := by
    refine ⟨hx, ?_⟩
    by_cases hb : b = 0
    · subst hb
      simpa using hx
    · obtain ⟨p, hpm, hp⟩ := hx
      have hqm : ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]).Monic := by monicity!
      have hqd : ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]).natDegree = 2 := by compute_degree!
      have hQx : ∀ y : V, (y - algebraMap K V a) ^ 2 = algebraMap K V (b ^ 2 * d) →
          aeval y ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]) = 0 := by
        intro y hy
        simp only [map_sub, map_pow, aeval_X, aeval_C, hy, sub_self]
      generalize ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]) = Q at hqm hqd hQx
      have e : ∀ y : V, aeval y (p.map (algebraMap 𝒪[K] K)) = eval₂ (algebraMap 𝒪[K] V) y p :=
        fun y => by rw [aeval_map_algebraMap, aeval_def]
      generalize p.map (algebraMap 𝒪[K] K) = P at e
      have key : ∀ y : V, aeval y Q = 0 → aeval y P = aeval y (P %ₘ Q) := by
        intro y hy
        conv_lhs => rw [← modByMonic_add_div P Q]
        simp [hy]
      have hQ1 : Q ≠ 1 := by
        rintro rfl
        simp at hqd
      have hrd : (P %ₘ Q).natDegree ≤ 1 := by
        have := natDegree_modByMonic_lt P hqm hQ1
        omega
      generalize P %ₘ Q = r at key hrd
      have hr := eq_X_add_C_of_natDegree_le_one hrd
      have hx1 : (algebraMap K V a + algebraMap K V b * θ - algebraMap K V a) ^ 2 =
          algebraMap K V (b ^ 2 * d) := by
        rw [map_mul, map_pow, ← hθ]; ring
      have hx2 : (algebraMap K V a - algebraMap K V b * θ - algebraMap K V a) ^ 2 =
          algebraMap K V (b ^ 2 * d) := by
        rw [map_mul, map_pow, ← hθ]; ring
      have hrx : aeval (algebraMap K V a + algebraMap K V b * θ) r = 0 := by
        rw [← key _ (hQx _ hx1), e]
        exact hp
      rw [hr] at hrx
      simp only [map_add, map_mul, aeval_X, aeval_C] at hrx
      have hw : r.coeff 1 = 0 := by
        by_contra hw
        apply hθr
        have hwb : r.coeff 1 * b ≠ 0 := mul_ne_zero hw hb
        have hinv : algebraMap K V (r.coeff 1 * b)⁻¹ *
            (algebraMap K V (r.coeff 1) * algebraMap K V b) = 1 := by
          rw [← map_mul, ← map_mul, inv_mul_cancel₀ hwb, map_one]
        refine ⟨-(r.coeff 1 * a + r.coeff 0) * (r.coeff 1 * b)⁻¹, ?_⟩
        rw [map_mul, map_neg, map_add, map_mul]
        linear_combination (-(algebraMap K V (r.coeff 1 * b)⁻¹)) * hrx + θ * hinv
      have hu : r.coeff 0 = 0 := by
        rw [hw] at hrx
        apply (algebraMap K V).injective
        simpa using hrx
      refine ⟨p, hpm, ?_⟩
      rw [← e, key _ (hQx _ hx2), hr, hw, hu]
      simp
  have hθi : IsIntegral 𝒪[K] θ := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hθ]
    exact integral_V_of_memO hdO
  have hA : algebraMap K V (2 * a) = (algebraMap K V a + algebraMap K V b * θ) +
      (algebraMap K V a - algebraMap K V b * θ) := by
    rw [map_mul, map_ofNat]; ring
  have hB : algebraMap K V (2 * b * d) = (algebraMap K V a + algebraMap K V b * θ) * θ +
      (algebraMap K V a - algebraMap K V b * θ) * (-θ) := by
    rw [map_mul, map_mul, map_ofNat]
    linear_combination (-2 * algebraMap K V b) * hθ
  refine ⟨memO_of_integral_V (V := V) ?_, memO_of_integral_V (V := V) ?_⟩
  · rw [hA]; exact hxi.add hx'
  · rw [hB]; exact (hxi.mul hθi).add (hx'.mul hθi.neg)

theorem integral_mem_nhds_and_subset_compact_of_finrank_two [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V]
    [TopologicalSpace V] [IsModuleTopology K V]
    (O : Subring V) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[K] x) :
    ∃ _ : K × K ≃ₜ V, (O : Set V) ∈ 𝓝 (0 : V) ∧ ∃ C : Set V, IsCompact C ∧ (O : Set V) ⊆ C := by
  classical
  obtain ⟨θ, d, hθr, hθ, hd0, hdO⟩ := exists_sq (K := K) (V := V) hr
  haveI : Module.Finite K V := Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hr]; norm_num)
  have hθi : IsIntegral 𝒪[K] θ := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hθ]
    exact integral_V_of_memO hdO
  let L : K × K →ₗ[K] V :=
    (LinearMap.fst K K K).smulRight (1 : V) + (LinearMap.snd K K K).smulRight θ
  have hL : ∀ p : K × K, L p = algebraMap K V p.1 + algebraMap K V p.2 * θ := by
    intro p
    simp [L, Algebra.smul_def]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    have hb : p.2 = 0 := by
      by_contra hb
      apply hθr
      refine ⟨-p.1 * p.2⁻¹, ?_⟩
      have hinv : algebraMap K V p.2⁻¹ * algebraMap K V p.2 = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hb, map_one]
      rw [map_mul, map_neg]
      linear_combination (-(algebraMap K V p.2⁻¹)) * hp + θ * hinv
    have ha : p.1 = 0 := by
      rw [hb] at hp
      apply (algebraMap K V).injective
      simpa using hp
    exact Prod.ext ha hb
  have hsurj : Function.Surjective L := by
    have : Module.finrank K (K × K) = Module.finrank K V := by
      rw [Module.finrank_prod, Module.finrank_self, hr]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).mp hinj
  obtain ⟨e, he⟩ : ∃ e : (K × K) ≃ₗ[K] V,
      ∀ p, e p = algebraMap K V p.1 + algebraMap K V p.2 * θ :=
    ⟨LinearEquiv.ofBijective L (show Function.Bijective L from ⟨hinj, hsurj⟩), fun p => hL p⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd (R := K) (A := V)
  haveI : ContinuousSMul K V := IsModuleTopology.toContinuousSMul (R := K) (A := V)
  obtain ⟨h, hh⟩ : ∃ h : K × K ≃ₜ V, ∀ p, h p = e p :=
    ⟨{ toEquiv := e.toEquiv
       continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
       continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
     fun _ => rfl⟩
  refine ⟨h, ?_, ?_⟩
  · have hsub : h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) ⊆ (O : Set V) := by
      rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
      show h p ∈ O
      rw [hO, hh, he]
      exact (integral_V_of_memO hp1).add ((integral_V_of_memO hp2).mul hθi)
    have hopen : IsOpen (h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K))) :=
      h.isOpenMap _ ((isOpen_integer' (K := K)).prod (isOpen_integer' (K := K)))
    have h0 : (0 : V) ∈ h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) :=
      ⟨(0, 0), ⟨Subring.zero_mem _, Subring.zero_mem _⟩, by rw [hh]; exact map_zero e⟩
    exact Filter.mem_of_superset (hopen.mem_nhds h0) hsub
  · refine ⟨h '' ((fun q : K × K => (q.1 * 2⁻¹, q.2 * (2 * d)⁻¹)) ''
      ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K))), ?_, ?_⟩
    · exact (((isCompact_integer (K := K)).prod (isCompact_integer (K := K))).image
        (by fun_prop)).image h.continuous
    · intro x hx
      have hpx : h (h.symm x) = x := h.apply_symm_apply x
      have hint : IsIntegral 𝒪[K]
          (algebraMap K V (h.symm x).1 + algebraMap K V (h.symm x).2 * θ) := by
        rw [← he, ← hh, hpx]
        exact (hO x).mp hx
      obtain ⟨h1, h2⟩ := key_bound hθr hθ hdO hint
      refine ⟨h.symm x, ⟨(2 * (h.symm x).1, 2 * (h.symm x).2 * d), ⟨h1, h2⟩, ?_⟩, hpx⟩
      refine Prod.ext ?_ ?_ <;> dsimp only <;> first | (field_simp; done) | (field_simp; ring)

end None

end PI.LocHaarRRW
end
end

section
noncomputable section

open ValuativeRel MeasureTheory Topology IsDedekindDomain NumberField

namespace PI.LocHaarRRW

section Some

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}

theorem mem_ordR (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (h1 : (sg.e x).1 ∈ 𝒪[A.Fp]) (h2 : (sg.e x).2 ∈ 𝒪[A.Fp])
    (h12 : Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).1, h1⟩ =
      Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).2, h2⟩) :
    x ∈ PI.LocHaarRR.ordR sg := by
  simp only [PI.LocHaarRR.ordR]
  rw [Subring.mem_comap, Subring.mem_map]
  exact ⟨(⟨_, h1⟩, ⟨_, h2⟩), h12, rfl⟩

theorem ordR_sub (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (hx : x ∈ PI.LocHaarRR.ordR sg) : (sg.e x).1 ∈ 𝒪[A.Fp] ∧ (sg.e x).2 ∈ 𝒪[A.Fp] := by
  simp only [PI.LocHaarRR.ordR] at hx
  rw [Subring.mem_comap, Subring.mem_map] at hx
  obtain ⟨y, -, hy⟩ := hx
  have hy' : sg.e x = ((y.1 : A.Fp), (y.2 : A.Fp)) := hy.symm
  rw [hy']
  exact ⟨y.1.2, y.2.2⟩

end Some

theorem target : PI.LocHaarRR.Target := by
  intro F E _ _ _ _ _ sig p A hred
  haveI := A.lf
  haveI := A.top
  haveI := A.borel
  haveI := A.char0
  haveI := A.free
  haveI : IsTopologicalAddGroup A.Ep := IsModuleTopology.topologicalAddGroup A.Fp A.Ep
  haveI := sigmaCompactSpace_lf A.Fp
  rcases hs : A.split with _ | sg
  · obtain ⟨H, h0, C, hC, hOC⟩ := integral_mem_nhds_and_subset_compact_of_finrank_two A.rank A.O A.O_def
    haveI : SigmaCompactSpace A.Ep := H.symm.isClosedEmbedding.sigmaCompactSpace
    have hR : PI.LocHaarRR.RR A = (A.O : Set A.Ep) := by simp [PI.LocHaarRR.RR, hs]
    rw [hR]
    exact exists_haar_of_subgroup A.O.toAddSubgroup h0 hC hOC
  · have hR : PI.LocHaarRR.RR A = (PI.LocHaarRR.ordR sg : Set A.Ep) := by
      simp [PI.LocHaarRR.RR, hs]
    rw [hR]
    let H : A.Fp × A.Fp ≃ₜ A.Ep := homeoOfLin sg.e.symm.toLinearEquiv
    have hH : ∀ y, sg.e (H y) = y := fun y => sg.e.apply_symm_apply y
    have hH' : ∀ x, H (sg.e x) = x := fun x => sg.e.symm_apply_apply x
    haveI : SigmaCompactSpace A.Ep := H.symm.isClosedEmbedding.sigmaCompactSpace
    have hq0 : (sg.q : A.Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
    let Q : Set A.Fp := (fun y : A.Fp => (sg.q : A.Fp) * y) '' (𝒪[A.Fp] : Set A.Fp)
    have hQ : IsOpen Q := (Homeomorph.mulLeft₀ (sg.q : A.Fp) hq0).isOpenMap _ (isOpen_integer' _)
    refine exists_haar_of_subgroup (PI.LocHaarRR.ordR sg).toAddSubgroup ?_
      (((isCompact_integer _).prod (isCompact_integer _)).image H.continuous) ?_
    · rw [mem_nhds_iff]
      refine ⟨H '' (Q ×ˢ Q), ?_, H.isOpenMap _ (hQ.prod hQ), ⟨(0, 0), ⟨⟨0, zero_mem _, by simp⟩,
        ⟨0, zero_mem _, by simp⟩⟩, by have h00 := hH' 0; rw [map_zero] at h00; exact h00⟩⟩
      rintro _ ⟨⟨_, _⟩, ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩, rfl⟩
      have h1 : (sg.e (H ((sg.q : A.Fp) * u, (sg.q : A.Fp) * v))).1 ∈ 𝒪[A.Fp] := by
        rw [hH]; exact mul_mem sg.q.2 hu
      have h2 : (sg.e (H ((sg.q : A.Fp) * u, (sg.q : A.Fp) * v))).2 ∈ 𝒪[A.Fp] := by
        rw [hH]; exact mul_mem sg.q.2 hv
      refine mem_ordR sg h1 h2 ?_
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      refine ⟨⟨u, hu⟩ - ⟨v, hv⟩, Subtype.ext ?_⟩
      simp only [hH, AddSubgroupClass.coe_sub, MulMemClass.coe_mul]
      ring
    · intro x hx
      obtain ⟨h1, h2⟩ := ordR_sub sg hx
      exact ⟨sg.e x, ⟨h1, h2⟩, hH' x⟩

end PI.LocHaarRRW
end
end
