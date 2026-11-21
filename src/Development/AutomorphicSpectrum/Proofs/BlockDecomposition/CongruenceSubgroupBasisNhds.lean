import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Mathlib

section
open ValuativeRel Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.CongruenceBasis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_pow_succ_lt {a γ : ValueGroupWithZero k} (ha0 : a ≠ 0) (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ (m + 1) < γ := by
  haveI : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h1 : 1 < a⁻¹ := (one_lt_inv₀ (zero_lt_iff.2 ha0)).2 ha
  obtain ⟨n, hn⟩ := MulArchimedean.arch γ⁻¹ h1
  refine ⟨n, ?_⟩
  have h2 : a ^ n ≤ γ := by
    rw [inv_pow] at hn
    exact (inv_le_inv₀ (zero_lt_iff.2 hγ) (zero_lt_iff.2 (pow_ne_zero n ha0))).1 hn
  exact lt_of_lt_of_le (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ha0) ha n.lt_succ_self) h2

theorem inv_mem_of_mem {N : ℕ} {t : ValueGroupWithZero k} (ht : t < 1) (g : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t) (i j : Fin N) :
    valuation k (((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t := by
  set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) - 1 with hA
  set B : Matrix (Fin N) (Fin N) k := ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 with hB
  have hAle : ∀ i j, valuation k (A i j) ≤ t := fun i j => by simpa [hA] using hg i j
  have hrel : B = -A - A * B := by
    have hgh : (g : Matrix (Fin N) (Fin N) k) * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hg' : (g : Matrix (Fin N) (Fin N) k) = A + 1 := by simp [hA]
    have hh' : ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = B + 1 := by simp [hB]
    rw [hg', hh'] at hgh
    have : (A + 1) * (B + 1) = A * B + A + B + 1 := by noncomm_ring
    rw [this] at hgh
    have h3 : A * B + A + B = 0 := by simpa using hgh
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h3]
    abel
  show valuation k (B i j) ≤ t
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N))
    (fun p => valuation k (B p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  set M := valuation k (B i₀ j₀) with hM
  have hMt : t < M := lt_of_lt_of_le hcon (hmax (i, j) (Finset.mem_univ _))
  have hM0 : 0 < M := lt_of_le_of_lt zero_le' hMt
  have hprod : valuation k ((A * B) i₀ j₀) ≤ t * M := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hAle _ _) (hmax (l, j₀) (Finset.mem_univ _))
  have htM : t * M < M := by
    simpa using mul_lt_mul_of_pos_right ht hM0
  have hent : B i₀ j₀ = -A i₀ j₀ - (A * B) i₀ j₀ := by
    conv_lhs => rw [hrel]
    simp
  have : M < M := by
    calc M = valuation k (-A i₀ j₀ - (A * B) i₀ j₀) := by rw [hM, ← hent]
      _ ≤ max (valuation k (-A i₀ j₀)) (valuation k ((A * B) i₀ j₀)) := Valuation.map_sub _ _ _
      _ < M := by
        refine max_lt ?_ (lt_of_le_of_lt hprod htM)
        rw [Valuation.map_neg]
        exact lt_of_le_of_lt (hAle _ _) hMt
  exact lt_irrefl _ this

theorem exists_congruence_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k), ϖ ≠ 0 →
    ValuativeRel.valuation k (ϖ) < 1 →
    (∀ x : k, ValuativeRel.valuation k (x) < 1 →
      ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) →
    ∀ U : Set (GL (Fin N) k), U ∈ nhds (1 : GL (Fin N) k) →
    ∃ m : ℕ, 1 ≤ m ∧ {g : GL (Fin N) k | ∀ i j,
      ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
        (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)} ⊆ U := by
  intro k _ _ _ _ N ϖ hϖ0 hϖ1 _ U hU
  set a := valuation k ϖ with ha
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  let K : ℕ → Set (GL (Fin N) k) := fun m => {g | ∀ i j,
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)}
  have hanti : Antitone K := fun m n hmn g hg i j =>
    (hg i j).trans (pow_le_pow_of_le_one zero_le' hϖ1.le (by omega))
  have hbasis : (⨅ m, 𝓟 (K m)).HasBasis (fun _ => True) K :=
    hasBasis_iInf_principal hanti.directed_ge
  have hent : ∀ (i j : Fin N) (c : GL (Fin N) k → k), (∀ m, ∀ g ∈ K m, valuation k (c g - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)) →
      Tendsto c (⨅ m, 𝓟 (K m)) (𝓝 ((1 : Matrix (Fin N) (Fin N) k) i j)) := by
    intro i j c hc
    rw [(IsValuativeTopology.hasBasis_nhds' _).tendsto_right_iff]
    intro γ hγ
    obtain ⟨m, hm⟩ := exists_pow_succ_lt ha0 hϖ1 hγ
    exact hbasis.eventually_iff.2 ⟨m, trivial, fun g hg => lt_of_le_of_lt (hc m g hg) hm⟩
  have hlim : Tendsto (id : GL (Fin N) k → GL (Fin N) k) (⨅ m, 𝓟 (K m)) (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ ?_
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact hent i j _ fun m g hg => hg i j
    · refine (MulOpposite.continuous_op.tendsto _).comp ?_
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact hent i j (fun g => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) fun m g hg =>
        inv_mem_of_mem (pow_lt_one₀ zero_le' hϖ1 (by omega)) g hg i j
  obtain ⟨m, -, hm⟩ := hbasis.mem_iff.1 (hlim hU)
  refine ⟨m + 1, by omega, fun g hg => hm fun i j => ?_⟩
  simpa [ha, map_pow] using hg i j

end GlobalTheory.CompanionTheory.CongruenceBasis
end

section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceBasis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unif_lt_one : valuation k (algebraMap 𝒪[k] k (Zls.unif k)) < 1 := by
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 Zls.irreducible_unif.not_isUnit

theorem val_le_val_unif (x : k) (hx : valuation k x < 1) :
    valuation k x ≤ valuation k (algebraMap 𝒪[k] k (Zls.unif k)) := by
  let y : 𝒪[k] := ⟨x, hx.le⟩
  have hy : ¬ IsUnit y :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hx
  have hmem : y ∈ IsLocalRing.maximalIdeal 𝒪[k] := hy
  rw [Zls.irreducible_unif.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hx' : x = algebraMap 𝒪[k] k c * algebraMap 𝒪[k] k (Zls.unif k) := by
    rw [← map_mul, hc]; rfl
  rw [hx', map_mul]
  exact mul_le_of_le_one_left' c.2

theorem val_sub_one_le_of_mem_Km {N m : ℕ} {g : GL (Fin N) k} (hg : g ∈ Zls.Km k N m) (i j : Fin N) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (algebraMap 𝒪[k] k (Zls.unif k) ^ m) := by
  obtain ⟨h, hker, rfl⟩ := Subgroup.mem_map.1 hg
  have h1 := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) =>
    u.1 i j) (MonoidHom.mem_ker.1 hker)
  have h2 : (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))
      ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) = 0 := by
    rw [map_sub, sub_eq_zero]
    simpa [Matrix.one_apply, apply_ite] using h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  have h3 : ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j =
      algebraMap 𝒪[k] k c * algebraMap 𝒪[k] k (Zls.unif k) ^ m := by
    rw [← map_pow, ← map_mul, hc, map_sub]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h3, map_mul]
  exact mul_le_of_le_one_left' c.2

theorem exists_Km_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (U : Set (GL (Fin N) k)), IsOpen U →
    (1 : GL (Fin N) k) ∈ U → ∃ m : ℕ, 1 ≤ m ∧ (Zls.Km k N m : Set (GL (Fin N) k)) ⊆ U := by
  intro k _ _ _ _ N U hU h1
  have hne : algebraMap 𝒪[k] k (Zls.unif k) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2
      Zls.irreducible_unif.ne_zero
  obtain ⟨m, hm, hsub⟩ := exists_congruence_subset k N (algebraMap 𝒪[k] k (Zls.unif k)) hne
    val_unif_lt_one val_le_val_unif U (hU.mem_nhds h1)
  exact ⟨m, hm, fun g hg => hsub fun i j => val_sub_one_le_of_mem_Km hg i j⟩

end GlobalTheory.CompanionTheory.CongruenceBasis
end
