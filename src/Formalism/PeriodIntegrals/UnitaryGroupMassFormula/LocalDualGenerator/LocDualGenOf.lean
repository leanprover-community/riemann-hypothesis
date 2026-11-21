import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.PsiTower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.AddCharKernel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDualSplit

section
noncomputable section

open ValuativeRel

namespace PI.LocDualGen.FpD

open PI.LocDualGen.W

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]

def P (x : K) : Prop := ∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * (b : K))‖ ≤ 1

theorem tr_alg_mul (q : ℚ_[l]) (z : K) :
    Algebra.trace ℚ_[l] K (algebraMap ℚ_[l] K q * z) = q * Algebra.trace ℚ_[l] K z := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem norm_l_pos : (0 : ℝ) < ‖(l : ℚ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem bound : ∃ m : ℕ, ∀ x : K, P l x → algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ∈ 𝒪[K] := by
  have hn : ((Module.finrank ℚ_[l] K : ℕ) : ℚ_[l]) ≠ 0 := by
    have : 0 < Module.finrank ℚ_[l] K := Module.finrank_pos
    exact_mod_cast this.ne'
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hn) (Padic.norm_p_lt_one (p := l))
  refine ⟨m, fun x hx => ?_⟩
  by_contra hcx
  rw [Valuation.mem_integer_iff, not_le] at hcx
  have hcx0 : algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ≠ 0 := by
    intro h
    rw [h, map_zero] at hcx
    exact absurd hcx (not_lt.mpr zero_le)
  have hb : (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹ ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hcx.le
  have hx0 : x ≠ 0 := right_ne_zero_of_mul hcx0
  have hc0 : algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) ≠ 0 := left_ne_zero_of_mul hcx0
  have h1 := hx ⟨_, hb⟩
  change ‖Algebra.trace ℚ_[l] K (x * (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹)‖ ≤ 1 at h1
  have e : x * (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹ =
      algebraMap ℚ_[l] K (((l : ℚ_[l]) ^ m)⁻¹) := by
    rw [map_inv₀]
    field_simp
  rw [e, Algebra.trace_algebraMap, nsmul_eq_mul, norm_mul, norm_inv, norm_pow] at h1
  have hpos : 0 < ‖(l : ℚ_[l])‖ ^ m := pow_pos (norm_l_pos l) m
  rw [mul_inv_le_iff₀ hpos, one_mul] at h1
  exact absurd hm (not_lt.mpr h1)

private theorem t2_lemma : T2Space K := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep ?_
  intro x hx
  have hv : ValuativeRel.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨{z | ValuativeRel.valuation K z < ValuativeRel.valuation K x}, ?_, fun h => lt_irrefl (ValuativeRel.valuation K x) h⟩
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hv, fun z hz => hz⟩

private theorem isOpen_lemma_2 : IsOpen (𝒪[K] : Set K) := by
  have h0 : ((𝒪[K]).toAddSubgroup : Set K) ∈ nhds (0 : K) := by
    refine (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun z hz => ?_⟩
    have hz' : ValuativeRel.valuation K z < 1 := by simpa using hz
    exact (Valuation.mem_integer_iff _ _).2 hz'.le
  exact AddSubgroup.isOpen_of_mem_nhds _ h0

private theorem trace_cont_lemma_3 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    Continuous (Algebra.trace ℚ_[l] K) := by
  haveI := t2_lemma (K := K)
  haveI : ContinuousSMul ℚ_[l] K := ⟨by
    simp only [Algebra.smul_def]
    exact (hcont.comp continuous_fst).mul continuous_snd⟩
  exact LinearMap.continuous_of_finiteDimensional _

private theorem int_lemma_4 (hcont : Continuous (algebraMap ℚ_[l] K)) (z : ℚ_[l]) (hz : ‖z‖ ≤ 1) :
    algebraMap ℚ_[l] K z ∈ 𝒪[K] := by
  have hcl : IsClosed (𝒪[K] : Set K) :=
    AddSubgroup.isClosed_of_isOpen ((𝒪[K]).toAddSubgroup) (isOpen_lemma_2 (K := K))
  let w : ℤ_[l] := ⟨z, hz⟩
  have key : algebraMap ℚ_[l] K (w : ℚ_[l]) ∈ 𝒪[K] := by
    refine PadicInt.denseRange_natCast.induction_on w ?_ ?_
    · exact hcl.preimage (hcont.comp continuous_subtype_val)
    · intro n
      rw [PadicInt.coe_natCast, map_natCast]
      exact natCast_mem _ n

  exact key

private theorem small_lemma_5 (hcont : Continuous (algebraMap ℚ_[l] K)) (y : K) :
    ∃ N : ℕ, ∀ k ≥ N, algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y ∈ 𝒪[K] := by
  have h1 : Filter.Tendsto (fun k : ℕ => (l : ℚ_[l]) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have h2 : Filter.Tendsto (fun k : ℕ => algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y)
      Filter.atTop (nhds 0) := by
    have := ((hcont.tendsto 0).comp h1).mul_const y
    rw [map_zero, zero_mul] at this
    exact this
  have h3 : (𝒪[K] : Set K) ∈ nhds (0 : K) := (isOpen_lemma_2 (K := K)).mem_nhds (zero_mem _)
  exact Filter.eventually_atTop.1 (h2.eventually_mem h3)

private theorem P_add_mem {x y : K} (hx : P l x) (hy : P l y) : P l (x + y) := fun b => by
  rw [add_mul, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx b) (hy b))

private theorem mul_mem_dual₂ {x : K} (hx : P l x) (c : 𝒪[K]) : P l (x * c) := fun b => by
  rw [mul_assoc]
  exact hx (c * b)

private theorem bound_lemma_8 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ m : ℕ, ∀ x : K, P l x → algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ∈ 𝒪[K] := by
  classical
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hnd := traceForm_nondegenerate ℚ_[l] K
  let B := Module.finBasis ℚ_[l] K
  choose N hN using fun i => small_lemma_5 l hcont (B i)
  let b := B.isUnitSMul (w := fun i => (l : ℚ_[l]) ^ N i)
    (fun i => (isUnit_iff_ne_zero.2 hl0).pow _)
  have hb : ∀ i, b i ∈ 𝒪[K] := fun i => by
    simp only [b, Module.Basis.isUnitSMul_apply, Algebra.smul_def]
    exact hN i (N i) le_rfl
  let D := (Algebra.traceForm ℚ_[l] K).dualBasis hnd b
  choose N' hN' using fun i => small_lemma_5 l hcont (D i)
  refine ⟨Finset.univ.sup N', fun x hx => ?_⟩
  have hc : ∀ i, algebraMap ℚ_[l] K (D.repr x i) ∈ 𝒪[K] := fun i => by
    apply int_lemma_4 l hcont
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact hx ⟨b i, hb i⟩
  rw [← D.sum_repr x, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, mul_left_comm]
  exact mul_mem (hc i) (hN' i _ (Finset.le_sup (Finset.mem_univ i)))

theorem exists_ne_zero (hcont : Continuous (algebraMap ℚ_[l] K)) : ∃ x : K, x ≠ 0 ∧ P l x := by
  have hT := trace_cont_lemma_3 l hcont
  have hcpt : IsCompact (𝒪[K] : Set K) := by
    have h : CompactSpace 𝒪[K] := inferInstance
    exact isCompact_iff_compactSpace.2 h
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hT.continuousOn
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have hpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hl1
  refine ⟨algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ n), ?_, fun b => ?_⟩
  · rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · rw [tr_alg_mul, norm_mul, norm_pow]
    have h1 : ‖Algebra.trace ℚ_[l] K (b : K)‖ ≤ max C 1 := (hC b b.2).trans (le_max_left _ _)
    calc ‖(l : ℚ_[l])‖ ^ n * ‖Algebra.trace ℚ_[l] K (b : K)‖
        ≤ ‖(l : ℚ_[l])‖ ^ n * max C 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (max C 1)⁻¹ * max C 1 := mul_le_mul_of_nonneg_right hn.le hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'

end

private theorem main_lemma_9 {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K] := by
  classical
  obtain ⟨m, hm⟩ := bound_lemma_8 l hcont
  obtain ⟨x0, hx0, hPx0⟩ := exists_ne_zero l hcont
  set t : K := algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) with ht
  have ht0 : t ≠ 0 := by
    rw [ht, Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let I : Ideal 𝒪[K] :=
    { carrier := {c | P l ((c : K) * t⁻¹)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [add_mul]
        exact P_add_mem l ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro b
        simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        have h := mul_mem_dual₂ l ha c
        have e : ((c * a : 𝒪[K]) : K) * t⁻¹ = (a : K) * t⁻¹ * (c : K) := by
          push_cast
          ring
        rw [e]
        exact h }
  obtain ⟨g0, hg0⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ c : 𝒪[K], c ∈ I ↔ P l ((c : K) * t⁻¹) := fun c => Iff.rfl
  have hspan : ∀ c : 𝒪[K], c ∈ I ↔ ∃ r : 𝒪[K], r * g0 = c := fun c => by
    rw [hg0, Submodule.mem_span_singleton]
    rfl
  have hc0 : (⟨t * x0, hm x0 hPx0⟩ : 𝒪[K]) ∈ I := by
    rw [hmem]
    have e : t * x0 * t⁻¹ = x0 := by field_simp
    simpa only [e] using hPx0
  have hg0I : g0 ∈ I := (hspan g0).2 ⟨1, one_mul _⟩
  have hg0ne : (g0 : K) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := (hspan _).1 hc0
    have := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul, h, mul_zero] at this
    exact mul_ne_zero ht0 hx0 this.symm
  set g : K := (g0 : K) * t⁻¹ with hg
  have hPg : P l g := (hmem g0).1 hg0I
  have hgne : g ≠ 0 := mul_ne_zero hg0ne (inv_ne_zero ht0)
  refine ⟨g⁻¹, inv_ne_zero hgne, fun a => ?_⟩
  simp only [inv_inv]
  constructor
  · intro h
    have hPa : P l (a * g) := fun b => by
      have e : a * g * (b : K) = a * (b : K) * g := by ring
      rw [e]
      exact h b
    have hc : (⟨t * (a * g), hm _ hPa⟩ : 𝒪[K]) ∈ I := by
      rw [hmem]
      have e : t * (a * g) * t⁻¹ = a * g := by field_simp
      simpa only [e] using hPa
    obtain ⟨r, hr⟩ := (hspan _).1 hc
    have h2 := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul] at h2
    have h3 : (r : K) = a := by
      have e : t * (a * g) = a * (g0 : K) := by
        rw [hg]
        field_simp
      rw [e] at h2
      exact mul_right_cancel₀ hg0ne h2
    rw [← h3]
    exact r.2
  · intro ha b
    have h := mul_mem_dual₂ l hPg ⟨a, ha⟩ b
    have e : a * (b : K) * g = g * a * (b : K) := by ring
    rw [e]
    exact h

theorem existsDifferentGenerator : FpDual := by
  intro K _ _ _ l _ _ hK _ hcont hfin
  haveI := hK
  haveI := hfin
  exact main_lemma_9 l hcont

end PI.LocDualGen.FpD
end
end

section
set_option linter.style.haveILetI false

noncomputable section
open ValuativeRel IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace PI.LocDualGen.EpF

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]

local notation "C" => integralClosure 𝒪[K] L

theorem tf : Module.IsTorsionFree 𝒪[K] L := by
  first
    | exact Module.IsTorsionFree.trans_faithfulSMul 𝒪[K] K L
    | (rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
        IsScalarTower.algebraMap_eq 𝒪[K] K L]
       exact (algebraMap K L).injective.comp Subtype.val_injective)

theorem dd : IsDedekindDomain C := integralClosure.isDedekindDomain 𝒪[K] K L
theorem fr : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
theorem mf : Module.Finite 𝒪[K] C := IsIntegralClosure.finite 𝒪[K] K L C
theorem tfC : Module.IsTorsionFree 𝒪[K] C := by
  have hf : FaithfulSMul 𝒪[K] L := Module.isTorsionFree_iff_faithfulSMul.1 (tf K L)
  rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]
  intro a b h
  have h' := congrArg (algebraMap C L) h
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h'
  exact (FaithfulSMul.algebraMap_injective 𝒪[K] L) h'

attribute [local instance] dd fr mf tfC

theorem sepFR : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing C) := by
  first
    | infer_instance
    | exact Algebra.IsAlgebraic.isSeparable_of_perfectField

attribute [local instance] sepFR

theorem differentIdeal_eq_top
    (hU : ∀ x : C, x * x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] →
      x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) :
    differentIdeal 𝒪[K] C = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hPmax.isPrime
  have hdvd := (dvd_differentIdeal_iff (A := 𝒪[K]) (B := C) (P := P)).1 (Ideal.dvd_iff_le.2 hle)
  apply hdvd
  have hpmax : (P.comap (algebraMap 𝒪[K] C)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hpeq : P.comap (algebraMap 𝒪[K] C) = 𝓂[K] := IsLocalRing.eq_maximalIdeal hpmax
  haveI : P.LiesOver 𝓂[K] := ⟨hpeq.symm⟩
  letI := Localization.AtPrime.instAlgebraOfLiesOver 𝓂[K] P
  haveI : Localization.AtPrime.IsLiesOverAlgebra 𝓂[K] P :=
    Localization.AtPrime.instIsLiesOverAlgebra 𝓂[K] P
  rw [Algebra.isUnramifiedAt_iff_map_eq 𝒪[K] 𝓂[K] P]
  refine ⟨?_, ?_⟩
  · haveI : Finite (𝒪[K] ⧸ 𝓂[K]) := (inferInstance : Finite 𝓀[K])
    haveI : Finite 𝓂[K].ResidueField :=
      Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField 𝓂[K]).2
    haveI : PerfectField 𝓂[K].ResidueField := inferInstance
    haveI : Algebra.IsAlgebraic 𝓂[K].ResidueField P.ResidueField := inferInstance
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  · have hP0 : P ≠ ⊥ := fun h =>
      differentIdeal_ne_bot (A := 𝒪[K]) (B := C) (le_bot_iff.1 (h ▸ hle))
    haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hP0 (Localization.AtPrime P)
    haveI : FaithfulSMul 𝒪[K] C := Module.isTorsionFree_iff_faithfulSMul.1 (tfC K L)
    have hinj : Function.Injective (algebraMap C (Localization.AtPrime P)) :=
      IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
    have hinjO : Function.Injective (algebraMap 𝒪[K] (Localization.AtPrime P)) := by
      rw [IsScalarTower.algebraMap_eq 𝒪[K] C (Localization.AtPrime P)]
      exact hinj.comp (FaithfulSMul.algebraMap_injective 𝒪[K] C)
    have hmap : Ideal.map (algebraMap 𝒪[K] (Localization.AtPrime P)) 𝓂[K] =
        Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have hJP : Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] ≤ P := Ideal.map_le_iff_le_comap.2 hpeq.ge
    have hIle : Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hJP
    have hI0 : Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) ≠ ⊥ := by
      rw [← hmap, Ne, Ideal.map_eq_bot_iff_of_injective hinjO]
      exact IsDiscreteValuationRing.not_a_field _
    have hrad : ∀ x : (Localization.AtPrime P), x * x ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) →
        x ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
      intro x hx
      obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
      have h1 : algebraMap C (Localization.AtPrime P) (c * c) ∈
          Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
        have he : algebraMap C (Localization.AtPrime P) (c * c) = (IsLocalization.mk' (Localization.AtPrime P) c s * IsLocalization.mk' (Localization.AtPrime P) c s) *
            algebraMap C (Localization.AtPrime P) ((s * s : P.primeCompl) : C) := by
          rw [← IsLocalization.mk'_mul, IsLocalization.mk'_spec]
        rw [he]
        exact Ideal.mul_mem_right _ _ hx
      obtain ⟨⟨⟨a, ha⟩, ⟨m, hm⟩⟩, he⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).1 h1
      have h2 : c * c * m = a := hinj (by rw [map_mul]; exact he)
      have h3 : (m * c) * (m * c) ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] := by
        have hr : (m * c) * (m * c) = m * (c * c * m) := by ring
        rw [hr, h2]
        exact Ideal.mul_mem_left _ _ ha
      have h4 := hU _ h3
      have hv : IsUnit (algebraMap C (Localization.AtPrime P) (m * s)) :=
        IsLocalization.map_units (Localization.AtPrime P) (⟨m, hm⟩ * s : P.primeCompl)
      refine (Ideal.unit_mul_mem_iff_mem _ hv).1 ?_
      have h6 : algebraMap C (Localization.AtPrime P) (m * s) * IsLocalization.mk' (Localization.AtPrime P) c s = algebraMap C (Localization.AtPrime P) (m * c) := by
        rw [map_mul, mul_assoc, IsLocalization.mk'_spec', ← map_mul]
      rw [h6]
      exact Ideal.mem_map_of_mem _ h4
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hϖ
    rw [hmap]
    apply le_antisymm hIle
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    have key : ∀ j : ℕ, ϖ ^ (j + 1) ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) →
        ϖ ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro hj
        rcases Nat.eq_zero_or_pos j with rfl | hpos
        · simpa using hj
        · have hh : ϖ ^ ((j + 2) / 2) * ϖ ^ ((j + 2) / 2) ∈
              Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
            rw [← pow_add]
            have hs : (j + 2) / 2 + (j + 2) / 2 = (j + 1) + ((j + 2) / 2 + (j + 2) / 2 - (j + 1)) := by
              omega
            rw [hs, pow_add]
            exact Ideal.mul_mem_right _ _ hj
          have h2 := hrad _ hh
          have hs : (j + 2) / 2 = ((j + 2) / 2 - 1) + 1 := by omega
          rw [hs] at h2
          exact ih _ (by omega) h2
    cases n with
    | zero =>
      exfalso
      have h1 : (1 : (Localization.AtPrime P)) ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
        rw [hn]
        simp
      exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top ((Ideal.eq_top_iff_one _).2 (hIle h1))
    | succ k =>
      exact key k (by rw [hn]; exact Ideal.mem_span_singleton_self _)

theorem mem_C_iff (x : L) : x ∈ (1 : FractionalIdeal (nonZeroDivisors C) L) ↔ x ∈ C := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem selfDual_field
    (hU : ∀ x : C, x * x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] →
      x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) (x : L) :
    (∀ y ∈ C, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ C := by
  have hdual : FractionalIdeal.dual 𝒪[K] K (1 : FractionalIdeal (nonZeroDivisors C) L) = 1 := by
    have h := coeIdeal_differentIdeal 𝒪[K] K L C
    rw [differentIdeal_eq_top K L hU, FractionalIdeal.coeIdeal_top] at h
    exact inv_eq_one.1 h.symm
  have hr : ∀ z : K, z ∈ (algebraMap 𝒪[K] K).range ↔ z ∈ 𝒪[K] :=
    fun z => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  have h10 : (1 : FractionalIdeal (nonZeroDivisors C) L) ≠ 0 := by
    rw [Ne, ← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_eq_zero]
    exact top_ne_bot
  rw [← mem_C_iff K L x, ← hdual, FractionalIdeal.mem_dual h10]
  simp only [Algebra.traceForm_apply, mem_C_iff K L, hr]

end PI.LocDualGen.EpF
end
end

section
noncomputable section
open Module

namespace PI.LocDualGen.EpC

variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]

private theorem nontrivial_of_finrank_eq_two (hr : finrank K L = 2) : Nontrivial L := by
  rcases subsingleton_or_nontrivial L with h | h
  · rw [Module.finrank_zero_of_subsingleton] at hr
    exact absurd hr (by norm_num)
  · exact h

private theorem exists_not_mem_range_algebraMap_of_finrank_eq_two (hr : finrank K L = 2) :
    ∃ x : L, x ∉ Set.range (algebraMap K L) := by
  by_contra h
  push Not at h
  have hsurj : LinearMap.range (Algebra.linearMap K L) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨a, ha⟩ := h y
    exact ⟨a, ha⟩
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap K L)
  rw [hsurj, finrank_top, Module.finrank_self, hr] at h1
  omega

private theorem exists_eq_add_mul_of_finrank_eq_two' (hr : finrank K L = 2) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) (y : L) :
    ∃ a c : K, algebraMap K L a + algebraMap K L c * x = y := by
  have := nontrivial_of_finrank_eq_two hr
  have hli : LinearIndependent K ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      refine ⟨?_, rfl⟩
      have h0 : algebraMap K L s = 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact hst
      exact (algebraMap K L).injective (by rw [h0, map_zero])
    · exfalso
      apply hx
      refine ⟨-(s / t), ?_⟩
      have h2 : t • x = -(s • (1 : L)) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact hst
      have h3 : x = t⁻¹ • (t • x) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [Algebra.algebraMap_eq_smul_one, h3, h2, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = finrank K L := by
    rw [hr, Fintype.card_fin]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  have hy := b.sum_repr y
  rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one] at hy
  exact ⟨b.repr y 0, b.repr y 1, hy⟩

theorem dichotomy (hr : finrank K L = 2) (hred : IsReduced L) :
    IsField L ∨ ∃ e : L, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  have := nontrivial_of_finrank_eq_two hr
  obtain ⟨x, hx⟩ := exists_not_mem_range_algebraMap_of_finrank_eq_two hr
  have hrep := exists_eq_add_mul_of_finrank_eq_two' hr hx
  obtain ⟨p, q, hpq0⟩ := hrep (x ^ 2)
  have hpq : x ^ 2 = algebraMap K L p + algebraMap K L q * x := hpq0.symm
  by_cases hroot : ∃ r : K, r ^ 2 = p + q * r
  · obtain ⟨r, hr2⟩ := hroot
    have hfac : (x - algebraMap K L r) * (x - algebraMap K L (q - r)) = 0 := by
      have h' : algebraMap K L (r ^ 2) = algebraMap K L (p + q * r) := by rw [hr2]
      simp only [map_add, map_mul, map_pow, map_sub] at h' ⊢
      linear_combination hpq - h'
    by_cases hrs : r = q - r
    · exfalso
      have hsq : (x - algebraMap K L r) ^ 2 = 0 := by
        have h' := hfac
        rw [← hrs] at h'
        rw [sq]
        exact h'
      have hz : x - algebraMap K L r = 0 := hred.eq_zero _ ⟨2, hsq⟩
      exact hx ⟨r, (sub_eq_zero.mp hz).symm⟩
    · right
      have hd : q - r - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
      have hsq : (x - algebraMap K L r) * (x - algebraMap K L r) =
          algebraMap K L (q - r - r) * (x - algebraMap K L r) := by
        have h' := hfac
        simp only [map_sub] at h' ⊢
        linear_combination h'
      have hu : algebraMap K L (q - r - r)⁻¹ * algebraMap K L (q - r - r) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hd, map_one]
      have hback : x - algebraMap K L r = algebraMap K L (q - r - r) *
          (algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r)) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd, map_one, one_mul]
      refine ⟨algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r), ?_, ?_, ?_⟩
      · show _ * _ = _
        linear_combination (algebraMap K L (q - r - r)⁻¹) ^ 2 * hsq +
          algebraMap K L (q - r - r)⁻¹ * (x - algebraMap K L r) * hu
      · intro he
        rw [he, mul_zero, sub_eq_zero] at hback
        exact hx ⟨r, hback.symm⟩
      · intro he
        rw [he, mul_one] at hback
        apply hx
        refine ⟨q - r, ?_⟩
        simp only [map_sub] at hback ⊢
        linear_combination -hback
  · push Not at hroot
    left
    refine ⟨⟨0, 1, zero_ne_one⟩, fun a b => mul_comm a b, ?_⟩
    intro y hy
    obtain ⟨a, c, rfl⟩ := hrep y
    have hN : a * a + a * c * q - c ^ 2 * p ≠ 0 := by
      intro h0
      by_cases hc : c = 0
      · subst hc
        apply hy
        have ha : a = 0 := by simpa using h0
        simp [ha]
      · apply hroot (-a / c)
        have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
        linear_combination (c⁻¹) ^ 2 * h0 + (p * (1 + c * c⁻¹) - q * a * c⁻¹) * hci
    have hprod : (algebraMap K L a + algebraMap K L c * x) *
        (algebraMap K L (a + c * q) - algebraMap K L c * x) =
        algebraMap K L (a * a + a * c * q - c ^ 2 * p) := by
      simp only [map_add, map_mul, map_sub, map_pow]
      linear_combination (-(algebraMap K L c) ^ 2) * hpq
    refine ⟨algebraMap K L (a * a + a * c * q - c ^ 2 * p)⁻¹ *
      (algebraMap K L (a + c * q) - algebraMap K L c * x), ?_⟩
    rw [mul_left_comm, hprod, ← map_mul, inv_mul_cancel₀ hN, map_one]

end PI.LocDualGen.EpC
end
end

section
set_option linter.style.haveILetI false

noncomputable section
open ValuativeRel Module

namespace PI.LocDualGen.EpG

theorem field_version (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (L : Type) [Field L] [Algebra K L] (hr : finrank K L = 2)
    (O : Subring L) (hO : ∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x)
    (hU : ∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)})
    (x : L) : (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  have hOC : ∀ z : L, z ∈ O ↔ z ∈ integralClosure 𝒪[K] L := fun z => (hO z).trans Iff.rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hm : 𝓂[K] = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hcoe : ∀ c : integralClosure 𝒪[K] L,
      ((c * algebraMap 𝒪[K] (integralClosure 𝒪[K] L) ϖ : integralClosure 𝒪[K] L) : L) =
        (c : L) * algebraMap K L (ϖ : K) := by
    intro c
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply 𝒪[K] K L]
    rfl
  have hmem : ∀ z : integralClosure 𝒪[K] L,
      z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] ↔
        (z : L) ∈ Submodule.span O {algebraMap K L (ϖ : K)} := by
    intro z
    rw [hm, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨⟨c, (hOC c).2 c.2⟩, ?_⟩
      rw [← hc, hcoe]
      rfl
    · rintro ⟨a, ha⟩
      refine ⟨⟨a, (hOC a).1 a.2⟩, Subtype.ext ?_⟩
      rw [hcoe, ← ha]
      rfl
  have hU' : ∀ z : integralClosure 𝒪[K] L,
      z * z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] →
        z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] := by
    intro z hz
    rw [hmem] at hz ⊢
    exact hU ϖ hϖ z ((hOC z).2 z.2) hz
  have key := PI.LocDualGen.EpF.selfDual_field K L hU' x
  simpa only [hOC] using key

theorem quadraticSelfDual : PI.LocDualGen.W.EpSelfDual := by
  intro K _ _ _ L _ _ hK hC _ hr hred O hO hU x
  haveI := hK
  haveI := hC
  rcases PI.LocDualGen.EpC.dichotomy hr hred with hF | ⟨e, he, h0, h1⟩
  · letI : Field L := hF.toField
    exact field_version K L hr O hO hU x
  · have key := PI.LocDualGen.EpS.selfDual_split hr e he h0 h1 x
    simpa only [hO] using key

end PI.LocDualGen.EpG
end
end

section
namespace PI.LocDualGen.Of

theorem locDualGen_of (h : PI.LocDualGen.W.FpDualUnram) : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Top.stmt_of PI.LocDualGen.Psi.addCharKernel PI.LocDualGen.FpD.existsDifferentGenerator h
    PI.LocDualGen.EpG.quadraticSelfDual

end PI.LocDualGen.Of
end
