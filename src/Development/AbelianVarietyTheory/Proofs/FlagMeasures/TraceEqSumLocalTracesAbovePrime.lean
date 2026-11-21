import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataSpaces
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocalTraceSum

open Filter Topology TensorProduct

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem t2 : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem isOpen_lt (γ : ValueGroupWithZero K) : IsOpen {x : K | valuation K x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hγ : γ ≠ 0 := (lt_of_le_of_lt zero_le hx).ne'
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.2 ⟨γ, hγ, fun y hy => ?_⟩
  have := (valuation K).map_add_lt (x := y - x) (y := x) hy hx
  simpa using this

theorem tendsto_pow {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]

theorem contSMul (hc : Continuous (algebraMap ℚ_[l] K)) : ContinuousSMul ℚ_[l] K :=
  continuousSMul_of_algebraMap _ _ hc

variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem continuous_algHom [FiniteDimensional ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    (τ : K →ₐ[ℚ_[l]] Ω) : Continuous τ := by
  have := contSMul hc
  have : T2Space K := t2
  exact τ.toLinearMap.continuous_of_finiteDimensional

theorem norm_lt_one [FiniteDimensional ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    (τ : K →ₐ[ℚ_[l]] Ω) {x : K} (h : valuation K x < 1) : ‖τ x‖ < 1 := by
  have h1 := ((continuous_algHom hc τ).tendsto 0).comp (tendsto_pow h)
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  simpa [Function.comp_def] using h1

end Local

section Place

variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]

theorem norm_int_le (σ : F →+* Ω) (a : 𝓞 F) : ‖σ a‖ ≤ 1 := by
  have h : IsIntegral ℤ (σ a) := a.isIntegral_coe.map σ.toIntAlgHom
  have h2 : IsIntegral (NormedField.valuation (K := Ω)).integer (σ a) := h.tower_top
  have := (Valuation.integer.integers _).mem_of_integral h2
  exact this

def ker (σ : F →+* Ω) : Ideal (𝓞 F) where
  carrier := {a | ‖σ a‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, RingOfIntegers.coe_eq_algebraMap, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le σ c)) ha

theorem mem_ker (σ : F →+* Ω) (a : 𝓞 F) : a ∈ ker σ ↔ ‖σ a‖ < 1 := Iff.rfl

theorem ker_isPrime (σ : F →+* Ω) : (ker σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_ker]; simp
  · intro a b hab
    rw [mem_ker] at hab
    by_contra h
    rw [not_or, mem_ker, mem_ker, not_lt, not_lt] at h
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at hab
    nlinarith [h.1, h.2]

theorem norm_le_one (σ : F →+* Ω) (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal = ker σ)
    {a : F} (ha : p.valuation F a ≤ 1) : ‖σ a‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := p.exists_primeCompl_mul_eq_of_integer a ha
  have hd : ¬ ‖σ (d : 𝓞 F)‖ < 1 := by
    rw [← mem_ker, ← hp]; exact d.2
  have h1 : ‖σ a‖ * ‖σ (d : 𝓞 F)‖ = ‖σ n‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun x => ‖σ x‖) h
  have h2 := norm_int_le σ n
  nlinarith [norm_nonneg (σ a), not_lt.1 hd]

end Place

section Ext

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem norm_l_lt : ‖(l : Ω)‖ < 1 := by
  have : (l : Ω) = algebraMap ℚ_[l] Ω l := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_ext (hc : Continuous (algebraMap ℚ_[l] K)) (ι : F →+* K) (hι : DenseRange ι)
    (σ : F →+* Ω) (h : ∀ a : F, valuation K (ι a) < 1 → ‖σ a‖ ≤ 1) :
    ∃ τ : K →ₐ[ℚ_[l]] Ω, ∀ a, τ (ι a) = σ a := by
  have := contSMul hc
  have : T2Space K := t2
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] _).injective
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ_[l] _).injective
  let φ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] K :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ι.toRatAlgHom (fun _ _ => .all _ _)
  let ψ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) σ.toRatAlgHom (fun _ _ => .all _ _)
  have hφ : ∀ c a, φ (c ⊗ₜ a) = c • ι a := fun c a => by simp [φ, Algebra.smul_def]
  have hψ : ∀ c a, ψ (c ⊗ₜ a) = c • σ a := fun c a => by simp [ψ, Algebra.smul_def]
  have hsurj : Function.Surjective φ := by
    have hcl : IsClosed (LinearMap.range φ.toLinearMap : Set K) :=
      Submodule.closed_of_finiteDimensional _
    intro x
    have : x ∈ (LinearMap.range φ.toLinearMap : Set K) := by
      refine hι.induction_on x hcl fun a => ⟨1 ⊗ₜ a, ?_⟩
      simp [hφ]
    exact this
  let G : AddSubgroup (K × Ω) := ((ι.prod σ).toAddMonoidHom.range).topologicalClosure
  have hG : ∀ z, (φ z, ψ z) ∈ G := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact G.zero_mem
    | add x y hx hy => simpa using G.add_mem hx hy
    | tmul c a =>
      rw [hφ, hψ]
      refine (Padic.denseRange_ratCast l).induction_on c ?_ fun q => ?_
      · exact (AddSubgroup.isClosed_topologicalClosure _).preimage
          (f := fun c : ℚ_[l] => (c • ι a, c • σ a)) (by fun_prop)
      · refine AddSubgroup.le_topologicalClosure _ ⟨(q : F) * a, ?_⟩
        simp [Algebra.smul_def]
  have hl : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl' : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hker : ∀ z, φ z = 0 → ψ z = 0 := by
    intro z hz
    have hb : ∀ k : ℕ, ‖ψ z‖ ≤ ‖(l : Ω)‖ ^ k := by
      intro k
      have hcl : IsClosed ({w : K × Ω | valuation K w.1 < valuation K ((l : K) ^ k)}ᶜ ∪
          {w : K × Ω | ‖w.2‖ ≤ ‖(l : Ω)‖ ^ k}) :=
        (((isOpen_lt _).preimage continuous_fst).isClosed_compl).union
          (isClosed_le (by fun_prop) continuous_const)
      have hsub := closure_minimal (s := ((ι.prod σ).toAddMonoidHom.range : Set (K × Ω))) ?_ hcl
      · rcases hsub (hG z) with h1 | h1
        · exfalso
          apply h1
          simp only [Set.mem_setOf_eq, hz, map_zero]
          exact zero_lt_iff.2 (by simp [hl])
        · exact h1
      · rintro _ ⟨a, rfl⟩
        by_cases ha : valuation K (ι a) < valuation K ((l : K) ^ k)
        · right
          have h2 := h (a / (l : F) ^ k) (by
            rw [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.2 (by simp [hl]))]
            simpa using ha)
          rw [map_div₀, norm_div, div_le_one (by simp [hl'])] at h2
          simpa using h2
        · left; exact ha
    have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt (l := l) (Ω := Ω))) hb
    exact norm_le_zero_iff.1 this
  refine ⟨AlgHom.liftOfSurjective φ hsurj ψ (fun z hz => hker z hz), fun a => ?_⟩
  have h1 : ι a = φ (1 ⊗ₜ a) := by simp [hφ]
  rw [h1]
  exact (AlgHom.liftOfSurjective_apply φ hsurj ψ _ _).trans (by rw [hψ, one_smul])

end Ext


end GlobalTheory.LocalTraceSum
