import Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeLeOfMetricBoundedMap
import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem

section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

def tailIncl (K : Type) [Field K] (r : ℕ) : (Fin r → 𝓞 K) →ₗ[𝓞 K] (Fin (r + 1) → 𝓞 K) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [NumberField K] in
theorem coord_tail_zero (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin r → 𝓞 K)) :
    standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x) 0 = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, tailIncl]
  | add a b ha hb => simp only [map_add, PiLp.add_apply] at ha hb ⊢; rw [ha, hb, add_zero]

omit [NumberField K] in
theorem coord_tail_succ (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin r → 𝓞 K)) (j : Fin r) :
    standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x) j.succ =
      standardCoord K σ (Fin r) x j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, tailIncl]
  | add a b ha hb => simp only [map_add, PiLp.add_apply] at ha hb ⊢; rw [ha, hb]

omit [NumberField K] in
theorem coord_head (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin (r + 1) → 𝓞 K)) :
    integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x) =
      standardCoord K σ (Fin (r + 1)) x 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, integersCoord]
  | add a b ha hb => simp only [map_add] at ha hb ⊢; rw [ha, hb]; rfl

theorem coord_zero_of_orth (σ : K →+* ℂ) (r : ℕ) (v : Fibre σ (Fin (r + 1) → 𝓞 K))
    (hv : ∀ w : Fibre σ (Fin r → 𝓞 K), ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) w) v = 0) (j : Fin r) :
    standardCoord K σ (Fin (r + 1)) v j.succ = 0 := by
  have h := hv (1 ⊗ₜ Pi.single j 1)
  change inner ℂ (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) (1 ⊗ₜ Pi.single j 1)))
      (standardCoord K σ (Fin (r + 1)) v) = 0 at h
  rw [PiLp.inner_apply, Fin.sum_univ_succ] at h
  simp only [coord_tail_zero, coord_tail_succ, inner_zero_left, zero_add] at h
  simpa [standardCoord, Pi.single_apply] using h

theorem tail_iso (σ : K →+* ℂ) (r : ℕ) (x y : Fibre σ (Fin r → 𝓞 K)) :
    ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) x) ((tailIncl K r).lTensor (ComplexAt σ) y) =
      ((HermitianMetric.standard K (Fin r)).form σ).inner x y := by
  show inner ℂ (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x))
      (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) y)) =
    inner ℂ (standardCoord K σ (Fin r) x) (standardCoord K σ (Fin r) y)
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [coord_tail_zero, coord_tail_succ, inner_zero_left, zero_add]

theorem head_coiso (σ : K →+* ℂ) (r : ℕ) (x y : Fibre σ (Fin (r + 1) → 𝓞 K))
    (hy : ∀ w : Fibre σ (Fin r → 𝓞 K), ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) w) y = 0) :
    ((HermitianMetric.integers K).form σ).inner
      ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x)
      ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) y) =
      ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner x y := by
  show inner ℂ (integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x))
      (integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) y)) =
    inner ℂ (standardCoord K σ (Fin (r + 1)) x) (standardCoord K σ (Fin (r + 1)) y)
  rw [coord_head, coord_head, PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [coord_zero_of_orth σ r y hy, inner_zero_right, Finset.sum_const_zero, add_zero]

def stdExt (K : Type) [Field K] [NumberField K] (r : ℕ) :
    HermitianExtension (HermitianBundle.standard K r) (HermitianBundle.standard K (r + 1))
      (HermitianBundle.integers K) where
  incl := tailIncl K r
  proj := (LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K)
  incl_injective := fun a b h => funext fun j => congrFun h j.succ
  proj_surjective := fun a => ⟨fun _ => a, rfl⟩
  exact := by
    intro y
    constructor
    · intro hy
      refine ⟨fun j => y j.succ, funext fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (show y 0 = 0 from hy).symm
      · rfl
    · rintro ⟨a, rfl⟩
      rfl
  incl_isometric σ x y := tail_iso σ r x y
  proj_coisometric σ x y _ hy := head_coiso σ r x y hy

private theorem exists_injective_quotient_span_map {M N : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup N]
    [Module (𝓞 K) N] (φ : M →ₗ[𝓞 K] N) (hφ : Function.Injective φ) (m : M) :
    ∃ f : M ⧸ Submodule.span (𝓞 K) {m} → N ⧸ Submodule.span (𝓞 K) {φ m}, Function.Injective f := by
  have h : Submodule.span (𝓞 K) {m} ≤ (Submodule.span (𝓞 K) {φ m}).comap φ := by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap]
    exact Submodule.mem_span_singleton_self _
  refine ⟨Submodule.mapQ _ _ φ h, fun x y hxy => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hxy
  exact Submodule.mem_span_singleton.2 ⟨c, hφ (by rw [map_smul, map_sub]; exact hc)⟩

set_option maxHeartbeats 400000 in
theorem integers_deg_le (G : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) :
    (HermitianBundle.integers K).degree G ≤ 0 := by
  by_cases hG : G = ⊥
  · rw [hG, HermitianBundle.degree_bot]
  obtain ⟨a, haG, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG
  let sG : Fin 1 → G := fun _ => ⟨a, haG⟩
  let sT : Fin 1 → (⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) :=
    fun _ => ⟨a, Submodule.mem_top⟩
  have liG : LinearIndependent (𝓞 K) sG :=
    linearIndependent_unique_iff.2 (fun h => ha0 (congrArg Subtype.val h))
  have liT : LinearIndependent (𝓞 K) sT :=
    linearIndependent_unique_iff.2 (fun h => ha0 (congrArg Subtype.val h))
  have rT : (HermitianBundle.integers K).rank ⊤ = 1 := by
    show Module.finrank (𝓞 K) (⊤ : Submodule (𝓞 K) (𝓞 K)) = 1
    rw [finrank_top, Module.finrank_self]
  have rG : (HermitianBundle.integers K).rank G = 1 := by
    refine le_antisymm ?_ ?_
    · show Module.finrank (𝓞 K) G ≤ 1
      calc Module.finrank (𝓞 K) G ≤ Module.finrank (𝓞 K) (𝓞 K) := Submodule.finrank_le G
        _ = 1 := Module.finrank_self _
    · have h := liG.fintype_card_le_finrank
      rw [Fintype.card_fin] at h
      exact h
  have hGd := (HermitianBundle.integers K).degree_eq_of_linearIndependent G liG (by simp [rG])
  have hTd := (HermitianBundle.integers K).degree_eq_of_linearIndependent ⊤ liT (by simp [rT])
  have hT0 : (HermitianBundle.integers K).degree ⊤ = 0 := by
    rw [HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.arithDegree_integers]
  have hsame : (fun i => (sG i : (HermitianBundle.integers K).carrier)) =
      fun i => (sT i : (HermitianBundle.integers K).carrier) := rfl
  rw [hsame] at hGd
  rw [Set.range_const] at hGd hTd
  have hfin : Finite (𝓞 K ⧸ Ideal.span {(show 𝓞 K from a)}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by rw [Ne, Ideal.span_singleton_eq_bot]; exact ha0)
  obtain ⟨f1, hf1⟩ := exists_injective_quotient_span_map
    (⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier).subtype Subtype.val_injective (sT 0)
  obtain ⟨f2, hf2⟩ := exists_injective_quotient_span_map (Submodule.inclusion (le_top : G ≤ ⊤))
    (Submodule.inclusion_injective _) (sG 0)
  have hfinT : Finite ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
      Submodule.span (𝓞 K) {sT 0}) := by
    have : Finite ((HermitianBundle.integers K).carrier ⧸ Submodule.span (𝓞 K)
      {((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier).subtype (sT 0))}) := hfin
    exact Finite.of_injective f1 hf1
  have hfinT' : Finite ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
      Submodule.span (𝓞 K) {Submodule.inclusion (le_top : G ≤ ⊤) (sG 0)}) := hfinT
  have hfinG : Finite (G ⧸ Submodule.span (𝓞 K) {sG 0}) := Finite.of_injective f2 hf2
  have hle : Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) ≤
      Nat.card ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
        Submodule.span (𝓞 K) {sT 0}) :=
    Nat.card_le_card_of_injective f2 hf2
  have hpos : 0 < Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) := Nat.card_pos
  have hlog := Real.log_le_log (by exact_mod_cast hpos)
    (Nat.cast_le.2 hle : (Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) : ℝ) ≤ _)
  have e1 : (HermitianBundle.integers K).degree G =
      Real.log (Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0})) -
        1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet (HermitianBundle.integers K).metric σ
          fun i => (sT i : (HermitianBundle.integers K).carrier)) := hGd
  have e2 : (HermitianBundle.integers K).degree ⊤ =
      Real.log (Nat.card ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
        Submodule.span (𝓞 K) {sT 0})) -
        1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet (HermitianBundle.integers K).metric σ
          fun i => (sT i : (HermitianBundle.integers K).carrier)) := hTd
  linarith

theorem std_deg (r : ℕ) : (∀ F, (HermitianBundle.standard K r).degree F ≤ 0) ∧
    (HermitianBundle.standard K r).degree ⊤ = 0 := by
  induction r with
  | zero =>
    have hs : ∀ F : Submodule (𝓞 K) (HermitianBundle.standard K 0).carrier, F = ⊥ := by
      intro F
      refine (Submodule.eq_bot_iff F).2 fun x _ => ?_
      show (x : Fin 0 → 𝓞 K) = 0
      funext i
      exact i.elim0
    refine ⟨fun F => ?_, ?_⟩
    · rw [hs F, HermitianBundle.degree_bot]
    · rw [hs ⊤, HermitianBundle.degree_bot]
  | succ r ih =>
    refine ⟨fun F => ?_, ?_⟩
    · have h1 := ih.1 (Submodule.comap (stdExt K r).incl F)
      have h2 := integers_deg_le (Submodule.map (stdExt K r).proj F)
      have h3 := (stdExt K r).degree_submodule_le F
      linarith
    · rw [HermitianBundle.degree_top_eq_arithDegree, (stdExt K r).arithDegree_eq_add,
        ← HermitianBundle.degree_top_eq_arithDegree, ih.2, HermitianBundle.arithDegree_integers, add_zero]

theorem standard_hermitian_bundle_semistable : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ), (HermitianBundle.standard K r).slopeMax ≤ 0 ∧ (HermitianBundle.standard K r).normDegree ⊤ = 0 := by
  intro K _ _ r
  have h := std_deg (K := K) r
  refine ⟨?_, ?_⟩
  · refine iSup_le fun F => iSup_le fun _ => ?_
    have hF : HermitianBundle.slope _ F ≤ 0 := by
      unfold HermitianBundle.slope HermitianBundle.normDegree
      refine div_nonpos_iff.2 (Or.inr ⟨div_nonpos_iff.2 (Or.inr ⟨h.1 F, by positivity⟩), by positivity⟩)
    exact_mod_cast hF
  · simp [HermitianBundle.normDegree, h.2]

end CoverDenseAlt
end

section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

theorem sqAt_std (r : ℕ) (σ : K →+* ℂ) (y : Fibre σ (Fin r → 𝓞 K)) :
    sqAt (HermitianBundle.standard K r) σ y = ∑ a, ‖standardCoord K σ (Fin r) y a‖ ^ 2 := by
  have h := HermitianMetric.standard_inner K (Fin r) σ y y
  unfold sqAt
  erw [h]
  simp only [Complex.conj_mul', Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

omit [NumberField K] in
theorem sum_coord {M : Type} [AddCommGroup M] [Module (𝓞 K) M] {r : ℕ}
    (b : Module.Basis (Fin r) (𝓞 K) M) (σ : K →+* ℂ) (y : Fibre σ (Fin r → 𝓞 K)) :
    ∑ a, ComplexAt.ofComplex σ (standardCoord K σ (Fin r) y a) ⊗ₜ[𝓞 K] b a =
      b.equivFun.symm.toLinearMap.lTensor (ComplexAt σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul z f =>
    have hc : ∀ a, ComplexAt.ofComplex σ (standardCoord K σ (Fin r) (z ⊗ₜ f) a) = f a • z := by
      intro a
      simp [standardCoord]
    simp only [hc, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    simp only [map_add, WithLp.ofLp_add, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

theorem slopeMax_le_of_comparable_metric : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C := by
  intro K _ _ E r b C hC h
  have hC0 : 0 < C := by linarith
  let φ : E.carrier →ₗ[𝓞 K] (HermitianBundle.standard K r).carrier := b.equivFun.toLinearMap
  let ψ : (HermitianBundle.standard K r).carrier →ₗ[𝓞 K] E.carrier := b.equivFun.symm.toLinearMap
  have hb : ∀ (σ : K →+* ℂ) (y : Fibre σ (HermitianBundle.standard K r).carrier),
      C⁻¹ * sqAt (HermitianBundle.standard K r) σ y ≤ sqAt E σ (ψ.lTensor (ComplexAt σ) y) ∧
      sqAt E σ (ψ.lTensor (ComplexAt σ) y) ≤ C * sqAt (HermitianBundle.standard K r) σ y := by
    intro σ y
    have := h σ fun a => standardCoord K σ (Fin r) y a
    rw [sum_coord b σ y, ← sqAt_std r σ y] at this
    exact this
  have hψφ : ψ ∘ₗ φ = LinearMap.id := LinearMap.ext fun x => b.equivFun.symm_apply_apply x
  have h1 := normDegree_le_of_metric_bounded_map K E (HermitianBundle.standard K r) φ C b.equivFun.injective hC0 (fun σ x => by
    have := (hb σ (φ.lTensor (ComplexAt σ) x)).1
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hψφ, LinearMap.lTensor_id,
      LinearMap.id_apply, inv_mul_le_iff₀ hC0] at this
    exact this)
  have h2 := normDegree_le_of_metric_bounded_map K (HermitianBundle.standard K r) E ψ C b.equivFun.symm.injective hC0
    fun σ y => (hb σ y).2
  obtain ⟨s1, s2⟩ := standard_hermitian_bundle_semistable K r
  refine ⟨h1.2.trans ?_, ?_⟩
  · refine (add_le_add_left s1 _).trans ?_
    rw [zero_add]
  · have a := h1.1 ⊤
    have c := h2.1 ⊤
    have e1 : (⊤ : Submodule (𝓞 K) E.carrier).map φ = ⊤ := by
      rw [Submodule.map_top]; exact LinearMap.range_eq_top.mpr b.equivFun.surjective
    have e2 : (⊤ : Submodule (𝓞 K) (HermitianBundle.standard K r).carrier).map ψ = ⊤ := by
      rw [Submodule.map_top]; exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective
    have r1 : E.rank ⊤ = r := by
      rw [HermitianBundle.rank, finrank_top, Module.finrank_eq_card_basis b, Fintype.card_fin]
    have r2 : (HermitianBundle.standard K r).rank ⊤ = r := by
      rw [HermitianBundle.rank, finrank_top]
      exact Module.finrank_fin_fun (𝓞 K)
    rw [e1, s2, r1] at a
    rw [e2, s2, r2] at c
    rw [abs_le]
    constructor <;> linarith

end CoverDenseAlt
end
