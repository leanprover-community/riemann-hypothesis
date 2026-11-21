import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConvolutionL2Class
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLatticeGLConjLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.latCount :
    UpperTheory.V.Cj.H.LatCount := by
  intro E _ _ _ a _ S hS g
  obtain ⟨A, hA⟩ := GlobalTheory.card_latticeGL_conj_le E a
  set c : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g with hc
  set f : GA E a := finGL E a (GeneralLinearGroup.map (pFin E) g) with hf
  obtain ⟨C, hC0, hC⟩ := hA ((fun s => f * s * f⁻¹) '' S) (hS.image (by fun_prop))
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c))
  refine ⟨C * B ^ (2 * A), 2 * A, fun y => ?_⟩
  obtain ⟨hfin, hle⟩ := hC (c * y)
  have hg : g * infGL E a y = infGL E a (c * y) * f := by
    refine ga_ext ?_ ?_
    · simp only [map_mul, hf, pInf_infGL, pInf_finGL, mul_one, hc]
    · simp only [map_mul, hf, pFin_infGL, pFin_finGL, mul_one, one_mul]
  refine ⟨_, hle.trans ?_, ?_⟩
  · have h0 : 0 ≤ GlobalTheory.CuspRep.height (c * y) := zero_le_one.trans (one_le_height _)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hB c rfl y) _) hC0
  · rw [hfin.cast_ncard_eq]
    refine Set.encard_le_encard fun γ hγ => ⟨_, hγ, ?_⟩
    rw [hg]
    group
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.cvGrow :
    UpperTheory.V.Cj.H.CvGrow := by
  intro E _ _ _ a ha μ _ _ ψ hψc hψs F g
  obtain ⟨B, hB0, hB⟩ := cvCount (GA E a) (latticeGL E a) μ ψ hψc hψs
  have hKc : IsCompact (tsupport ψ) := hψs.isCompact
  obtain ⟨C, N, hC⟩ := latCount E a ha ((tsupport ψ)⁻¹ * tsupport ψ) (hKc.inv.mul hKc) g
  refine ⟨B * ‖F‖ * C, N, fun y => ?_⟩
  obtain ⟨M, hM, hcard⟩ := hC y
  have key : ∀ h : GA E a,
      {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.encard ≤ (M : ℕ∞) := by
    intro h
    by_cases hne : {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.Nonempty
    · obtain ⟨γ₀, hγ₀⟩ := hne
      refine le_trans (Set.encard_le_encard_of_injOn (f := fun γ => γ * γ₀⁻¹) ?_ ?_) hcard
      · intro γ hγ
        simp only [Set.mem_setOf_eq] at hγ hγ₀ ⊢
        have h₁ := subset_tsupport ψ hγ
        have h₂ := subset_tsupport ψ hγ₀
        have e : (g * infGL E a y)⁻¹ * ↑(γ * γ₀⁻¹) * (g * infGL E a y)
            = ((↑γ * h)⁻¹ * (g * infGL E a y))⁻¹ * ((↑γ₀ * h)⁻¹ * (g * infGL E a y)) := by
          push_cast
          group
        rw [e]
        exact Set.mul_mem_mul (Set.inv_mem_inv.mpr h₁) h₂
      · intro γ _ δ _ hγδ
        simpa using hγδ
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hx := hB (g * infGL E a y) M key F
  calc ‖cv ψ F (g * infGL E a y)‖ ≤ B * M * ‖F‖ := hx
    _ = B * ‖F‖ * M := by ring
    _ ≤ B * ‖F‖ * (C * height y ^ N) :=
        mul_le_mul_of_nonneg_left hM (mul_nonneg hB0 (norm_nonneg _))
    _ = B * ‖F‖ * C * height y ^ N := by ring
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.cvAlg :
    UpperTheory.V.Cj.H.CvAlg := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs
  obtain ⟨hloc, hcnt⟩ := locInt G Γ μ
  obtain ⟨B, hB, hbd⟩ := cvCount G Γ μ ψ hψ hψs
  have hint : ∀ (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (x : G),
      MeasureTheory.Integrable (fun y ↦ GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) μ := by
    intro F x
    have hc : Continuous fun y : G ↦ ψ (y⁻¹ * x) :=
      hψ.comp (continuous_inv.mul continuous_const)
    have hs : HasCompactSupport fun y : G ↦ ψ (y⁻¹ * x) :=
      hψs.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
    simpa [smul_eq_mul] using (hloc F).integrable_smul_right_of_hasCompactSupport hc hs
  refine ⟨hint, ?_, ?_, ?_⟩
  · intro F F' s t
    funext x
    have hae : ∀ᵐ y ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑(s • F + t • F')) y
        = s * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y + t * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y := by
      have h := Filter.Eventually.and (MeasureTheory.Lp.coeFn_add (s • F) (t • F'))
        (Filter.Eventually.and (MeasureTheory.Lp.coeFn_smul s F)
          (MeasureTheory.Lp.coeFn_smul t F'))
      have h' := (GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff (μ := μ)).1 h
      filter_upwards [h'] with y hy
      obtain ⟨e1, e2, e3⟩ := hy
      simp only [GlobalTheory.AutomorphicL2Unitary.lift]
      rw [e1, Pi.add_apply, e2, e3]
      simp [smul_eq_mul]
    calc cv ψ (s • F + t • F') x
        = ∫ y, (s * (GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x))
            + t * (GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y * ψ (y⁻¹ * x))) ∂μ := by
          unfold UpperTheory.V.Cj.H.cv
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hae] with y hy
          rw [hy]
          ring
      _ = (s • cv ψ F + t • cv ψ F') x := by
          rw [MeasureTheory.integral_add ((hint F x).const_mul s) ((hint F' x).const_mul t),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          simp [UpperTheory.V.Cj.H.cv, smul_eq_mul]
  · intro F γ hγ g
    unfold UpperTheory.V.Cj.H.cv
    rw [← MeasureTheory.integral_mul_left_eq_self _ γ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [GlobalTheory.AutomorphicL2Unitary.leftInv_lift _ γ hγ y, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · intro C hC
    have hK : IsCompact (tsupport ψ) := hψs
    obtain ⟨N, hN⟩ := hcnt (C * (tsupport ψ)⁻¹) (hC.mul hK.inv)
    refine ⟨B * (N : ℝ), fun F x hx ↦ ?_⟩
    refine hbd x N (fun g ↦ le_trans (Set.encard_le_encard ?_) (hN g)) F
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ ⊢
    have hmem : ((γ : G) * g)⁻¹ * x ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hγ)
    have heq : (γ : G) * g = x * (((γ : G) * g)⁻¹ * x)⁻¹ := by group
    rw [heq]
    exact Set.mul_mem_mul hx (Set.inv_mem_inv.2 hmem)
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem hasDerivAt_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f ψ ψ' : G → ℂ) (hf : LocallyIntegrable f μ)
    (h' : Continuous ψ') (hs' : HasCompactSupport ψ')
    (hi : ∀ x, Integrable (fun y => f y * ψ (y⁻¹ * x)) μ) (hi' : ∀ x, Integrable (fun y => f y * ψ' (y⁻¹ * x)) μ)
    (c : ℝ → G) (hc : Continuous c) (c0 : c 0 = 1) (cadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => ψ (g * c t)) (ψ' g) 0) (x : G) :
    HasDerivAt (fun t => ∫ y, f y * ψ (y⁻¹ * (x * c t)) ∂μ) (∫ y, f y * ψ' (y⁻¹ * x) ∂μ) 0 := by
  obtain ⟨M, hM⟩ := h'.bounded_above_of_compact_support hs'
  let K : Set G := (fun p : ℝ × G => x * c p.1 * p.2⁻¹) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport ψ')
  have hK : IsCompact K := (isCompact_Icc.prod hs').image (by fun_prop)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hb : Integrable (K.indicator fun y => ‖f y‖ * M) μ :=
    (integrable_indicator_iff hKm).2 ((hf.integrableOn_isCompact hK).norm.mul_const M)
  have hdt : ∀ g t, HasDerivAt (fun s => ψ (g * c s)) (ψ' (g * c t)) t := fun g t => by
    have h1 : HasDerivAt (fun s => ψ (g * c t * c s)) (ψ' (g * c t)) (t - t) := by
      rw [sub_self]; exact hd _
    have h2 := h1.comp_sub_const t t
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← cadd, add_sub_cancel]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun t y => f y * ψ (y⁻¹ * (x * c t))) (F' := fun t y => f y * ψ' (y⁻¹ * (x * c t)))
    (x₀ := (0 : ℝ)) (s := Set.Icc (-1 : ℝ) 1) (bound := K.indicator fun y => ‖f y‖ * M)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hi _).aestronglyMeasurable) (hi _) (hi' _).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hy]
        have : ψ' (y⁻¹ * (x * c t)) = 0 := by
          by_contra hne
          exact hy ⟨(t, y⁻¹ * (x * c t)), ⟨ht, subset_tsupport _ hne⟩, by simp [mul_assoc]⟩
        simp [this]) hb
    (Eventually.of_forall fun y t _ => by
      simpa only [mul_assoc] using (hdt (y⁻¹ * x) t).const_mul (f y))
  simpa only [c0, mul_one] using key.2

theorem UpperTheory.V.Cj.H.cvLie :
    UpperTheory.V.Cj.H.CvLie := by
  intro E _ _ _ a μ _ _ ψ φ hψ F hφ X
  obtain ⟨c, c0, cadd, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have t1 := UpperTheory.V.Cj.H.testOps E a ψ
  have hψ' : IsTest (lie E a X ψ) := (t1.2 hψ).1 X
  have k1 : Continuous ψ.1 := (t1.1 hψ.2).1
  have k2 : Continuous (lie E a X ψ).1 := ((UpperTheory.V.Cj.H.testOps E a _).1 hψ'.2).1
  funext x
  have d := hasDerivAt_conv μ (GlobalTheory.AutomorphicL2Unitary.lift (latticeGL E a) F) ψ.1 (lie E a X ψ).1
    ((UpperTheory.V.Cj.H.locInt (GA E a) (latticeGL E a) μ).1 F) k2 hψ'.1
    ((UpperTheory.V.Cj.H.cvAlg (GA E a) (latticeGL E a) μ ψ.1 k1 hψ.1).1 F)
    ((UpperTheory.V.Cj.H.cvAlg (GA E a) (latticeGL E a) μ _ k2 hψ'.1).1 F)
    (fun s => infGL E a (c s)) ccont (by rw [c0, map_one]) (fun s t => by rw [cadd, map_mul])
    (fun g => hasDerivAt_curve ψ g c X c0 cder) x
  have d' := hasDerivAt_curve φ x c X c0 cder
  exact d'.unique (d.congr_of_eventuallyEq (Eventually.of_forall fun t => congrFun hφ _))
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem grow_lin {φ ψ : GA E a → ℂ} (hφ : Grow φ) (hψ : Grow ψ) : Grow (φ + ψ) := by
  intro g
  obtain ⟨C, N, h⟩ := hφ g
  obtain ⟨C', N', h'⟩ := hψ g
  refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
  have h1 := GlobalTheory.CuspRep.one_le_height y
  have h0 : 0 ≤ GlobalTheory.CuspRep.height y := zero_le_one.trans h1
  have e1 : C * GlobalTheory.CuspRep.height y ^ N ≤ |C| * GlobalTheory.CuspRep.height y ^ (N + N') :=
    mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right _ _)) (pow_nonneg h0 _) (abs_nonneg C)
  have e2 : C' * GlobalTheory.CuspRep.height y ^ N' ≤ |C'| * GlobalTheory.CuspRep.height y ^ (N + N') :=
    mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left _ _)) (pow_nonneg h0 _) (abs_nonneg C')
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add ((h y).trans e1) ((h' y).trans e2))

private theorem grow_smul (s : ℂ) {φ : GA E a → ℂ} (hφ : Grow φ) : Grow (s • φ) := by
  intro g
  obtain ⟨C, N, h⟩ := hφ g
  refine ⟨‖s‖ * C, N, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg s)

private theorem lev_of {φ : Sm E a} {S : Set (GL (Fin a) (Af E))} (hS : S ∈ 𝓝 1)
    (h : ∀ k ∈ S, act (.fin k) φ = φ) : HasLev φ :=
  isOpen_stab_of_mem_nhds (finRep E a) φ (Filter.mem_of_superset hS h)

private theorem lev_nhds {φ : Sm E a} (h : HasLev φ) : {k : GL (Fin a) (Af E) | act (.fin k) φ = φ} ∈ 𝓝 1 := by
  refine h.mem_nhds ?_
  change finRep E a 1 φ = φ
  rw [map_one]; rfl

private theorem rt_cv (μ : Measure (GA E a)) {φ ψ : Sm E a} {F : HL μ} (e : φ.1 = cv ψ.1 F) (g : GA E a) :
    (rt E a g φ).1 = cv (rt E a g ψ).1 F := by
  funext x
  change φ.1 (x * g) = ∫ y, GlobalTheory.AutomorphicL2Unitary.lift _ F y * ψ.1 (y⁻¹ * x * g) ∂μ
  rw [e]
  simp only [cv, mul_assoc]

end

theorem UpperTheory.V.Cj.H.gardFacts :
    UpperTheory.V.Cj.H.GardFacts := by
  intro E _ _ _ a ha μ _ _ φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, e⟩ := h
    obtain ⟨t1, t2⟩ := testOps E a ψ
    have hc : Continuous ψ.1 := (t1 hψ.2).1
    refine ⟨lev_of (lev_nhds hψ.2) fun k hk => ?_, ?_, ?_, fun X => ?_, fun g => ?_⟩
    · have hk' : rt E a (finGL E a k) ψ = ψ := hk
      apply Subtype.ext
      change (rt E a (finGL E a k) φ).1 = φ.1
      rw [rt_cv μ e, hk', e]
    · obtain ⟨h, -⟩ := convolution_L2_class (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1 F
      unfold InL
      rw [e]
      exact h
    · rw [e]
      exact cvGrow E a ha μ ψ.1 hc hψ.1 F
    · exact Submodule.subset_span ⟨_, F, (t2 hψ).1 X, cvLie E a μ ψ φ hψ F e X⟩
    · exact Submodule.subset_span ⟨_, F, (t2 hψ).2 g, rt_cv μ e g⟩
  | zero =>
    refine ⟨lev_of Filter.univ_mem fun k _ => map_zero _, ⟨fun _ _ _ => rfl, ?_⟩, fun g => ⟨0, 0, fun y => by simp⟩,
      fun X => by rw [map_zero]; exact zero_mem _, fun g => by rw [map_zero]; exact zero_mem _⟩
    exact MemLp.zero
  | add φ ψ _ _ h h' =>
    refine ⟨lev_of (Filter.inter_mem (lev_nhds h.1) (lev_nhds h'.1)) fun k hk => ?_, ?_, grow_lin h.2.2.1 h'.2.2.1,
      fun X => by rw [map_add]; exact add_mem (h.2.2.2.1 X) (h'.2.2.2.1 X),
      fun g => by rw [map_add]; exact add_mem (h.2.2.2.2 g) (h'.2.2.2.2 g)⟩
    · rw [map_add, hk.1, hk.2]
    · simpa only [one_smul] using ((clFacts E a μ).1 φ ψ 1 1 h.2.1 h'.2.1).1
  | smul s φ _ h =>
    refine ⟨lev_of (lev_nhds h.1) fun k hk => ?_, ?_, grow_smul s h.2.2.1,
      fun X => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.1 X),
      fun g => by rw [map_smul]; exact Submodule.smul_mem _ s (h.2.2.2.2 g)⟩
    · rw [map_smul, hk]
    · simpa only [zero_smul, add_zero] using ((clFacts E a μ).1 φ φ s 0 h.2.1 h.2.1).1
end
