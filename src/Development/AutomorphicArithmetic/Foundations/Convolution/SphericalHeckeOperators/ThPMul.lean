import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoVol

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem integral_conv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {f₁ f₂ : G → ℂ}
    (h₁ : HasCompactSupport f₁) (h₂ : HasCompactSupport f₂)
    (r₁ : ∀ g, ∀ k ∈ K, f₁ (g * k) = f₁ g) (l₂ : ∀ g, ∀ k ∈ K, f₂ (k * g) = f₂ g)
    (r₂ : ∀ g, ∀ k ∈ K, f₂ (g * k) = f₂ g) :
    ∫ x, groupConv μ f₁ f₂ x ∂μ = (∫ x, f₁ x ∂μ) * ∫ x, f₂ x ∂μ := by
  have key := integral_integral_swap_of_coset μ K hK (F := fun y z => f₁ y * f₂ (y⁻¹ * z))
    h₁ (h₁.mul h₂) ?_ ?_ ?_
  · simp only [groupConv]
    rw [← key, ← integral_mul_const]
    congr 1
    funext y
    rw [integral_const_mul, integral_mul_left_eq_self f₂ y⁻¹]
  · intro y z h
    have h' := mul_ne_zero_iff.1 h
    exact ⟨subset_tsupport _ h'.1, y, subset_tsupport _ h'.1, y⁻¹ * z, subset_tsupport _ h'.2,
      mul_inv_cancel_left y z⟩
  · intro y z k hk
    simp only [r₁ y k hk, mul_inv_rev, mul_assoc, l₂ _ _ (inv_mem hk)]
  · intro y z k hk
    simp only [← mul_assoc, r₂ _ k hk]

private theorem meas_dco {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] {a : Fin n → ℤ} (ha : Antitone a) :
    MeasurableSet (dco F a) := by
  have h := ((dcoShape F n a ha).2.2.1.1.isOpen_fiber 1).measurableSet
  convert h using 1
  ext g
  by_cases hg : g ∈ dco F a <;> simp [uFn, hg]

private theorem int_uFn {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) {a : Fin n → ℤ}
    (ha : Antitone a) : ∫ x, uFn F a x ∂μ = (μ.real (dco F a) : ℂ) := by
  have := integral_indicator_const (μ := μ) (1 : ℂ) (meas_dco (F := F) ha)
  rw [Complex.real_smul, mul_one] at this
  exact this

theorem UpperTheory.ConvolutionTheory.H.thMul :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (a b : Fin n → ℤ), Antitone a → Antitone b →
      groupConv μ (th μ a) (th μ b) = th μ (a + b) := by
  intro F _ _ _ _ n _ _ μ _ a b ha hb
  have hab : Antitone (a + b) := ha.add hb
  obtain ⟨-, hmul, hca, hIa⟩ := dcoShape F n a ha
  obtain ⟨-, -, hcb, hIb⟩ := dcoShape F n b hb
  let K : OpenSubgroup (GL (Fin n) F) := ⟨iwahori F n, isOpen_iwahori F n⟩
  have hKc : IsCompact (K : Set (GL (Fin n) F)) :=
    isCompact_iwahori F n
  have hI : (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 := by
    have h1 : μ (K : Set (GL (Fin n) F)) ≠ 0 := K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h1, hKc.measure_lt_top.ne⟩)
  set φ := groupConv μ (uFn F a) (uFn F b) with hφ
  have hl : ∀ g, ∀ y ∈ iwahori F n, φ (y * g) = φ g := by
    intro g y hy
    simp only [hφ, groupConv]
    rw [← integral_mul_left_eq_self _ y]
    congr 1
    funext x
    rw [(hIa x y hy).1, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hr : ∀ g, ∀ y ∈ iwahori F n, φ (g * y) = φ g := fun g y hy =>
    groupConv_mul_right (fun g => (hIb g y hy).2) g
  have hφe : φ = φ (torusPow F n (a + b)) • uFn F (a + b) := by
    funext g
    by_cases hg : g ∈ dco F (a + b)
    · rw [Pi.smul_apply, uFn, Set.indicator_of_mem hg, Pi.one_apply, smul_eq_mul, mul_one]
      obtain ⟨x, hx, y, hy, rfl⟩ := hg
      rw [hr _ y hy, hl _ x hx]
    · rw [Pi.smul_apply, uFn, Set.indicator_of_notMem hg, smul_zero]
      have : ∀ y, uFn F a y * uFn F b (y⁻¹ * g) = 0 := by
        intro y
        by_contra h
        have h' := mul_ne_zero_iff.1 h
        have := hmul b hb _ (Set.mem_of_indicator_ne_zero h'.1) _ (Set.mem_of_indicator_ne_zero h'.2)
        rw [mul_inv_cancel_left] at this
        exact hg this
      simp only [hφ, groupConv, this, integral_zero]
  set c := φ (torusPow F n (a + b)) with hc
  have hint : c * (μ.real (dco F (a + b)) : ℂ) = (μ.real (dco F a) : ℂ) * (μ.real (dco F b) : ℂ) := by
    have h := integral_conv μ K hKc hca.2 hcb.2 (fun g k hk => (hIa g k hk).2)
      (fun g k hk => (hIb g k hk).1) (fun g k hk => (hIb g k hk).2)
    rw [int_uFn μ ha, int_uFn μ hb, ← hφ] at h
    rw [← h, ← int_uFn μ hab, ← integral_const_mul, hφe]
    rfl
  have va := dcoVol F n μ a ha
  have vb := dcoVol F n μ b hb
  have vab := dcoVol F n μ (a + b) hab
  rw [halfModulus_add] at vab
  have hcI : c = (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) := by
    apply mul_right_cancel₀ hI
    calc c * _ = c * ((halfModulus F a * halfModulus F b) ^ 2 * (μ.real (dco F (a + b)) : ℂ)) := by rw [vab]
      _ = (halfModulus F a * halfModulus F b) ^ 2 * (c * (μ.real (dco F (a + b)) : ℂ)) := by ring
      _ = (halfModulus F a ^ 2 * (μ.real (dco F a) : ℂ)) * (halfModulus F b ^ 2 * (μ.real (dco F b) : ℂ)) := by
        rw [hint]; ring
      _ = _ := by rw [va, vb]
  funext g
  have e : groupConv μ (th μ a) (th μ b) g =
      (halfModulus F a / (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ)) *
        (halfModulus F b / (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ)) * φ g := by
    simp only [hφ, groupConv, th, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [e, hφe, hcI, th, halfModulus_add]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem groupConv_sum_sum {G ι κ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (S : Finset ι) (T : Finset κ) (c : ι → ℂ) (d : κ → ℂ) (f : ι → G → ℂ) (g : κ → G → ℂ)
    (hf : ∀ i ∈ S, f i ∈ locallyConstantCompactSupport G ℂ ℂ)
    (hg : ∀ j ∈ T, g j ∈ locallyConstantCompactSupport G ℂ ℂ) :
    groupConv μ (∑ i ∈ S, c i • f i) (∑ j ∈ T, d j • g j) =
      ∑ i ∈ S, ∑ j ∈ T, (c i * d j) • groupConv μ (f i) (g j) := by
  funext x
  have hint : ∀ i ∈ S, ∀ j ∈ T,
      Integrable (fun y => (c i * d j) * (f i y * g j (y⁻¹ * x))) μ := fun i hi j hj =>
    (integrable_mul_of_mem (hf i hi)
      ((hg j hj).1.continuous.comp (continuous_inv.mul continuous_const))).const_mul _
  have h1 : ∀ y, (∑ i ∈ S, c i • f i) y * (∑ j ∈ T, d j • g j) (y⁻¹ * x) =
      ∑ i ∈ S, ∑ j ∈ T, (c i * d j) * (f i y * g j (y⁻¹ * x)) := by
    intro y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [groupConv, h1]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => hint i hi j hj]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun j hj => hint i hi j hj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

theorem UpperTheory.ConvolutionTheory.H.thPMul :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (r s : LaurentRing n), Dom r → Dom s →
      Dom (r * s) ∧ thP μ r ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ ∧ BiI F (thP μ r) ∧ groupConv μ (thP μ r) (thP μ s) = thP μ (r * s) := by
  intro F _ _ _ _ n _ _ μ _ r s hr hs
  classical
  have hth : ∀ a : Fin n → ℤ, Antitone a →
      th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := fun a ha =>
    Submodule.smul_mem _ _ (dcoShape F n a ha).2.2.1
  refine ⟨fun a ha => ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, c, hc, rfl⟩ :=
      Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset r s ha)
    exact (hr b hb).add (hs c hc)
  · exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (hth a (hr a ha))
  · intro g y hy
    simp only [thP, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, th]
    constructor
    · exact Finset.sum_congr rfl fun a ha => by
        rw [((dcoShape F n a (hr a ha)).2.2.2 g y hy).1]
    · exact Finset.sum_congr rfl fun a ha => by
        rw [((dcoShape F n a (hr a ha)).2.2.2 g y hy).2]
  · have hz : ∀ a : Fin n → ℤ, (0 : ℂ) • th μ a = 0 := fun a => zero_smul _ _
    have ha : ∀ (a : Fin n → ℤ) (c d : ℂ), (c + d) • th μ a = c • th μ a + d • th μ a :=
      fun a c d => add_smul _ _ _
    have h1 : thP μ (r * s) = ∑ a ∈ r.coeff.support, ∑ b ∈ s.coeff.support,
        (r.coeff a * s.coeff b) • th μ (a + b) := by
      unfold thP
      rw [AddMonoidAlgebra.mul_def]
      simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single]
      rw [Finsupp.sum_sum_index hz ha]
      refine Finset.sum_congr rfl fun a _ => ?_
      beta_reduce
      rw [Finsupp.sum_sum_index hz ha]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact Finsupp.sum_single_index (hz _)
    rw [h1]
    unfold thP Finsupp.sum
    rw [groupConv_sum_sum μ _ _ _ _ _ _ (fun a ha => hth a (hr a ha)) (fun b hb => hth b (hs b hb))]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [thMul F n μ a b (hr a ha) (hs b hb)]
end
