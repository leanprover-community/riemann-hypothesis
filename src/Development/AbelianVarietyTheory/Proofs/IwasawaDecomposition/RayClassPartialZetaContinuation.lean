import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
import BuildAid.ForwardExisting

section
section
open Complex Filter Asymptotics
open scoped RealInnerProductSpace

namespace GlobalTheory.PlaneTheta

theorem exists_pos_le_of_summable {ι : Type*} {q : ι → ℝ}
    (h : Summable fun i => Real.exp (-q i)) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, 0 < q i → δ ≤ q i := by
  have h1 := h.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-1)))
  rw [Filter.eventually_cofinite] at h1
  have h2 : {i | ¬ Real.exp (-q i) < Real.exp (-1) ∧ 0 < q i}.Finite := h1.subset fun i hi => hi.1
  have h3 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i ∈ {i | ¬ Real.exp (-q i) < Real.exp (-1) ∧ 0 < q i}, δ < q i :=
    (Filter.eventually_all_finite h2).2 fun i hi => nhdsWithin_le_nhds (gt_mem_nhds hi.2)
  have h4 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  obtain ⟨δ, ⟨h5, h6⟩, h7⟩ := ((h3.and h4).and self_mem_nhdsWithin).exists
  refine ⟨δ, h7, fun i hi => ?_⟩
  by_cases hc : Real.exp (-q i) < Real.exp (-1)
  · rw [Real.exp_lt_exp] at hc
    linarith
  · exact (h5 i ⟨hc, hi⟩).le

theorem abs_tsum_le {ι : Type*} {q f : ι → ℝ} {δ s : ℝ} (hs : 1 ≤ s)
    (h : Summable fun i => Real.exp (-q i)) (hf : ∀ i, |f i| ≤ Real.exp (-(s * q i)))
    (hδ : ∀ i, f i ≠ 0 → δ ≤ q i) :
    |∑' i, f i| ≤ (Real.exp δ * ∑' i, Real.exp (-q i)) * Real.exp (-δ * s) := by
  have hb : ∀ i, ‖f i‖ ≤ Real.exp δ * Real.exp (-q i) * Real.exp (-δ * s) := by
    intro i
    by_cases h0 : f i = 0
    · rw [h0, norm_zero]; positivity
    · refine (hf i).trans ?_
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [hδ i h0]
  have := tsum_of_norm_bounded ((h.hasSum.mul_left (Real.exp δ)).mul_right (Real.exp (-δ * s))) hb
  exact this

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem atTop_bound (u : E) (hu : ∀ x : L, (x : E) + u ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      =O[atTop] (fun t => Real.exp (-c * t)) := by
  have h : Summable fun x : L => Real.exp (-(Real.pi * ‖(x : E) + u‖ ^ 2)) := by
    simpa only [neg_mul] using summable_lattice_exp_neg_mul_norm_add_sq L Real.pi_pos u
  obtain ⟨δ, hδ, hq⟩ := exists_pos_le_of_summable h
  refine ⟨δ, hδ, IsBigO.of_bound (Real.exp δ * ∑' x : L, Real.exp (-(Real.pi * ‖(x : E) + u‖ ^ 2))) ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  refine abs_tsum_le ht h (fun x => ?_) (fun x _ => hq x ?_)
  · rw [abs_of_pos (Real.exp_pos _)]
    apply le_of_eq; congr 1; ring
  · have := norm_pos_iff.2 (hu x)
    have := Real.pi_pos
    positivity

theorem zero_bound (hE : Module.finrank ℝ E = 2) (u : E) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => (∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      - 1 / (t * ZLattice.covolume L))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  classical
  have h : Summable fun y : dualLattice L => Real.exp (-(Real.pi * ‖(y : E)‖ ^ 2)) := by
    simpa only [neg_mul] using summable_lattice_exp_neg_mul_norm_sq (dualLattice L) Real.pi_pos
  obtain ⟨δ, hδ, hq⟩ := exists_pos_le_of_summable h
  have hV := ZLattice.covolume_pos L MeasureTheory.volume
  set C := Real.exp δ * ∑' y : dualLattice L, Real.exp (-(Real.pi * ‖(y : E)‖ ^ 2)) with hC
  have hC0 : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)
  refine ⟨δ / 2, by positivity, IsBigO.of_bound ((ZLattice.covolume L)⁻¹ * (2 / δ) * C) ?_⟩
  have h4 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  filter_upwards [h4, self_mem_nhdsWithin] with t ht1 ht
  have ht : 0 < t := ht
  obtain ⟨h1, h2⟩ := poisson_gaussian_lattice_cos L ht u
  rw [h2, h1.tsum_eq_add_tsum_ite 0, hE]
  have hs : 1 ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1.le
  have h5 := abs_tsum_le (δ := δ) (f := fun y : dualLattice L => if y = 0 then 0 else
      Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * Real.pi * ⟪(y : E), u⟫)) hs h
      (fun y => ?_) (fun y hy => hq y ?_)
  · generalize (∑' y : dualLattice L, if y = 0 then 0 else
      Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * Real.pi * ⟪(y : E), u⟫)) = S at h5 ⊢
    rw [← hC] at h5
    have h6 : t ^ (-(((2 : ℕ) : ℝ) / 2)) = t⁻¹ := by
      rw [← Real.rpow_neg_one]; norm_num
    rw [h6]
    have h7 : (ZLattice.covolume L)⁻¹ * t⁻¹ * (Real.exp (-Real.pi * ‖((0 : dualLattice L) : E)‖ ^ 2 / t) *
        Real.cos (2 * Real.pi * ⟪((0 : dualLattice L) : E), u⟫) + S) - 1 / (t * ZLattice.covolume L)
        = (ZLattice.covolume L)⁻¹ * t⁻¹ * S := by
      simp only [ZeroMemClass.coe_zero, norm_zero, inner_zero_left]
      simp
      ring
    rw [h7, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity)]
    have h8 : t⁻¹ ≤ 2 / δ * Real.exp (δ / 2 * t⁻¹) := by
      have := Real.add_one_le_exp (δ / 2 * t⁻¹)
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      nlinarith
    calc (ZLattice.covolume L)⁻¹ * t⁻¹ * |S|
        ≤ (ZLattice.covolume L)⁻¹ * (2 / δ * Real.exp (δ / 2 * t⁻¹)) * (C * Real.exp (-δ * t⁻¹)) := by
          gcongr
      _ = (ZLattice.covolume L)⁻¹ * (2 / δ) * C * (Real.exp (δ / 2 * t⁻¹) * Real.exp (-δ * t⁻¹)) := by
          ring
      _ = (ZLattice.covolume L)⁻¹ * (2 / δ) * C * Real.exp (-(δ / 2) / t) := by
          rw [← Real.exp_add]; congr 2; ring
  · split_ifs
    · rw [abs_zero]; positivity
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      refine (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)).trans ?_
      apply le_of_eq; congr 1; ring
  · have hy0 : y ≠ 0 := fun h0 => hy (if_pos h0)
    have : 0 < ‖(y : E)‖ := norm_pos_iff.2 (by simpa using hy0)
    have := Real.pi_pos
    positivity

end Lattice

theorem covolume_lattice (L : PeriodPair) :
    ZLattice.covolume L.lattice = |(starRingEnd ℂ L.ω₁ * L.ω₂).im| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.orthonormalBasisOneI.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis,
    Complex.orthonormalBasisOneI.volume_parallelepiped, ENNReal.toReal_one, _root_.mul_one]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply]
  ring

theorem theta_asymptotics : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  intro w₁ w₂ x₀ hw hx
  let L : PeriodPair := ⟨w₁, w₂, by
    rw [LinearIndependent.pair_iff]
    intro s t e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 hw
    constructor
    · apply mul_left_cancel₀ hw
      linear_combination w₂.im * e1 - w₂.re * e2
    · apply mul_left_cancel₀ hw
      linear_combination w₁.re * e2 - w₁.im * e1⟩
  have hsum : ∀ t : ℝ, ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2) =
      ∑' x : L.lattice, Real.exp (-Real.pi * t * ‖(x : ℂ) + x₀‖ ^ 2) := by
    intro t
    rw [← L.latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun p => ?_
    have := L.latticeEquiv_symm_apply p
    have e : ((L.latticeEquivProd.symm.toEquiv p : L.lattice) : ℂ) + x₀
        = x₀ + p.1 * w₁ + p.2 * w₂ := by
      change (L.latticeEquivProd.symm p).1 + x₀ = _
      rw [this]
      ring
    rw [e]
  have hu : ∀ x : L.lattice, (x : ℂ) + x₀ ≠ 0 := by
    intro x h
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 x.2
    apply hx m n
    rw [← h, ← hmn]
    ring
  obtain ⟨c₁, hc₁, h₁⟩ := atTop_bound L.lattice x₀ hu
  obtain ⟨c₂, hc₂, h₂⟩ := zero_bound L.lattice Complex.finrank_real_complex x₀
  rw [covolume_lattice] at h₂
  simp only [hsum]
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, h₁.trans (IsBigO.of_bound' ?_), h₂.trans (IsBigO.of_bound' ?_)⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp]
    nlinarith [min_le_left c₁ c₂]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : 0 < t := ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp]
    gcongr
    exact min_le_right _ _

end GlobalTheory.PlaneTheta
end

open Complex Filter Asymptotics
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_theta_asymptotics : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  atlas_forward_decl GlobalTheory.PlaneTheta.theta_asymptotics
end

section
section
open Complex Filter Asymptotics

namespace GlobalTheory

open Set MeasureTheory
open scoped Topology

theorem summable_shiftedLattice_normSq_rpow (w₁ w₂ x₀ : ℂ)
    (h : (starRingEnd ℂ w₁ * w₂).im ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : ℤ × ℤ => (‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) ^ (-σ) := by
  have hli : ∀ a b : ℝ, a • w₁ + b • w₂ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg Complex.re hab
    have h2 := congrArg Complex.im hab
    simp at h1 h2 h
    have h' : w₁.re * w₂.im - w₁.im * w₂.re ≠ 0 := by
      intro h0; apply h; linarith
    constructor
    · apply mul_right_cancel₀ h'
      linear_combination w₂.im * h1 - w₂.re * h2
    · apply mul_right_cancel₀ h'
      linear_combination w₁.re * h2 - w₁.im * h1
  let L : PeriodPair := ⟨w₁, w₂, LinearIndependent.pair_iff.mpr hli⟩
  have hs := ZLattice.summable_norm_sub_rpow L.lattice (-(2 * σ)) (by simp; linarith) (-x₀)
  let φ : ℤ × ℤ → L.lattice := fun p =>
    ⟨p.1 * w₁ + p.2 * w₂, PeriodPair.mem_lattice.mpr ⟨p.1, p.2, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro p q hpq
    have e : (p.1 * w₁ + p.2 * w₂ : ℂ) = q.1 * w₁ + q.2 * w₂ := congrArg Subtype.val hpq
    have := hli (p.1 - q.1) (p.2 - q.2) (by simp; linear_combination e)
    simp only [sub_eq_zero, Int.cast_inj] at this
    exact Prod.ext this.1 this.2
  refine (hs.comp_injective hφ).congr fun p => ?_
  simp only [Function.comp, φ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  · congr 1; ring
  · push_cast; ring

theorem summable_exp_neg_pi_mul_of_summable_rpow {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) {t : ℝ} (ht : 0 < t) :
    Summable fun i => Real.exp (-Real.pi * t * q i) := by
  refine Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) (fun i => ?_)
    (hs.mul_left (2 / (Real.pi * t) ^ 2))
  have hx : 0 < Real.pi * t * q i := by have := hq i; positivity
  have h1 := Real.pow_div_factorial_le_exp _ hx.le 2
  have h2 : -Real.pi * t * q i = -(Real.pi * t * q i) := by ring
  have h3 : (2 / (Real.pi * t) ^ 2) * q i ^ (-(2 : ℝ))
      = ((Real.pi * t * q i) ^ 2 / (Nat.factorial 2 : ℕ))⁻¹ := by
    have := hq i
    rw [Real.rpow_neg (hq i).le, Real.rpow_two]
    simp only [Nat.factorial_two, Nat.cast_ofNat]
    field_simp
  rw [h2, h3, Real.exp_neg]
  exact inv_anti₀ (by positivity) h1

theorem continuousOn_tsum_exp_neg_pi_mul {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) :
    ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi 0) := by
  intro t ht
  have ht' : 0 < t / 2 := half_pos ht
  have : ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi (t / 2)) := by
    refine continuousOn_tsum (fun i => by fun_prop)
      (summable_exp_neg_pi_mul_of_summable_rpow hq hs ht') fun i x hx => ?_
    rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_le_exp.mpr
    have h1 : t / 2 < x := hx
    have := mul_pos (mul_pos Real.pi_pos (sub_pos.mpr h1)) (hq i)
    linarith
  exact (this.continuousAt (Ioi_mem_nhds (half_lt_self ht))).continuousWithinAt

theorem isBigO_exp_neg_div_rpow {c : ℝ} (hc : 0 < c) (b : ℝ) :
    (fun t : ℝ => Real.exp (-c / t)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  refine ((isLittleO_exp_neg_mul_rpow_atTop hc b).isBigO.comp_tendsto
    tendsto_inv_nhdsGT_zero).congr' (.of_forall fun t => ?_)
    (eventually_mem_nhdsWithin.mono fun t ht => ?_)
  · simp [div_eq_mul_inv]
  · simp only [Function.comp]
    rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]

theorem exists_entire_dirichlet_of_theta {ι : Type*} [Countable ι] {q : ι → ℝ}
    (hq : ∀ i, 0 < q i) (hs : ∀ σ : ℝ, 1 < σ → Summable fun i => q i ^ (-σ)) {V c : ℝ}
    (hc : 0 < c)
    (htop : (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) =O[atTop]
      (fun t => Real.exp (-c * t)))
    (hbot : (fun t : ℝ => (∑' i, Real.exp (-Real.pi * t * q i)) - 1 / (t * V)) =O[𝓝[>] 0]
      (fun t => Real.exp (-c / t))) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / V : ℝ) ∧ Z (-1) = 0 ∧
      ∀ s : ℂ, 1 < s.re → Summable (fun i => ((q i : ℝ) : ℂ) ^ (-s)) ∧
        Z s = (s - 1) * ∑' i, ((q i : ℝ) : ℂ) ^ (-s) := by
  set θ : ℝ → ℝ := fun t => ∑' i, Real.exp (-Real.pi * t * q i) with hθ
  have hθc : ContinuousOn θ (Ioi 0) := continuousOn_tsum_exp_neg_pi_mul hq (hs 2 one_lt_two)
  let g : ℝ → ℂ := indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (-1 : ℂ))
  let A : ℂ := (V : ℂ)⁻¹
  let f : ℝ → ℂ := fun t => (θ t : ℂ) - A • g t
  have hfc : LocallyIntegrableOn f (Ioi 0) := by
    refine LocallyIntegrableOn.sub
      ((continuous_ofReal.comp_continuousOn hθc).locallyIntegrableOn measurableSet_Ioi)
      (LocallyIntegrableOn.smul ?_ A)
    have h0 : LocallyIntegrableOn (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) (Ioi 0) :=
      ContinuousOn.locallyIntegrableOn (continuousOn_of_forall_continuousAt fun t ht =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)) measurableSet_Ioi
    intro x hx
    obtain ⟨u, hu, hu'⟩ := h0 x hx
    exact ⟨u, hu, hu'.indicator measurableSet_Ioc⟩
  have hftop : f =O[atTop] fun t => Real.exp (-c * t) := by
    refine (isBigO_ofReal_left.mpr htop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [f, g, indicator_of_notMem (fun h : t ∈ Ioc (0:ℝ) 1 => h.2.not_gt ht)]
  have hfbot : ∀ b : ℝ, f =O[𝓝[>] 0] fun t => t ^ (-b) := by
    intro b
    refine ((isBigO_ofReal_left.mpr hbot).congr' ?_ EventuallyEq.rfl).trans
      (isBigO_exp_neg_div_rpow hc b)
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    simp only [f, g, A, indicator_of_mem ht, cpow_neg_one, smul_eq_mul, θ]
    push_cast
    ring
  have hdiff : Differentiable ℂ (mellin f) := fun s =>
    mellin_differentiableAt_of_isBigO_rpow_exp hc hfc hftop (hfbot (s.re - 1)) (sub_one_lt _)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨fun s => (Real.pi : ℂ) ^ s * (Gamma s)⁻¹ * ((s - 1) * mellin f s + A), ?_, ?_, ?_, ?_⟩
  · refine (Differentiable.mul (differentiable_id.const_cpow (Or.inl hpi))
      differentiable_one_div_Gamma).mul ?_
    exact ((differentiable_id.sub_const 1).mul hdiff).add_const A
  · simp [A, div_eq_mul_inv]
  · have : Gamma (-1) = 0 := by simpa using Gamma_neg_nat_eq_zero 1
    simp [this]
  · intro s hs1
    have hs0 : 0 < s.re := by linarith
    have hsum : HasSum (fun i => (Real.pi : ℂ) ^ (-s) * Gamma s * (1 : ℂ) / (q i : ℂ) ^ s)
        (mellin (fun t => (θ t : ℂ)) s) := by
      refine hasSum_mellin_pi_mul (a := fun _ => 1) (fun i => Or.inr (hq i)) hs0
        (fun t ht => ?_) ?_
      · have := (summable_exp_neg_pi_mul_of_summable_rpow hq (hs 2 one_lt_two) ht).hasSum
        rw [← hasSum_ofReal] at this
        convert this using 3 with i
        rw [one_mul]; congr 2; ring
      · refine (hs s.re hs1).congr fun i => ?_
        rw [Real.rpow_neg (hq i).le, norm_one, one_div]
    have hg := hasMellin_cpow_Ioc (-1) (s := s) (by simp; linarith)
    have hgA := hasMellin_const_smul hg.1 A
    have hfm : MellinConvergent f s :=
      mellinConvergent_of_isBigO_rpow_exp hc hfc hftop (hfbot 0) hs0
    have hadd := (hasMellin_add hfm hgA.1).2
    have e1 : (fun t => f t + A • g t) = fun t => (θ t : ℂ) := by
      funext t; simp [f]
    rw [hgA.2, hg.2] at hadd
    have hadd' : mellin (fun t => (θ t : ℂ)) s = mellin f s + A • (1 / (s + -1)) := by
      rw [← e1]; exact hadd
    have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
    have hp : (Real.pi : ℂ) ^ s ≠ 0 := by simp [cpow_eq_zero_iff]
    have hs1' : s - 1 ≠ 0 := by
      intro h0; rw [sub_eq_zero.mp h0] at hs1; simp at hs1
    have hsum2 : HasSum (fun i => ((q i : ℝ) : ℂ) ^ (-s))
        ((Real.pi : ℂ) ^ s * (Gamma s)⁻¹ * mellin (fun t => (θ t : ℂ)) s) := by
      refine HasSum.congr_fun (hsum.mul_left ((Real.pi : ℂ) ^ s * (Gamma s)⁻¹)) fun i => ?_
      rw [cpow_neg, cpow_neg]
      field_simp
    refine ⟨hsum2.summable, ?_⟩
    rw [hsum2.tsum_eq, hadd', ← sub_eq_add_neg, smul_eq_mul]
    field_simp

theorem epsteinZeta_shifted_continuation : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / |(starRingEnd ℂ w₁ * w₂).im| : ℝ) ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → Summable (fun p : ℤ × ℤ => ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s)) ∧ Z s = (s - 1) * ∑' p : ℤ × ℤ, ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  intro w₁ w₂ x₀ h hx
  obtain ⟨c, hc, htop, hbot⟩ := GlobalTheory.T.lattice_theta_asymptotics w₁ w₂ x₀ h hx
  exact exists_entire_dirichlet_of_theta
    (q := fun p : ℤ × ℤ => ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)
    (fun p => pow_pos (norm_pos_iff.mpr (hx p.1 p.2)) 2)
    (fun σ hσ => summable_shiftedLattice_normSq_rpow w₁ w₂ x₀ h hσ) hc htop hbot

end GlobalTheory
end

open Complex Filter Asymptotics
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_epstein_zeta_continuation : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / |(starRingEnd ℂ w₁ * w₂).im| : ℝ) ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → Summable (fun p : ℤ × ℤ => ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s)) ∧ Z s = (s - 1) * ∑' p : ℤ × ℤ, ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  atlas_forward_decl GlobalTheory.epsteinZeta_shifted_continuation
end

section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Mem.PartialZeta

variable {K : Type} [Field K] [NumberField K]

theorem place_unique [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (v w : InfinitePlace K) : v = w := by
  have hc := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, h2] at hr
  rw [IsTotallyComplex.nrRealPlaces_eq_zero] at hc
  have h1 : Fintype.card (InfinitePlace K) = 1 := by omega
  exact Fintype.card_le_one_iff.1 h1.le v w

theorem normSq_eq [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖ ^ 2 = (Ideal.absNorm (Ideal.span {x}) : ℝ) := by
  haveI : Subsingleton (InfinitePlace K) := ⟨place_unique h2⟩
  have hprod := InfinitePlace.prod_eq_abs_norm (x : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), InfinitePlace.apply,
    InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex _))] at hprod
  rw [hprod, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs,
    ← Algebra.coe_norm_int]
  norm_cast

theorem finite_units [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) : Finite (𝓞 K)ˣ := by
  have hfin := Embeddings.finite_of_norm_le K ℂ 1
  have hone : ∀ (u : (𝓞 K)ˣ) (ψ : K →+* ℂ), ‖ψ ((u : 𝓞 K) : K)‖ = 1 := by
    intro u ψ
    have h := normSq_eq h2 ψ (u : 𝓞 K)
    rw [Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  haveI := hfin.to_subtype
  refine Finite.of_injective (fun u : (𝓞 K)ˣ =>
    (⟨((u : 𝓞 K) : K), (u : 𝓞 K).isIntegral_coe, fun ψ => (hone u ψ).le⟩ :
      {x : K | IsIntegral ℤ x ∧ ∀ ψ : K →+* ℂ, ‖ψ x‖ ≤ 1})) ?_
  intro u v huv
  exact Units.ext (RingOfIntegers.ext (by simpa using congrArg Subtype.val huv))

theorem im_ne_zero [IsTotallyComplex K] (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) :
    (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ≠ 0 := by
  intro him
  have h2 : Module.finrank ℚ K = 2 := by
    rw [← RingOfIntegers.rank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hb0 : (b 0 : K) ≠ 0 := by
    intro h
    exact b.ne_zero 0 (RingOfIntegers.ext (by simpa using h))
  have ha0 : φ (b 0 : K) ≠ 0 := (map_ne_zero φ).2 hb0
  have hca0 : starRingEnd ℂ (φ (b 0 : K)) ≠ 0 := (map_ne_zero _).2 ha0
  set y : K := (b 1 : K) / (b 0 : K) with hy
  have hφy : (φ y).im = 0 := by
    have hq : φ y = (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)) /
        (Complex.normSq (φ (b 0 : K)) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_div_mul_left _ _ hca0, hy, map_div₀]
    rw [hq, Complex.div_ofReal_im, him, zero_div]
  by_cases hyq : y ∈ Set.range (algebraMap ℚ K)
  · obtain ⟨q, hq⟩ := hyq
    have hK : (q.den : K) * (b 1 : K) = (q.num : K) * (b 0 : K) := by
      have hd : (q.den : K) ≠ 0 := by exact_mod_cast q.den_nz
      have h1 : (b 1 : K) = (q : K) * (b 0 : K) := by
        rw [← eq_ratCast (algebraMap ℚ K) q, hq, hy, div_mul_cancel₀ _ hb0]
      rw [h1, Rat.cast_def]
      field_simp
    have hz : (-q.num) • b 0 + ((q.den : ℤ)) • b 1 = 0 := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.coe_eq_algebraMap] at hK ⊢
      simp only [zsmul_eq_mul, map_add, map_mul, map_intCast, map_neg, map_zero, map_natCast]
      push_cast at hK ⊢
      linear_combination hK
    have := Fintype.linearIndependent_iff.1 b.linearIndependent ![-q.num, (q.den : ℤ)]
      (by simpa [Fin.sum_univ_two] using hz) 1
    simp at this
  · have hli : LinearIndependent ℚ ![(1 : K), y] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have hg1 : g 1 = 0 := by
        by_contra hne
        apply hyq
        refine ⟨-(g 0) / g 1, ?_⟩
        rw [eq_ratCast]
        push_cast
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hg
        rw [div_eq_iff (by exact_mod_cast hne)]
        linear_combination -hg
      have hg0 : g 0 = 0 := by
        rw [hg1, zero_smul, add_zero, smul_eq_zero] at hg
        simpa using hg
      intro i
      fin_cases i
      · exact hg0
      · exact hg1
    have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
    have hreal : ∀ x : K, (φ x).im = 0 := by
      intro x
      have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), y]) := htop ▸ Submodule.mem_top
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hx
      simp [Fin.sum_univ_two, Rat.smul_def, hφy]
    have hR : ComplexEmbedding.IsReal φ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.2 (hreal x)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex
      (InfinitePlace.mk φ))) (InfinitePlace.isReal_mk_iff.2 hR)

theorem abs_im_eq (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (J : Ideal (𝓞 K))
    (e : Module.Basis (Fin 2) ℤ J) :
    |(starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im| =
      Ideal.absNorm J * |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| := by
  classical
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψdef
  have hψ : ∀ x : 𝓞 K, φ (x : K) = ψ x := fun x => rfl
  have he : ∀ j, ψ (e j : 𝓞 K) = (b.repr (e j : 𝓞 K) 0 : ℂ) * ψ (b 0) +
      (b.repr (e j : 𝓞 K) 1 : ℂ) * ψ (b 1) := by
    intro j
    conv_lhs => rw [← b.sum_repr (e j : 𝓞 K)]
    simp [map_sum, Fin.sum_univ_two, zsmul_eq_mul]
  have hdet := Ideal.natAbs_det_basis_change b J e
  rw [Module.Basis.det_apply, Matrix.det_fin_two] at hdet
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at hdet
  simp only [hψ]
  rw [← hdet, Nat.cast_natAbs, Int.cast_abs, ← abs_mul, he 0, he 1]
  congr 1
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem cls_iff {M : ℕ} (D : RayData K M) (c : D.G) (B I : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹)
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) (hI0 : I ≠ ⊥) :
    D.cls I = c ↔ ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I * B := by
  constructor
  · intro h
    have hIB : D.cls (I * B) = 1 := by
      rw [D.cls_mul I B hI hB hI0 hB0, h, hc, mul_inv_cancel]
    obtain ⟨a, b', ha, hb, ha1, hb1, hab⟩ :=
      (D.cls_eq_one_iff (hI.mul_left hB) (mul_ne_zero hI0 hB0)).1 hIB
    have hmem : b' ∈ Ideal.span {a} := by
      have : b' ∈ Ideal.span {a} * (I * B) := by
        rw [hab]; exact Ideal.mem_span_singleton_self b'
      exact Ideal.mul_le_left this
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨x, ?_, ?_⟩
    · have hax : a * x - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [mul_comm, hx]; exact hb1
      have : x - 1 = (a * x - 1) - (a - 1) * x := by ring
      rw [this]
      exact Ideal.sub_mem _ hax (Ideal.mul_mem_right x _ ha1)
    · have hspan : Ideal.span {a} * (I * B) = Ideal.span {a} * Ideal.span {x} := by
        rw [hab, ← hx, ← Ideal.span_singleton_mul_span_singleton, mul_comm]
      have ha' : Ideal.span {a} ≠ 0 := by
        rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact ha
      exact (mul_left_cancel₀ ha' hspan).symm
  · rintro ⟨x, hx1, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
      exact mul_ne_zero hI0 hB0 hx.symm
    have h1 : D.cls (I * B) = 1 := by rw [← hx]; exact D.cls_span hx0 hx1
    rw [D.cls_mul I B hI hB hI0 hB0, hc] at h1
    exact mul_inv_eq_one.1 h1

theorem lattice_bij (N B : Ideal (𝓞 K)) (hB : IsCoprime B N) (e : Module.Basis (Fin 2) ℤ ↥(N * B))
    (x₀ : 𝓞 K) (h0 : x₀ ∈ B) (h1 : x₀ - 1 ∈ N) :
    ∃ f : ℤ × ℤ ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N},
      ∀ p, (f p : 𝓞 K) = x₀ + p.1 * (e 0 : 𝓞 K) + p.2 * (e 1 : 𝓞 K) := by
  have hmemNB : ∀ y : ↥(N * B), (y : 𝓞 K) ∈ B ∧ (y : 𝓞 K) ∈ N := fun y =>
    ⟨Ideal.mul_le_right y.2, Ideal.mul_le_left y.2⟩
  let g : ↥(N * B) ≃ {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ N} :=
    { toFun := fun y => ⟨x₀ + y, B.add_mem h0 (hmemNB y).1, by
        rw [add_sub_right_comm]; exact N.add_mem h1 (hmemNB y).2⟩
      invFun := fun x => ⟨x.1 - x₀, by
        rw [← Ideal.inf_eq_mul_of_isCoprime hB.symm]
        refine ⟨?_, ?_⟩
        · have : x.1 - x₀ = (x.1 - 1) - (x₀ - 1) := by ring
          rw [this]; exact N.sub_mem x.2.2 h1
        · exact B.sub_mem x.2.1 h0⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  refine ⟨(finTwoArrowEquiv ℤ).symm.trans (e.equivFun.symm.toEquiv.trans g), fun p => ?_⟩
  simp [g, Fin.sum_univ_two, zsmul_eq_mul, add_assoc]

theorem ne_bot_of_coprime {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) {I : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hI
  exact hM hI

theorem gen_bij {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G)
    (B : Ideal (𝓞 K))
    (hB : IsCoprime B (Ideal.span {(M : 𝓞 K)})) (hB0 : B ≠ ⊥) (hc : D.cls B = c⁻¹) :
    ∃ f : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
        {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} ≃
        {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}},
      ∀ p, Ideal.span {(f p : 𝓞 K)} = p.1 * B := by
  classical
  have hgen : ∀ I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c},
      ∃ x : 𝓞 K, x - 1 ∈ Ideal.span {(M : 𝓞 K)} ∧ Ideal.span {x} = I.1 * B := fun I =>
    (cls_iff D c B I.1 hB hB0 hc I.2.1 (ne_bot_of_coprime hM I.2.1)).1 I.2.2
  choose g hg1 hg using hgen
  have hgB : ∀ I, g I ∈ B := fun I => by
    have : g I ∈ Ideal.span {g I} := Ideal.mem_span_singleton_self _
    rw [hg I] at this
    exact Ideal.mul_le_right this
  have hg0 : ∀ I, g I ≠ 0 := fun I h => by
    have := hg I
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact mul_ne_zero (ne_bot_of_coprime hM I.2.1) hB0 this.symm
  let F : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} ×
      {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} →
      {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} := fun p =>
    ⟨(p.2.1 : 𝓞 K) * g p.1, Ideal.mul_mem_left _ _ (hgB p.1), by
      have : (p.2.1 : 𝓞 K) * g p.1 - 1 = (p.2.1 : 𝓞 K) * (g p.1 - 1) + ((p.2.1 : 𝓞 K) - 1) := by
        ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hg1 p.1)) p.2.2⟩
  have hspanF : ∀ p, Ideal.span {(F p : 𝓞 K)} = p.1 * B := fun p => by
    show Ideal.span {(p.2.1 : 𝓞 K) * g p.1} = _
    rw [Ideal.span_singleton_mul_left_unit p.2.1.isUnit, hg]
  have hinj : Function.Injective F := by
    rintro ⟨I, u⟩ ⟨I', u'⟩ h
    have h1 := hspanF (I, u)
    rw [h, hspanF (I', u')] at h1
    have hII : I = I' := Subtype.ext (mul_right_cancel₀ (by simpa using hB0) h1.symm)
    subst hII
    have h2 : (u.1 : 𝓞 K) * g I = (u'.1 : 𝓞 K) * g I := congrArg Subtype.val h
    have h3 : (u.1 : 𝓞 K) = (u'.1 : 𝓞 K) := mul_right_cancel₀ (hg0 I) h2
    rw [Subtype.ext (Units.ext h3)]
  have hsurj : Function.Surjective F := by
    rintro ⟨x, hxB, hx1⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hM
      rw [Ideal.eq_top_iff_one]
      have := (Ideal.neg_mem_iff _).2 hx1
      simpa using this
    have hle : Ideal.span {x} ≤ B := (Ideal.span_singleton_le_iff_mem _).2 hxB
    obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 hle
    have hxc : IsCoprime (Ideal.span {x}) (Ideal.span {(M : 𝓞 K)}) := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      have : (1 : 𝓞 K) = x - (x - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
        (Ideal.mem_sup_right hx1)
    have hIc : IsCoprime I (Ideal.span {(M : 𝓞 K)}) := by
      rw [hI] at hxc; exact hxc.of_mul_left_right
    have hIB : Ideal.span {x} = I * B := by rw [hI, mul_comm]
    have hIcls : D.cls I = c :=
      (cls_iff D c B I hB hB0 hc hIc (ne_bot_of_coprime hM hIc)).2 ⟨x, hx1, hIB⟩
    let I' : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} :=
      ⟨I, hIc, hIcls⟩
    have hass : Associated (g I') x := by
      rw [← Ideal.span_singleton_eq_span_singleton, hg I', hIB]
    obtain ⟨u, hu⟩ := hass
    have hu1 : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have hgu : g I' * u - 1 ∈ Ideal.span {(M : 𝓞 K)} := by rw [hu]; exact hx1
      have : (u : 𝓞 K) - 1 = (g I' * u - 1) - (g I' - 1) * u := by ring
      rw [this]
      exact Ideal.sub_mem _ hgu (Ideal.mul_mem_right _ _ (hg1 I'))
    refine ⟨(I', ⟨u, hu1⟩), Subtype.ext ?_⟩
    show (u : 𝓞 K) * g I' = x
    rw [mul_comm, hu]
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun p => hspanF p⟩

theorem hasSum_cnt {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G) (s a : ℂ)
    (h : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} =>
      (Ideal.absNorm I.1 : ℂ) ^ (-s)) a) : LSeriesHasSum (D.cnt c) s a := by
  classical
  let C := {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c}
  let Nm : C → ℕ := fun I => Ideal.absNorm I.1
  have h' : HasSum (fun x : (Σ n : ℕ, {I : C // Nm I = n}) =>
      (Ideal.absNorm x.2.1.1 : ℂ) ^ (-s)) a :=
    (Equiv.sigmaFiberEquiv Nm).hasSum_iff.2 h
  refine h'.sigma (fun n => ?_)
  let en : {I : C // Nm I = n} ≃
      {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = c} :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.2, x.1.2.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.2⟩, y.2.2.1⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  haveI : Finite {I : C // Nm I = n} := by
    haveI := D.finite_cnt c n
    exact Finite.of_equiv _ en.symm
  haveI : Fintype {I : C // Nm I = n} := Fintype.ofFinite _
  have hconst : (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) =
      fun _ => (n : ℂ) ^ (-s) := by
    funext x
    rw [show Ideal.absNorm x.1.1 = n from x.2]
  show HasSum (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) _
  rw [hconst]
  by_cases hn : n = 0
  · subst hn
    haveI : IsEmpty {I : C // Nm I = 0} := ⟨fun x => by
      have hx : x.1.1 = ⊥ := Ideal.absNorm_eq_zero_iff.1 x.2
      exact ne_bot_of_coprime hM x.1.2.1 hx⟩
    rw [LSeries.term_zero]
    exact hasSum_empty
  · rw [LSeries.term_of_ne_zero hn]
    have hs := hasSum_fintype (fun _ : {I : C // Nm I = n} => (n : ℂ) ^ (-s))
    convert hs using 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, RayData.cnt,
      ← Nat.card_congr en, Nat.card_eq_fintype_card, Complex.cpow_neg, div_eq_mul_inv]

theorem partial_zeta_continuation : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ D : RayData K M, ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : D.G, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = ρ ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → LSeriesSummable (D.cnt c) s ∧ Z s = (s - 1) * LSeries (D.cnt c) s := by
  intro K _ _ _ h2 M hM2 D
  classical
  have hrk : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, h2]
  have hNnorm : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    rw [Ideal.absNorm_span_singleton,
      show (M : 𝓞 K) = algebraMap ℤ (𝓞 K) (M : ℤ) by simp, Algebra.norm_algebraMap, hrk]
    simp [Int.natAbs_pow]
  have hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤ := by
    intro h
    have := hNnorm
    rw [h, Ideal.absNorm_top] at this
    nlinarith
  have hN0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    intro h
    have := hNnorm
    rw [h, Ideal.absNorm_bot] at this
    nlinarith
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrk
  let φ : K →+* ℂ := Classical.choice inferInstance
  let ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K)
  haveI : Finite (𝓞 K)ˣ := finite_units h2
  let U := {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}}
  haveI : Fintype U := Fintype.ofFinite _
  have hw : 0 < Fintype.card U := Fintype.card_pos_iff.2 ⟨⟨1, by simp⟩⟩
  set ib := |(starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im| with hib
  have hib0 : 0 < ib := abs_pos.2 (im_ne_zero φ b)
  refine ⟨Real.pi / (Fintype.card U * (M : ℝ) ^ 2 * ib), by positivity, fun c => ?_⟩
  obtain ⟨B, hBc, hB0, hcB⟩ := D.cls_surj c⁻¹
  obtain ⟨x₀, hx₀B, z, hz, hxz⟩ := Submodule.mem_sup.1
    ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hBc))
  have hx₀1 : x₀ - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
    have : x₀ - 1 = -z := by rw [← hxz]; ring
    rw [this]; exact (Ideal.neg_mem_iff _).2 hz
  have hNB0 : Ideal.span {(M : 𝓞 K)} * B ≠ ⊥ := mul_ne_zero hN0 hB0
  let e : Module.Basis (Fin 2) ℤ ↥(Ideal.span {(M : 𝓞 K)} * B) := Ideal.selfBasis b _ hNB0
  obtain ⟨fL, hfL⟩ := lattice_bij (Ideal.span {(M : 𝓞 K)}) B hBc e x₀ hx₀B hx₀1
  obtain ⟨fG, hfG⟩ := gen_bij hM D c B hBc hB0 hcB
  have hBn0 : Ideal.absNorm B ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hIm := abs_im_eq φ b (Ideal.span {(M : 𝓞 K)} * B) e
  rw [map_mul, hNnorm] at hIm
  have him : (starRingEnd ℂ (φ ((e 0 : 𝓞 K) : K)) * φ ((e 1 : 𝓞 K) : K)).im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hIm
    have : (0 : ℝ) < ((M ^ 2 * Ideal.absNorm B : ℕ) : ℝ) * ib := by
      have : 0 < M ^ 2 * Ideal.absNorm B := by positivity
      positivity
    linarith
  have hψL : ∀ p : ℤ × ℤ, ψ (fL p : 𝓞 K) =
      φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) + p.2 * φ ((e 1 : 𝓞 K) : K) := by
    intro p
    rw [hfL p]
    simp [ψ, map_add, map_mul, map_intCast]
  have hnz : ∀ m n : ℤ, φ (x₀ : K) + m * φ ((e 0 : 𝓞 K) : K) + n * φ ((e 1 : 𝓞 K) : K) ≠ 0 := by
    intro m n h0
    have hx := (fL (m, n)).2.2
    have hzero : (fL (m, n) : 𝓞 K) = 0 := by
      have := hψL (m, n)
      rw [h0] at this
      have hinj : Function.Injective ψ :=
        φ.injective.comp (IsFractionRing.injective (𝓞 K) K)
      exact hinj (by rw [this, map_zero])
    rw [hzero, zero_sub] at hx
    apply hM
    rw [Ideal.eq_top_iff_one]
    simpa using (Ideal.neg_mem_iff _).2 hx
  obtain ⟨Z0, hZd, hZ1, hZm1, hZs⟩ := GlobalTheory.T.lattice_epstein_zeta_continuation _ _ _ him hnz
  have hBc0 : (Ideal.absNorm B : ℂ) ≠ 0 := by exact_mod_cast hBn0
  have hwc : (Fintype.card U : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  refine ⟨fun s => (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s, ?_, ?_, ?_, ?_⟩
  · exact ((differentiable_id.const_cpow (Or.inl hBc0)).div_const _).mul hZd
  · simp only [Complex.cpow_one]
    rw [hZ1, hIm]
    push_cast
    field_simp
    rw [← hib]
    exact div_self (by exact_mod_cast hib0.ne')
  · simp [hZm1]
  · intro s hs
    obtain ⟨hsum, hZeq⟩ := hZs s hs
    set S := ∑' p : ℤ × ℤ, ((‖φ (x₀ : K) + p.1 * φ ((e 0 : 𝓞 K) : K) +
      p.2 * φ ((e 1 : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) with hS
    let G : {x : 𝓞 K // x ∈ B ∧ x - 1 ∈ Ideal.span {(M : 𝓞 K)}} → ℂ := fun x =>
      ((‖ψ (x : 𝓞 K)‖ ^ 2 : ℝ) : ℂ) ^ (-s)
    have hG : HasSum G S := by
      rw [← fL.hasSum_iff]
      convert hsum.hasSum using 1
      funext p
      simp only [Function.comp_apply, G, hψL p]
    have hGG := fG.hasSum_iff.2 hG
    have hterm : ∀ p, (G ∘ fG) p = (Ideal.absNorm p.1.1 : ℂ) ^ (-s) *
        (Ideal.absNorm B : ℂ) ^ (-s) := by
      intro p
      simp only [Function.comp_apply, G]
      have hn := normSq_eq h2 φ (fG p : 𝓞 K)
      rw [hfG p, map_mul] at hn
      show ((‖φ ((fG p : 𝓞 K) : K)‖ ^ 2 : ℝ) : ℂ) ^ (-s) = _
      rw [hn]
      push_cast
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast (Ideal.absNorm B),
        ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    have hfib := hGG.prod_fiberwise (fun I => hasSum_fintype (fun u : U => (G ∘ fG) (I, u)))
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfib
    have hcnt : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧
        D.cls I = c} => (Ideal.absNorm I.1 : ℂ) ^ (-s))
        ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U * S) := by
      have hBs : (Ideal.absNorm B : ℂ) ^ s ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; tauto
      refine (hfib.mul_left ((Ideal.absNorm B : ℂ) ^ s / Fintype.card U)).congr_fun (fun I => ?_)
      rw [Complex.cpow_neg (Ideal.absNorm B : ℂ)]
      first
        | (field_simp; done)
        | (field_simp; ring)
    have hL := hasSum_cnt hM D c s _ hcnt
    refine ⟨hL.LSeriesSummable, ?_⟩
    rw [hL.LSeries_eq]
    show (Ideal.absNorm B : ℂ) ^ s / Fintype.card U * Z0 s = _
    rw [hZeq]
    ring

end GlobalTheory.Mem.PartialZeta

end
end
