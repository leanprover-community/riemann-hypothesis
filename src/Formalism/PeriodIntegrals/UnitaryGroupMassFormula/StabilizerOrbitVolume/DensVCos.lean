import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibFour

section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter
open scoped Pointwise

def IsLCcOn {V : Type} [TopologicalSpace V] (U : Set V) (φ : V → ℝ) : Prop :=
  IsLocallyConstant φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

def HasCOSub (V : Type) [AddGroup V] [TopologicalSpace V] : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

section Dens

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def HasDens (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

theorem HasDens.sub [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) := by
  obtain ⟨i1, c1, e1⟩ := h₁
  obtain ⟨i2, c2, e2⟩ := h₂
  refine ⟨i1.sub i2, c1.sub c2, fun S hS => ?_⟩
  rw [integral_sub i1.integrableOn i2.integrableOn,
    integral_sub (c1.continuousOn.integrableOn_compact hS) (c2.continuousOn.integrableOn_compact hS),
    e1 S hS, e2 S hS]

theorem HasDens.const_mul (c : ℝ) {φ : V → ℝ} {g : X → ℝ} (h : HasDens μ f ι ν φ g) :
    HasDens μ f ι ν (fun v => c * φ v) (fun b => c * g b) := by
  obtain ⟨hi, hc, he⟩ := h
  refine ⟨hi.const_mul c, continuous_const.mul hc, fun S hS => ?_⟩
  rw [integral_const_mul, integral_const_mul, he S hS]

theorem nonneg_of_setIntegral [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  push_neg at hneg
  have hU : {b | D b < D b0 / 2} ∈ 𝓝 b0 :=
    (isOpen_lt hD continuous_const).mem_nhds (by show D b0 < D b0 / 2; linarith)
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hpos : 0 < ν K := ν.measure_pos_of_mem_nhds hKn
  have hfin : ν K < ⊤ := hKc.measure_lt_top
  have h1 : ∫ b in K, D b ∂ν ≤ ∫ b in K, D b0 / 2 ∂ν :=
    setIntegral_mono_on (hD.continuousOn.integrableOn_compact hKc)
      (continuousOn_const.integrableOn_compact hKc) hKc.measurableSet
      (fun x hx => le_of_lt (hKU hx))
  rw [setIntegral_const, smul_eq_mul] at h1
  try simp only [Measure.real] at h1
  have h2 : 0 < (ν K).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have h3 := h0 K hKc
  nlinarith

theorem HasDens.le [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b := by
  have h := h₂.sub h₁
  have hS : ∀ S, IsCompact S → 0 ≤ ∫ x in S, g₂ x - g₁ x ∂ν := by
    intro S hS
    rw [← h.2.2 S hS]
    exact integral_nonneg fun v => sub_nonneg.mpr (hle v)
  have key : 0 ≤ g₂ b - g₁ b := nonneg_of_setIntegral (fun x => g₂ x - g₁ x) h.2.1 hS b
  linarith

end Dens

section Approx

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem isOpen_inf_iInf (Λ₀ : AddSubgroup V) (h₀o : IsOpen (Λ₀ : Set V)) {ι : Type}
    (t : Finset ι) (L : ι → AddSubgroup V) (hLo : ∀ i, IsOpen (L i : Set V)) :
    IsOpen ((Λ₀ ⊓ ⨅ i ∈ t, L i : AddSubgroup V) : Set V) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := (0 : V)) ?_
  have h1 : (Λ₀ : Set V) ∈ 𝓝 (0 : V) := h₀o.mem_nhds Λ₀.zero_mem
  have h2 : (⋂ i ∈ t, (L i : Set V)) ∈ 𝓝 (0 : V) :=
    (Filter.biInter_finset_mem t).2 fun i _ => (hLo i).mem_nhds (L i).zero_mem
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Set.mem_iInter, SetLike.mem_coe] at hx1 hx2
  simp only [SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
  exact ⟨hx1, fun i hi => hx2 i hi⟩

theorem exists_sub_osc (hNA : HasCOSub V) {φ : V → ℝ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : AddSubgroup V)
    (h₀o : IsOpen (Λ₀ : Set V)) (h₀c : IsCompact (Λ₀ : Set V)) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ ≤ Λ₀ ∧
      ∀ x z, z ∈ Λ → |φ (x + z) - φ x| < ε := by
  have hloc : ∀ x : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧
      ∀ w ∈ W, |φ (x + w) - φ x| < ε / 2 := by
    intro x
    have hcx : ContinuousAt (fun w => φ (x + w)) 0 :=
      (hc.comp (continuous_const.add continuous_id)).continuousAt
    have hN : {w | |φ (x + w) - φ x| < ε / 2} ∈ 𝓝 (0 : V) := by
      have h1 := hcx.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
      filter_upwards [h1] with w hw
      simpa [Real.dist_eq] using hw
    obtain ⟨W, hWo, -, hWN⟩ := hNA _ hN
    exact ⟨W, hWo, fun w hw => hWN hw⟩
  choose W hWo hW using hloc
  have hUo : ∀ i, IsOpen ((fun y => -i + y) ⁻¹' (W i : Set V)) :=
    fun i => (hWo i).preimage (continuous_const.add continuous_id)
  have hcov : tsupport φ ⊆ ⋃ i, (fun y => -i + y) ⁻¹' (W i : Set V) := by
    intro y _
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    show -y + y ∈ W y
    simp
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun i => (fun y => -i + y) ⁻¹' (W i : Set V)) hUo hcov
  have hΛo := isOpen_inf_iInf Λ₀ h₀o t W hWo
  refine ⟨Λ₀ ⊓ ⨅ i ∈ t, W i, hΛo,
    h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ hΛo)
      (SetLike.coe_subset_coe.mpr inf_le_left), inf_le_left, ?_⟩
  intro x z hz
  have hz' := hz
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hz'
  have hzW : ∀ i ∈ t, z ∈ W i := hz'.2
  have hzero : ∀ y, y ∉ tsupport φ → φ y = 0 := fun y hy => by
    by_contra hne
    exact hy (subset_tsupport φ (Function.mem_support.mpr hne))
  by_cases hx : x ∈ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V)
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hxi' : -i + x ∈ W i := hxi
    have h1 := hW i (-i + x) hxi'
    have h2 := hW i (-i + (x + z)) (by
      have e : -i + (x + z) = (-i + x) + z := by abel
      rw [e]
      exact (W i).add_mem hxi' (hzW i hi))
    simp only [add_neg_cancel_left] at h1 h2
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have hxz : x + z ∉ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V) := by
      intro hc'
      apply hx
      simp only [Set.mem_iUnion] at hc' ⊢
      obtain ⟨i, hi, hxi⟩ := hc'
      refine ⟨i, hi, ?_⟩
      have hxi' : -i + (x + z) ∈ W i := hxi
      show -i + x ∈ W i
      have e : -i + x = (-i + (x + z)) + -z := by abel
      rw [e]
      exact (W i).add_mem hxi' ((W i).neg_mem (hzW i hi))
    rw [hzero x (fun h => hx (ht h)), hzero (x + z) (fun h => hxz (ht h))]
    simpa using hε

end Approx

section Main

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]

def cosApx (Λ : AddSubgroup V) (φ : V → ℝ) (x : V) : ℝ := φ ((x : V ⧸ Λ).out)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_sub_mem (Λ : AddSubgroup V) (x : V) : -((x : V ⧸ Λ).out) + x ∈ Λ := by
  have h : ((((x : V ⧸ Λ).out : V) : V ⧸ Λ)) = (x : V ⧸ Λ) := Quotient.out_eq _
  exact QuotientAddGroup.eq.mp h

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_eq (Λ : AddSubgroup V) (φ : V → ℝ) {x y : V} (h : -x + y ∈ Λ) :
    cosApx Λ φ y = cosApx Λ φ x := by
  have e : (y : V ⧸ Λ) = (x : V ⧸ Λ) := (QuotientAddGroup.eq.mpr h).symm
  show φ ((y : V ⧸ Λ).out) = φ ((x : V ⧸ Λ).out)
  rw [e]

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem cosApx_lc (Λ : AddSubgroup V) (hΛ : IsOpen (Λ : Set V)) (φ : V → ℝ) :
    IsLocallyConstant (cosApx Λ φ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : V => -x + y := continuous_const.add continuous_id
  have hm : (fun y : V => -x + y) ⁻¹' (Λ : Set V) ∈ 𝓝 x :=
    (hΛ.preimage hc).mem_nhds (by show -x + x ∈ Λ; simp)
  filter_upwards [hm] with y hy
  exact cosApx_eq Λ φ hy

theorem densApprox_lc (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (f : V → Y) (ι : X → Y)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] (U : Set V)
    (hU : IsOpen U) (hNA : HasCOSub V) : DensApprox (IsLCcOn U) μ f ι ν U := by
  intro hLC φ hφ
  obtain ⟨hc, hs, hsU⟩ := hφ
  obtain ⟨W, hW, hKW⟩ := compact_open_separated_add_right hs.isCompact hU hsU
  obtain ⟨Λ₀, h₀o, h₀c, h₀W⟩ := hNA W hW
  set K' : Set V := tsupport φ + (Λ₀ : Set V) with hK'
  have hcos : ∀ x y, -x + y ∈ Λ₀ → y ∈ K' → x ∈ K' := by
    intro x y h hy
    obtain ⟨k, hk, l, hl, rfl⟩ := hy
    exact ⟨k, hk, l - (-x + (k + l)), Λ₀.sub_mem hl h, by abel⟩
  have hcos' : ∀ x y, -x + y ∈ Λ₀ → (y ∈ K' ↔ x ∈ K') := by
    intro x y h
    refine ⟨hcos x y h, hcos y x ?_⟩
    have := Λ₀.neg_mem h
    rwa [neg_add_rev, neg_neg] at this
  have hnb : ∀ x : V, {y | -x + y ∈ Λ₀} ∈ 𝓝 x := by
    intro x
    refine (h₀o.preimage (continuous_const.add continuous_id)).mem_nhds ?_
    show -x + x ∈ Λ₀
    rw [neg_add_cancel]
    exact Λ₀.zero_mem
  have hK'cl : IsClosed K' := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    exact Filter.mem_of_superset (hnb x) fun y hy hyK => hx (hcos x y hy hyK)
  have hK'c : IsCompact K' := hs.isCompact.add h₀c
  have hK'U : K' ⊆ U := (Set.add_subset_add subset_rfl h₀W).trans hKW
  have hKK' : tsupport φ ⊆ K' := fun x hx => ⟨x, hx, 0, Λ₀.zero_mem, add_zero x⟩
  have hlcc : ∀ ψ : V → ℝ, IsLocallyConstant ψ → Function.support ψ ⊆ K' → IsLCcOn U ψ :=
    fun ψ h1 h2 => ⟨h1, hK'c.of_isClosed_subset isClosed_closure (closure_minimal h2 hK'cl),
      (closure_minimal h2 hK'cl).trans hK'U⟩
  have hdens : ∀ ψ, IsLCcOn U ψ → ∃ g, HasDens μ f ι ν ψ g := fun ψ h => by
    obtain ⟨g, hg, hS⟩ := hLC ψ h
    exact ⟨g, h.1.continuous.integrable_of_hasCompactSupport h.2.1, hg, hS⟩
  set ind : V → ℝ := K'.indicator fun _ => 1 with hind_def
  have hind : IsLCcOn U ind := by
    refine hlcc ind ?_ Set.support_indicator_subset
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y | -x + y ∈ Λ₀}, h₀o.preimage (continuous_const.add continuous_id),
      mem_of_mem_nhds (hnb x), fun y hy => ?_⟩
    have := hcos' x y hy
    rw [hind_def]
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h => hx (this.1 h)]
  obtain ⟨g0, hg0⟩ := hdens ind hind
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose Λ hΛo hΛc hΛ0 hosc using fun n : ℕ => exists_sub_osc hNA hc hs (hε n) Λ₀ h₀o h₀c
  set φn : ℕ → V → ℝ := fun n => cosApx (Λ n) φ with hφn_def
  have hφn_close : ∀ n x, |φn n x - φ x| < 1 / ((n : ℝ) + 1) := by
    intro n x
    have := hosc n ((x : V ⧸ Λ n).out) _ (cosApx_sub_mem (Λ n) x)
    rw [add_neg_cancel_left] at this
    rw [abs_sub_comm]
    exact this
  have hφn_supp : ∀ n, Function.support (φn n) ⊆ K' := by
    intro n x hx
    exact ⟨_, subset_tsupport φ hx, _, hΛ0 n (cosApx_sub_mem (Λ n) x), add_neg_cancel_left _ x⟩
  have hφn : ∀ n, IsLCcOn U (φn n) := fun n => hlcc _ (cosApx_lc _ (hΛo n) φ) (hφn_supp n)
  choose g hg using fun n => hdens (φn n) (hφn n)
  have hbd : ∀ n x, |φn n x - φ x| ≤ 1 / ((n : ℝ) + 1) * ind x := by
    intro n x
    by_cases hx : x ∈ K'
    · rw [hind_def, Set.indicator_of_mem hx, mul_one]
      exact (hφn_close n x).le
    · have h1 : φn n x = 0 := by
        by_contra h
        exact hx (hφn_supp n h)
      have h2 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hKK' h)
      rw [hind_def, Set.indicator_of_notMem hx, h1, h2]
      simp
  have hgg : ∀ n m b, |g n b - g m b| ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b := by
    intro n m b
    have hA := hg0.const_mul (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1))
    have hle : ∀ n m x, φn n x - φn m x ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * ind x := by
      intro n m x
      have h1 := abs_le.1 (hbd n x)
      have h2 := abs_le.1 (hbd m x)
      rw [add_mul]
      linarith [h1.1, h1.2, h2.1, h2.2]
    have u1 := ((hg n).sub (hg m)).le hA (hle n m) b
    have hA' := hg0.const_mul (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1))
    have u2 := ((hg m).sub (hg n)).le hA' (hle m n) b
    refine abs_le.2 ⟨?_, u1⟩
    have : (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) :=
      add_comm _ _
    rw [this] at u2
    linarith
  have hcauchy : ∀ b, CauchySeq fun n => g n b := by
    intro b
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1)) * |g0 b|)
      (fun n m N hn hm => ?_) ?_
    · rw [Real.dist_eq]
      have hN : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hM : (N : ℝ) ≤ m := by exact_mod_cast hm
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      calc |g n b - g m b| ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b := hgg n m b
        _ ≤ (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * |g0 b| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        _ ≤ (1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1)) * |g0 b| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = 2 * (1 / ((N : ℝ) + 1)) * |g0 b| := by ring
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const |g0 b|
      rwa [mul_zero, zero_mul] at this
  set G : X → ℝ := fun b => limUnder atTop fun n => g n b with hG_def
  have hlim : ∀ b, Tendsto (fun n => g n b) atTop (𝓝 (G b)) := fun b =>
    (hcauchy b).tendsto_limUnder
  have hGn : ∀ n b, |G b - g n b| ≤ 1 / ((n : ℝ) + 1) * g0 b := by
    intro n b
    have ht : Tendsto (fun m => |g m b - g n b|) atTop (𝓝 |G b - g n b|) :=
      ((hlim b).sub_const _).abs
    have ht2 : Tendsto (fun m : ℕ => (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) * g0 b) atTop
        (𝓝 ((1 / ((n : ℝ) + 1) + 0) * g0 b)) :=
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const _
    have := le_of_tendsto_of_tendsto' ht ht2 fun m => by
      rw [abs_sub_comm]
      exact hgg n m b
    rwa [add_zero] at this
  have hGc : Continuous G := by
    refine TendstoLocallyUniformly.continuous (F := g) (p := atTop) ?_
      (Eventually.of_forall fun n => (hg n).2.1).frequently
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hεp x
    refine ⟨{y | g0 y < g0 x + 1}, (isOpen_lt hg0.2.1 continuous_const).mem_nhds (by simp), ?_⟩
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * (|g0 x| + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (|g0 x| + 1)
      rwa [zero_mul] at this
    filter_upwards [ht.eventually (Iio_mem_nhds hεp)] with n hn y hy
    have hy' : g0 y < g0 x + 1 := hy
    have hx' := le_abs_self (g0 x)
    rw [Real.dist_eq]
    calc |G y - g n y| ≤ 1 / ((n : ℝ) + 1) * g0 y := hGn n y
      _ ≤ 1 / ((n : ℝ) + 1) * (|g0 x| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ < ε := hn
  refine ⟨G, hGc, fun S hS => ?_⟩
  have hφi : Integrable φ μ := hc.integrable_of_hasCompactSupport hs
  have hC : ∀ n : ℕ, |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ b in S, G b ∂ν| ≤
      2 * (1 / ((n : ℝ) + 1)) * |∫ b in S, g0 b ∂ν| := by
    intro n
    have e1 : |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ v in f ⁻¹' (ι '' S), φn n v ∂μ| ≤
        ∫ v in f ⁻¹' (ι '' S), 1 / ((n : ℝ) + 1) * ind v ∂μ := by
      rw [← integral_sub hφi.integrableOn (hg n).1.integrableOn, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (g := fun v => 1 / ((n : ℝ) + 1) * ind v)
        (hg0.1.const_mul _).integrableOn (ae_of_all _ ?_)
      intro x
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hbd n x
    have e2 : |∫ b in S, g n b ∂ν - ∫ b in S, G b ∂ν| ≤ ∫ b in S, 1 / ((n : ℝ) + 1) * g0 b ∂ν := by
      rw [← integral_sub ((hg n).2.1.continuousOn.integrableOn_compact hS)
        (hGc.continuousOn.integrableOn_compact hS), ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (g := fun b => 1 / ((n : ℝ) + 1) * g0 b)
        ((continuous_const.mul hg0.2.1).continuousOn.integrableOn_compact hS) (ae_of_all _ ?_)
      intro b
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hGn n b
    rw [integral_const_mul, hg0.2.2 S hS] at e1
    rw [integral_const_mul] at e2
    rw [(hg n).2.2 S hS] at e1
    have h3 := abs_sub_le (∫ v in f ⁻¹' (ι '' S), φ v ∂μ) (∫ b in S, g n b ∂ν) (∫ b in S, G b ∂ν)
    have h4 : 1 / ((n : ℝ) + 1) * ∫ b in S, g0 b ∂ν ≤ 1 / ((n : ℝ) + 1) * |∫ b in S, g0 b ∂ν| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    linarith
  by_contra hne
  have hpos : 0 < |∫ v in f ⁻¹' (ι '' S), φ v ∂μ - ∫ b in S, G b ∂ν| :=
    abs_pos.2 (sub_ne_zero.2 hne)
  have ht : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) * |∫ b in S, g0 b ∂ν|) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const
      |∫ b in S, g0 b ∂ν|
    rwa [mul_zero, zero_mul] at this
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hpos)).exists
  exact absurd (hC n) (not_le.2 hn)

end Main

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter

section Cos

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def DensCos (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) : Prop :=
  ∀ x ∈ U, ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ : AddSubgroup V, IsOpen (Λ : Set V) →
    IsCompact (Λ : Set V) → (Λ : Set V) ⊆ N → ∃ g : X → ℝ, Continuous g ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ}.indicator (fun _ => (1 : ℝ)) v ∂μ =
          ∫ b in S, g b ∂ν

theorem hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0) := by
  exact ⟨integrable_zero _ _ _, continuous_const, fun S _ => by simp⟩

theorem HasDens.add [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v + φ₂ v) (fun b => g₁ b + g₂ b) := by
  obtain ⟨hi1, hc1, he1⟩ := h₁
  obtain ⟨hi2, hc2, he2⟩ := h₂
  refine ⟨hi1.add hi2, hc1.add hc2, fun S hS => ?_⟩
  have hg1 : IntegrableOn g₁ S ν := by
    first
      | exact hc1.continuousOn.integrableOn_compact hS
      | exact ContinuousOn.integrableOn_compact hS hc1.continuousOn
  have hg2 : IntegrableOn g₂ S ν := by
    first
      | exact hc2.continuousOn.integrableOn_compact hS
      | exact ContinuousOn.integrableOn_compact hS hc2.continuousOn
  rw [integral_add hi1.integrableOn hi2.integrableOn, integral_add hg1 hg2, he1 S hS, he2 S hS]

theorem hasDens_sum [IsFiniteMeasureOnCompacts ν] {κ : Type} (φ : κ → V → ℝ) (g : κ → X → ℝ) :
    ∀ T : Finset κ, (∀ i ∈ T, HasDens μ f ι ν (φ i) (g i)) →
      HasDens μ f ι ν (fun v => ∑ i ∈ T, φ i v) (fun b => ∑ i ∈ T, g i b) := by
  intro T
  induction T using Finset.cons_induction with
  | empty =>
    intro _
    simpa using (hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0))
  | cons a s ha ih =>
    intro hT
    have h1 := hT a (Finset.mem_cons_self a s)
    have h2 := ih (fun i hi => hT i (Finset.mem_cons_of_mem hi))
    simpa [Finset.sum_cons] using h1.add h2

def DensCosB (B : AddSubgroup V → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X)
    (U : Set V) : Prop :=
  ∀ x ∈ U, ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ : AddSubgroup V, B Λ → IsOpen (Λ : Set V) →
    IsCompact (Λ : Set V) → (Λ : Set V) ⊆ N → ∃ g : X → ℝ, Continuous g ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ}.indicator (fun _ => (1 : ℝ)) v ∂μ =
          ∫ b in S, g b ∂ν

omit [IsTopologicalAddGroup V] in

def IsCOBasis (B : AddSubgroup V → Prop) : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, B Λ ∧ IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem isCompact_cos (Λ : AddSubgroup V) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    IsCompact {z | z - y ∈ Λ} := by
  have he : {z | z - y ∈ Λ} = (fun w => w + y) '' (Λ : Set V) := by
    ext z
    constructor
    · intro hz
      exact ⟨z - y, hz, sub_add_cancel z y⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [he]
  exact hΛc.image (continuous_add_right y)

theorem integrable_cos [IsFiniteMeasureOnCompacts μ] (Λ : AddSubgroup V)
    (hΛo : IsOpen (Λ : Set V)) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    Integrable ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) μ := by
  have hK := isCompact_cos Λ hΛc y
  have hO : IsOpen {z : V | z - y ∈ Λ} := hΛo.preimage (continuous_sub_right y)
  have hI : IntegrableOn (fun _ : V => (1 : ℝ)) {z : V | z - y ∈ Λ} μ := by
    first
      | exact ContinuousOn.integrableOn_compact hK continuousOn_const
      | exact integrableOn_const hK.measure_lt_top.ne
      | exact integrableOn_const.2 (Or.inr hK.measure_lt_top)
  exact hI.integrable_indicator hO.measurableSet

theorem densLC_of_cosB [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (U : Set V)
    (B : AddSubgroup V → Prop) (hB : IsCOBasis B) (h : DensCosB B μ f ι ν U) :
    DensOn (IsLCcOn U) μ f ι ν := by
  classical
  rintro φ ⟨hlc, hs, hsU⟩
  have hloc : ∀ x : tsupport φ, ∃ Λx : AddSubgroup V, IsOpen (Λx : Set V) ∧
      IsCompact (Λx : Set V) ∧
      (∀ y, y - (x : V) ∈ Λx → ∀ Λ : AddSubgroup V, B Λ → IsOpen (Λ : Set V) →
        IsCompact (Λ : Set V) → Λ ≤ Λx →
          ∃ g, HasDens μ f ι ν ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) g) ∧
      ∀ z ∈ Λx, φ ((x : V) + z) = φ x := by
    intro x
    obtain ⟨N, hN, hd⟩ := h x (hsU x.2)
    have hfib : {z : V | φ ((x : V) + z) = φ x} ∈ 𝓝 (0 : V) := by
      have ho : IsOpen {z : V | (φ ∘ fun z => (x : V) + z) z = φ x} :=
        (hlc.comp_continuous (continuous_const.add continuous_id)).isClopen_fiber _ |>.isOpen
      exact ho.mem_nhds (by simp)
    obtain ⟨Λx, -, ho, hc, hsub⟩ := hB _ (inter_mem hN hfib)
    refine ⟨Λx, ho, hc, fun y hy Λ hBΛ hΛo hΛc hle => ?_, fun z hz => (hsub hz).2⟩
    obtain ⟨g, hg, hS⟩ := hd y (hsub hy).1 Λ hBΛ hΛo hΛc fun z hz => (hsub (hle hz)).1
    exact ⟨g, integrable_cos Λ hΛo hΛc y, hg, hS⟩
  choose Λx hΛxo hΛxc hΛxd hΛxφ using hloc
  obtain ⟨t, ht⟩ := hs.isCompact.elim_finite_subcover
    (fun x : tsupport φ => {y : V | y - (x : V) ∈ Λx x})
    (fun x => (hΛxo x).preimage (continuous_id.sub continuous_const))
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, by simp [(Λx _).zero_mem]⟩)
  obtain ⟨Λs, -, hso, -, -⟩ := hB univ univ_mem
  set Λi : AddSubgroup V := Λs ⊓ ⨅ x ∈ t, Λx x with hΛi
  have hΛio : IsOpen (Λi : Set V) := isOpen_inf_iInf Λs hso t Λx hΛxo
  obtain ⟨Λ', hBΛ', hΛ'o, hΛ'c, hΛ'sub⟩ := hB _ (hΛio.mem_nhds Λi.zero_mem)
  have hΛ'le : ∀ x ∈ t, Λ' ≤ Λx x := fun x hx z hz =>
    AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (inf_le_right (a := Λs) (hΛ'sub hz)) x) hx
  have hK : ∀ y ∈ tsupport φ, ∃ x ∈ t, y - (x : V) ∈ Λx x := fun y hy => by
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
    exact ⟨x, hx, hyx⟩
  have hconst : ∀ y ∈ tsupport φ, ∀ z ∈ Λ', φ (y + z) = φ y := by
    intro y hy z hz
    obtain ⟨x, hx, hyx⟩ := hK y hy
    have h1 := hΛxφ x (y - x) hyx
    have h2 := hΛxφ x (y + z - x) (by
      have := (Λx x).add_mem hyx (hΛ'le x hx hz)
      rwa [show y - (x : V) + z = y + z - x by abel] at this)
    rw [add_sub_cancel] at h1 h2
    rw [h2, h1]
  obtain ⟨t2, ht2⟩ := hs.isCompact.elim_finite_subcover
    (fun y : tsupport φ => {z : V | z - (y : V) ∈ Λ'})
    (fun y => hΛ'o.preimage (continuous_id.sub continuous_const))
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, by simp [Λ'.zero_mem]⟩)
  set T : Finset (V ⧸ Λ') :=
    t2.image fun y : tsupport φ => (QuotientAddGroup.mk (y : V) : V ⧸ Λ') with hT
  have hrep : ∀ q ∈ T, ∃ y ∈ tsupport φ, q.out - y ∈ Λ' := by
    intro q hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    refine ⟨y, y.2, ?_⟩
    have := Λ'.neg_mem (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (y : V) : V ⧸ Λ')))
    rwa [neg_add_rev, neg_neg, neg_add_eq_sub] at this
  have hTd : ∀ q ∈ T, ∃ g, HasDens μ f ι ν ({z | z - q.out ∈ Λ'}.indicator fun _ => (1 : ℝ)) g := by
    intro q hq
    obtain ⟨y, hy, hqy⟩ := hrep q hq
    obtain ⟨x, hx, hyx⟩ := hK y hy
    exact hΛxd x q.out (by
      have := (Λx x).add_mem hyx (hΛ'le x hx hqy)
      rwa [show y - (x : V) + (q.out - y) = q.out - x by abel] at this) Λ' hBΛ' hΛ'o hΛ'c
      (hΛ'le x hx)
  choose! gq hgq using hTd
  have hsum := hasDens_sum
    (fun q v => φ (q : V ⧸ Λ').out * {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) v)
    (fun q b => φ (q : V ⧸ Λ').out * gq q b) T (fun q hq => (hgq q hq).const_mul _)
  have heq : (fun v => ∑ q ∈ T,
      φ (q : V ⧸ Λ').out * {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) v) = φ := by
    funext x
    have hind : ∀ q : V ⧸ Λ', {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) x =
        if (x : V ⧸ Λ') = q then 1 else 0 := by
      intro q
      have : x - q.out ∈ Λ' ↔ (x : V ⧸ Λ') = q := by
        conv_rhs => rw [← QuotientAddGroup.out_eq' q]
        rw [eq_comm, QuotientAddGroup.eq, neg_add_eq_sub]
      by_cases hq : (x : V ⧸ Λ') = q
      · rw [if_pos hq, Set.indicator_of_mem (show x ∈ {z | z - q.out ∈ Λ'} from this.2 hq)]
      · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {z | z - q.out ∈ Λ'} from
          fun h' => hq (this.1 h'))]
    simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    split_ifs with hxT
    · obtain ⟨y, hy, hqy⟩ := hrep _ hxT
      have e1 := hconst y hy _ hqy
      rw [add_sub_cancel] at e1
      have hxo : x - (x : V ⧸ Λ').out ∈ Λ' := by
        have := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (x : V ⧸ Λ'))
        rwa [neg_add_eq_sub] at this
      have e2 := hconst y hy _ (Λ'.add_mem hxo hqy)
      rw [show y + (x - (x : V ⧸ Λ').out + ((x : V ⧸ Λ').out - y)) = x by abel] at e2
      rw [e1, e2]
    · by_contra hne
      have hxK : x ∈ tsupport φ := subset_tsupport φ (Ne.symm hne)
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht2 hxK)
      apply hxT
      refine Finset.mem_image.2 ⟨y, hy, ?_⟩
      exact QuotientAddGroup.eq.2 (by rw [neg_add_eq_sub]; exact hxy)
  rw [heq] at hsum
  exact ⟨_, hsum.2.1, hsum.2.2⟩


end Cos

end PI.VolStabSW
end
end
