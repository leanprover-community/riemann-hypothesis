import Mathlib
import GroundTheory.LocalFields.LocalFourier
import GroundTheory.LocalFields.PadicLogHom

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Order

variable (K) in
theorem exists_units_ord_eq_one : ∃ π : Kˣ, ord (π : K) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨Units.mk0 _ h0, by rw [Units.val_mk0]; exact ord_uniformizer hϖ⟩

variable (K) in

def unifUnit : Kˣ := (exists_units_ord_eq_one K).choose

theorem ord_unifUnit : ord (unifUnit K : K) = 1 := (exists_units_ord_eq_one K).choose_spec

theorem ord_units_mul (u v : Kˣ) : ord ((u * v : Kˣ) : K) = ord (u : K) + ord (v : K) := by
  rw [Units.val_mul, ord_mul u.ne_zero v.ne_zero]

theorem ord_units_zpow (u : Kˣ) (k : ℤ) : ord ((u ^ k : Kˣ) : K) = k * ord (u : K) := by
  rw [Units.val_zpow_eq_zpow_val]
  simp [ord, map_zpow₀, WithZero.log_zpow]

theorem ord_units_inv (u : Kˣ) : ord ((u⁻¹ : Kˣ) : K) = -ord (u : K) := by
  rw [Units.val_inv_eq_inv_val, ord_inv u.ne_zero]

theorem ord_unifUnit_zpow (k : ℤ) : ord ((unifUnit K ^ k : Kˣ) : K) = k := by
  rw [ord_units_zpow, ord_unifUnit, mul_one]

theorem valuation_eq_one_iff_ord_eq_zero {x : K} (hx : x ≠ 0) :
    valuation K x = 1 ↔ ord x = 0 := by
  have h0 := mem_valBall_iff_le_ord (n := 0) hx
  have h1 := mem_valBall_iff_le_ord (n := 1) hx
  rw [mem_valBall_zero_iff, Valuation.mem_integer_iff] at h0
  rw [mem_valBall_one_iff] at h1
  constructor
  · intro h
    have a := h0.mp h.le
    have b : ¬ 1 ≤ ord x := fun hb => (h1.mpr hb).ne h
    omega
  · intro h
    refine le_antisymm (h0.mpr h.ge) (not_lt.mp fun hl => ?_)
    have := h1.mp hl
    omega

theorem mem_unitFiltrationUnits_zero_iff_ord {u : Kˣ} :
    u ∈ unitFiltrationUnits K 0 ↔ ord (u : K) = 0 := by
  rw [mem_unitFiltrationUnits_zero_iff, valuation_eq_one_iff_ord_eq_zero u.ne_zero]

end Order

section Shell

variable (K) in

def ordShell (k : ℤ) : Set Kˣ := {u | ord (u : K) = k}

theorem mem_ordShell {k : ℤ} {u : Kˣ} : u ∈ ordShell K k ↔ ord (u : K) = k := Iff.rfl

theorem ordShell_zero : ordShell K 0 = (unitFiltrationUnits K 0 : Set Kˣ) := by
  ext u
  rw [SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff_ord]
  rfl

theorem mul_mem_ordShell_iff (v : Kˣ) {k : ℤ} {u : Kˣ} :
    v * u ∈ ordShell K (ord (v : K) + k) ↔ u ∈ ordShell K k := by
  simp only [mem_ordShell, ord_units_mul]
  omega

theorem pairwise_disjoint_ordShell : Pairwise (Function.onFun Disjoint (ordShell K)) := by
  intro i j hij
  exact Set.disjoint_left.mpr fun u hi hj => hij (hi.symm.trans hj)

theorem iUnion_ordShell : ⋃ k, ordShell K k = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.mem_iUnion.mpr ⟨_, rfl⟩

end Shell

section Measure

variable [MeasurableSpace K] [BorelSpace K]

theorem measurable_units_val : Measurable (Units.val : Kˣ → K) :=
  measurableEmbedding_units_val.measurable

instance instMeasurableMul₂UnitsLocalField : MeasurableMul₂ Kˣ where
  measurable_mul := by
    rw [← measurableEmbedding_units_val.measurable_comp_iff]
    have : (Units.val ∘ fun p : Kˣ × Kˣ => p.1 * p.2) = fun p => (p.1 : K) * (p.2 : K) := by
      funext p
      simp
    rw [this]
    exact (measurable_units_val.comp measurable_fst).mul (measurable_units_val.comp measurable_snd)

instance instBorelSpaceUnitsLocalField : BorelSpace Kˣ := by
  refine ⟨?_⟩
  calc (Units.instMeasurableSpace : MeasurableSpace Kˣ) = MeasurableSpace.comap Units.val (borel K) := by
        rw [← BorelSpace.measurable_eq]
        rfl
    _ = borel Kˣ := by
        rw [(Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]

theorem measurableSet_ordShell (k : ℤ) : MeasurableSet (ordShell K k) := by
  have : ordShell K k = Units.val ⁻¹' ((valBall K k : Set K) \ valBall K (k + 1)) := by
    ext u
    simp only [mem_ordShell, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      mem_valBall_iff_le_ord u.ne_zero]
    omega
  rw [this]
  exact ((measurableSet_valBall k).diff (measurableSet_valBall (k + 1))).preimage
    measurable_units_val

theorem multHaar_ordShell (k : ℤ) : multHaar K (ordShell K k) = 1 := by
  have h : (fun u => unifUnit K ^ k * u) ⁻¹' ordShell K k = ordShell K 0 := by
    ext u
    have := mul_mem_ordShell_iff (K := K) (unifUnit K ^ k) (k := 0) (u := u)
    rwa [ord_unifUnit_zpow, add_zero] at this
  rw [← measure_preimage_mul (multHaar K) (unifUnit K ^ k), h, ordShell_zero,
    multHaar_unitFiltrationUnits_zero]

instance instSigmaFiniteMultHaar : SigmaFinite (multHaar K) := by
  refine Measure.sigmaFinite_of_countable (S := Set.range (ordShell K)) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    rw [multHaar_ordShell]
    exact ENNReal.one_lt_top
  · rw [Set.sUnion_range, iUnion_ordShell]

theorem lintegral_multHaar_eq_tsum (g : Kˣ → ℝ≥0∞) :
    ∫⁻ u, g u ∂multHaar K = ∑' k : ℤ, ∫⁻ u in ordShell K k, g u ∂multHaar K := by
  rw [← lintegral_iUnion measurableSet_ordShell pairwise_disjoint_ordShell, iUnion_ordShell,
    Measure.restrict_univ]

theorem lintegral_multHaar_le_tsum (g : Kˣ → ℝ≥0∞) (a : ℤ → ℝ≥0∞)
    (h : ∀ u, g u ≤ a (ord (u : K))) : ∫⁻ u, g u ∂multHaar K ≤ ∑' k, a k := by
  rw [lintegral_multHaar_eq_tsum]
  refine ENNReal.tsum_le_tsum fun k => ?_
  calc ∫⁻ u in ordShell K k, g u ∂multHaar K ≤ ∫⁻ _ in ordShell K k, a k ∂multHaar K :=
        setLIntegral_mono' (measurableSet_ordShell k) fun u hu => (h u).trans_eq (by rw [hu])
    _ = a k := by rw [setLIntegral_const, multHaar_ordShell, mul_one]

theorem hasSum_setIntegral_ordShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Kˣ → E} (hF : Integrable F (multHaar K)) :
    HasSum (fun k : ℤ => ∫ u in ordShell K k, F u ∂multHaar K) (∫ u, F u ∂multHaar K) := by
  have := hasSum_integral_iUnion (μ := multHaar K) (measurableSet_ordShell (K := K))
    (pairwise_disjoint_ordShell (K := K)) (by rw [iUnion_ordShell]; exact hF.integrableOn)
  rwa [iUnion_ordShell, Measure.restrict_univ] at this

theorem setIntegral_ordShell_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Kˣ → E) (v : Kˣ) (k : ℤ) :
    ∫ u in ordShell K (ord (v : K) + k), F u ∂multHaar K =
      ∫ u in ordShell K k, F (v * u) ∂multHaar K := by
  rw [← integral_indicator (measurableSet_ordShell _), ← integral_indicator (measurableSet_ordShell _),
    ← integral_mul_left_eq_self _ v]
  congr 1
  funext u
  by_cases hu : u ∈ ordShell K k
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((mul_mem_ordShell_iff v).mpr hu)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt (mul_mem_ordShell_iff v).mp hu)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] in

theorem integral_eq_zero_of_mul_eq {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (F : G → ℂ) (v : G) {a : ℂ} (ha : a ≠ 1)
    (hF : ∀ u, F (v * u) = a * F u) : ∫ u, F u ∂μ = 0 := by
  refine eq_zero_of_eq_mul_of_ne_one ha ?_
  calc ∫ u, F u ∂μ = ∫ u, F (v * u) ∂μ := (integral_mul_left_eq_self F v).symm
    _ = ∫ u, a * F u ∂μ := by simp only [hF]
    _ = a * ∫ u, F u ∂μ := integral_const_mul a _

theorem setIntegral_ordShell_eq_zero (F : Kˣ → ℂ) {v : Kˣ} (hv : ord (v : K) = 0) {a : ℂ}
    (ha : a ≠ 1) (k : ℤ) (hF : ∀ u ∈ ordShell K k, F (v * u) = a * F u) :
    ∫ u in ordShell K k, F u ∂multHaar K = 0 := by
  rw [← integral_indicator (measurableSet_ordShell k)]
  refine integral_eq_zero_of_mul_eq _ _ v ha fun u => ?_
  have hiff : v * u ∈ ordShell K k ↔ u ∈ ordShell K k := by
    have := mul_mem_ordShell_iff (K := K) v (k := k) (u := u)
    rwa [hv, zero_add] at this
  by_cases hu : u ∈ ordShell K k
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hiff.mpr hu), hF u hu]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hiff.mp hu), mul_zero]

end Measure

section Power

theorem residueCard_pos_real : (0 : ℝ) < residueCard K := by
  exact_mod_cast zero_lt_one.trans one_lt_residueCard

theorem residueCard_ne_zero_complex : (residueCard K : ℂ) ≠ 0 := by
  exact_mod_cast residueCard_ne_zero

theorem modulus_cpow_eq_zpow (u : Kˣ) (s : ℂ) :
    ((modulus (u : K) : ℝ) : ℂ) ^ s = ((residueCard K : ℂ) ^ (-s)) ^ ord (u : K) := by
  have hq := residueCard_pos_real (K := K)
  rw [modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]
  have hpos : (0 : ℝ) < (residueCard K : ℝ) ^ (-ord (u : K)) := zpow_pos hq _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex, ← Complex.exp_int_mul,
    ← Complex.ofReal_log hpos.le, Real.log_zpow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hq.le]
  push_cast
  ring_nf

theorem norm_qpow (s : ℂ) : ‖(residueCard K : ℂ) ^ (-s)‖ = (residueCard K : ℝ) ^ (-s.re) := by
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos residueCard_pos_real,
    Complex.neg_re]

theorem qpow_ne_zero (s : ℂ) : (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex]
  exact Complex.exp_ne_zero _

end Power

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Decomposition

theorem unifUnit_zpow_neg_mul_mem (u : Kˣ) :
    unifUnit K ^ (-ord (u : K)) * u ∈ unitFiltrationUnits K 0 := by
  rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_unifUnit_zpow]
  ring

theorem eq_unifUnit_zpow_mul (u : Kˣ) :
    u = unifUnit K ^ ord (u : K) * (unifUnit K ^ (-ord (u : K)) * u) := by
  rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

theorem isCompact_unitFiltrationUnits_zero :
    IsCompact (unitFiltrationUnits K 0 : Set Kˣ) := by
  have hS : IsCompact ((valBall K 0 : Set K) \ valBall K 1) :=
    (isCompact_valBall 0).diff (isOpen_valBall 1)
  have heq : (unitFiltrationUnits K 0 : Set Kˣ) =
      Units.val ⁻¹' ((valBall K 0 : Set K) \ valBall K 1) := by
    rw [← ordShell_zero]
    ext u
    simp only [mem_ordShell, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      mem_valBall_iff_le_ord u.ne_zero]
    omega
  rw [heq]
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS ?_
  rintro x ⟨-, hx⟩
  have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  exact ⟨Units.mk0 x hx0, rfl⟩

end Decomposition

section QuasiCharacter

variable (χ : Kˣ →* ℂˣ)

def IsUnramifiedChar : Prop := unitFiltrationUnits K 0 ≤ χ.ker

def quasiCharConductor : ℕ := sInf {n : ℕ | unitFiltrationUnits K n ≤ χ.ker}

def quasiCharExponent : ℝ := -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖

variable {χ}

theorem isUnramifiedChar_iff : IsUnramifiedChar χ ↔ ∀ u : Kˣ, ord (u : K) = 0 → χ u = 1 := by
  refine ⟨fun h u hu => h (mem_unitFiltrationUnits_zero_iff_ord.mpr hu), fun h u hu => ?_⟩
  exact h u (mem_unitFiltrationUnits_zero_iff_ord.mp hu)

theorem quasiChar_apply_of_isUnramified (h : IsUnramifiedChar χ) (u : Kˣ) :
    χ u = χ (unifUnit K) ^ ord (u : K) := by
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, MonoidHom.mem_ker.mp (h (unifUnit_zpow_neg_mul_mem u)), mul_one, map_zpow]

theorem quasiChar_apply_eq_of_isUnramified (h : IsUnramifiedChar χ) {π : Kˣ}
    (hπ : ord (π : K) = 1) : χ π = χ (unifUnit K) := by
  rw [quasiChar_apply_of_isUnramified h, hπ, zpow_one]

variable (hχ : Continuous χ)
include hχ

theorem exists_unitFiltrationUnits_le_ker : ∃ n, unitFiltrationUnits K n ≤ χ.ker := by
  refine exists_unitFiltrationUnits_le (GroundTheory.Global.isOpen_ker_of_noSmallSubgroups (fun W hW => ?_)
    GroundTheory.Global.Complex.units_noSmallSubgroups χ hχ)
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp hW
  exact ⟨⟨unitFiltrationUnits K n, isOpen_unitFiltrationUnits n⟩, hn⟩

theorem unitFiltrationUnits_quasiCharConductor_le_ker :
    unitFiltrationUnits K (quasiCharConductor χ) ≤ χ.ker :=
  Nat.sInf_mem (exists_unitFiltrationUnits_le_ker hχ)

theorem quasiCharConductor_eq_zero_iff : quasiCharConductor χ = 0 ↔ IsUnramifiedChar χ := by
  constructor
  · intro h
    have := unitFiltrationUnits_quasiCharConductor_le_ker hχ
    rwa [h] at this
  · intro h
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le h)

theorem exists_apply_ne_one_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) :
    ∃ v ∈ unitFiltrationUnits K (quasiCharConductor χ - 1), χ v ≠ 1 := by
  have hc : quasiCharConductor χ ≠ 0 := mt (quasiCharConductor_eq_zero_iff hχ).mp h
  have hlt : quasiCharConductor χ - 1 < quasiCharConductor χ := by omega
  have hnot := Nat.notMem_of_lt_sInf hlt
  by_contra hcon
  push_neg at hcon
  exact hnot fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)

omit hχ in
theorem quasiCharConductor_pos (hχ : Continuous χ) (h : ¬ IsUnramifiedChar χ) :
    0 < quasiCharConductor χ :=
  Nat.pos_of_ne_zero (mt (quasiCharConductor_eq_zero_iff hχ).mp h)

theorem norm_quasiChar_apply_eq_one {u : Kˣ} (hu : u ∈ unitFiltrationUnits K 0) :
    ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have hcont : Continuous fun v : Kˣ => ‖((χ v : ℂˣ) : ℂ)‖ :=
    (Units.continuous_val.comp hχ).norm
  obtain ⟨C, hC⟩ := isCompact_unitFiltrationUnits_zero.exists_bound_of_continuousOn
    hcont.continuousOn
  have key : ∀ v ∈ unitFiltrationUnits K 0, ‖((χ v : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists
    have := hC (v ^ n) (pow_mem hv n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), map_pow, Units.val_pow_eq_pow_val,
      norm_pow] at this
    linarith
  have h1 := key u hu
  have h2 := key u⁻¹ (inv_mem hu)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ u : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ u).ne_zero
  have : 1 ≤ ‖((χ u : ℂˣ) : ℂ)‖ := by rwa [inv_le_one₀ hpos] at h2
  linarith

theorem norm_quasiChar_apply (u : Kˣ) :
    ‖((χ u : ℂˣ) : ℂ)‖ = (modulus (u : K) : ℝ) ^ quasiCharExponent χ := by
  have hq := residueCard_pos_real (K := K)
  have hq1 : (residueCard K : ℝ) ≠ 1 := by exact_mod_cast (one_lt_residueCard (K := K)).ne'
  have hr : 0 < ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ _).ne_zero
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, Units.val_mul, norm_mul,
    norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow,
    Units.val_zpow_eq_zpow_val, norm_zpow, modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow,
    NNReal.coe_natCast, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le,
    quasiCharExponent]
  rw [show ((-ord (u : K) : ℤ) : ℝ) * -Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ =
      Real.logb (residueCard K) ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ * (ord (u : K) : ℝ) by push_cast; ring,
    Real.rpow_mul hq.le, Real.rpow_logb hq hq1 hr]

omit hχ in
theorem continuous_quasiChar_inv (hχ : Continuous χ) : Continuous (χ⁻¹ : Kˣ →* ℂˣ) := by
  have : ((χ⁻¹ : Kˣ →* ℂˣ) : Kˣ → ℂˣ) = fun u => (χ u)⁻¹ := by
    funext u
    rfl
  rw [this]
  exact hχ.inv

omit hχ in

theorem quasiCharExponent_inv : quasiCharExponent χ⁻¹ = -quasiCharExponent χ := by
  simp only [quasiCharExponent, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv,
    Real.logb_inv, neg_neg]

end QuasiCharacter

section ShellIntegral

variable [MeasurableSpace K] [BorelSpace K] {χ : Kˣ →* ℂˣ}

open scoped Classical in

theorem setIntegral_ordShell_quasiChar (hχ : Continuous χ) (k : ℤ) :
    ∫ u in ordShell K k, ((χ u : ℂˣ) : ℂ) ∂multHaar K =
      if IsUnramifiedChar χ then ((χ (unifUnit K) : ℂˣ) : ℂ) ^ k else 0 := by
  have hk : ord ((unifUnit K ^ k : Kˣ) : K) + 0 = k := by rw [ord_unifUnit_zpow, add_zero]
  have e := setIntegral_ordShell_mul (fun u : Kˣ => ((χ u : ℂˣ) : ℂ)) (unifUnit K ^ k) 0
  rw [hk] at e
  rw [e]
  simp only [map_mul, Units.val_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  rw [integral_const_mul]
  split_ifs with h
  · have hone : ∀ u ∈ ordShell K 0, ((χ u : ℂˣ) : ℂ) = 1 := fun u hu => by
      rw [(isUnramifiedChar_iff.mp h) u hu, Units.val_one]
    rw [setIntegral_congr_fun (measurableSet_ordShell 0) hone, setIntegral_const,
      measureReal_def, multHaar_ordShell, ENNReal.toReal_one, one_smul, mul_one]
  · obtain ⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits K 0, χ v ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact h fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)
    rw [setIntegral_ordShell_eq_zero (fun u => ((χ u : ℂˣ) : ℂ))
      (mem_unitFiltrationUnits_zero_iff_ord.mp hv) (a := ((χ v : ℂˣ) : ℂ))
      (fun h1 => hv1 (Units.val_eq_one.mp h1)) 0 (fun u _ => by simp), mul_zero]

end ShellIntegral

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Laurent

variable (K) in

def qpowUnit (s : ℂ) : ℂˣ := Units.mk0 ((residueCard K : ℂ) ^ (-s)) (qpow_ne_zero s)

variable (K) in

def evalQpow (P : LaurentPolynomial ℂ) (s : ℂ) : ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) (qpowUnit K s) P

theorem evalQpow_C_mul_T (a : ℂ) (n : ℤ) (s : ℂ) :
    evalQpow K (LaurentPolynomial.C a * LaurentPolynomial.T n) s =
      a * ((residueCard K : ℂ) ^ (-s)) ^ n := by
  rw [evalQpow, LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]
  rfl

theorem evalQpow_add (P Q : LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (P + Q) s = evalQpow K P s + evalQpow K Q s := map_add _ _ _

theorem evalQpow_mul (P Q : LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (P * Q) s = evalQpow K P s * evalQpow K Q s := map_mul _ _ _

theorem evalQpow_sub (P Q : LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (P - Q) s = evalQpow K P s - evalQpow K Q s := map_sub _ _ _

theorem evalQpow_one (s : ℂ) : evalQpow K 1 s = 1 := map_one _


theorem evalQpow_sum {ι : Type*} (t : Finset ι) (P : ι → LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (∑ i ∈ t, P i) s = ∑ i ∈ t, evalQpow K (P i) s := map_sum _ _ _

theorem differentiable_qpow : Differentiable ℂ fun s : ℂ => (residueCard K : ℂ) ^ (-s) :=
  differentiable_neg.const_cpow (Or.inl residueCard_ne_zero_complex)

theorem differentiable_evalQpow (P : LaurentPolynomial ℂ) : Differentiable ℂ (evalQpow K P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    have : evalQpow K (p + q) = fun s => evalQpow K p s + evalQpow K q s :=
      funext fun s => evalQpow_add p q s
    rw [this]
    exact hp.add hq
  | C_mul_T n a =>
    have : evalQpow K (LaurentPolynomial.C a * LaurentPolynomial.T n) =
        fun s => a * ((residueCard K : ℂ) ^ (-s)) ^ n :=
      funext fun s => evalQpow_C_mul_T a n s
    rw [this]
    exact (differentiable_qpow.zpow (Or.inl fun s => qpow_ne_zero s)).const_mul a

end Laurent

section Sums

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem hasSum_int_of_shift {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {a : ℤ → E}
    (M : ℤ) (h : ∀ k, k < M → a k = 0) {x : E} (hx : HasSum (fun n : ℕ => a (M + n)) x) :
    HasSum a x := by
  have hinj : Function.Injective (fun n : ℕ => M + (n : ℤ)) := fun m n hmn => by
    simpa using hmn
  refine (hinj.hasSum_iff fun k hk => h k ?_).mp hx
  by_contra hle
  push Not at hle
  exact hk ⟨(k - M).toNat, by simp only; omega⟩

end Sums

section LFactor

variable (χ : Kˣ →* ℂˣ)

open Classical in

def localLFactor (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
  else 1

variable {χ}

theorem localLFactor_of_isUnramified (h : IsUnramifiedChar χ) (s : ℂ) :
    localLFactor χ s = (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ := by
  simp [localLFactor, h]

theorem localLFactor_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localLFactor χ s = 1 := by
  simp [localLFactor, h]

variable (hχ : Continuous χ)
include hχ

theorem norm_quasiChar_unifUnit :
    ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ = (residueCard K : ℝ) ^ (-quasiCharExponent χ) := by
  rw [norm_quasiChar_apply hχ, modulus_of_ne_zero (unifUnit K).ne_zero, ord_unifUnit,
    NNReal.coe_zpow, NNReal.coe_natCast, ← Real.rpow_intCast,
    ← Real.rpow_mul residueCard_pos_real.le]
  congr 1
  push_cast
  ring

theorem norm_quasiChar_unifUnit_mul_qpow_lt_one {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, norm_quasiChar_unifUnit hχ, norm_qpow, ← Real.rpow_add residueCard_pos_real]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_residueCard) (by linarith)

theorem one_sub_quasiChar_unifUnit_mul_qpow_ne_zero {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  rw [← sub_eq_zero.mp h, norm_one] at this
  exact lt_irrefl _ this

theorem localLFactor_ne_zero {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    localLFactor χ s ≠ 0 := by
  by_cases h : IsUnramifiedChar χ
  · rw [localLFactor_of_isUnramified h]
    exact inv_ne_zero (one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hχ hs)
  · rw [localLFactor_of_not_isUnramified h]
    exact one_ne_zero

theorem norm_quasiChar_mul_modulus_cpow (u : Kˣ) (s : ℂ) :
    ‖((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s‖ =
      ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ ^ ord (u : K) := by
  have hχu : ‖((χ u : ℂˣ) : ℂ)‖ = ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ ^ ord (u : K) := by
    have e := congrArg (fun v => ‖((χ v : ℂˣ) : ℂ)‖) (eq_unifUnit_zpow_mul u)
    rw [e, map_mul, Units.val_mul, norm_mul,
      norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  rw [norm_mul, hχu, modulus_cpow_eq_zpow, norm_zpow, ← mul_zpow, ← norm_mul]

end LFactor

section ZetaNonvanishing₂

variable [MeasurableSpace K] [BorelSpace K]

def localZeta (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ u, f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K

variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}

omit [MeasurableSpace K] [BorelSpace K] in
theorem continuous_localZeta_integrand (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) (s : ℂ) :
    Continuous fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s := by
  refine ((hf.1.continuous.comp Units.continuous_val).mul (Units.continuous_val.comp hχ)).mul ?_
  refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)

theorem integrable_localZeta (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    Integrable (fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s)
      (multHaar K) := by
  obtain ⟨-, M, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  set ρ := ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ with hρ
  have hρ1 : ρ < 1 := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  have hρ0 : 0 < ρ := norm_pos_iff.mpr (mul_ne_zero (χ _).ne_zero (qpow_ne_zero s))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨(continuous_localZeta_integrand hf hχ s).aestronglyMeasurable, ?_⟩
  let a : ℤ → ℝ := fun k => if M ≤ k then C * ρ ^ k else 0
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [a]
    split_ifs
    · exact mul_nonneg hC0 (zpow_nonneg hρ0.le _)
    · exact le_rfl
  have hsum : HasSum a (C * ρ ^ M * (1 - ρ)⁻¹) := by
    refine hasSum_int_of_shift M (fun k hk => by simp [a, not_le.mpr hk]) ?_
    have e : (fun n : ℕ => a (M + n)) = fun n : ℕ => C * ρ ^ M * ρ ^ n := by
      funext n
      simp only [a, le_add_iff_nonneg_right, Nat.cast_nonneg, if_true]
      rw [zpow_add₀ hρ0.ne', zpow_natCast, mul_assoc]
    rw [e]
    exact (hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hbound : ∀ u : Kˣ,
      ‖f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s‖ₑ ≤
        ENNReal.ofReal (a (ord (u : K))) := by
    intro u
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc, norm_mul, norm_quasiChar_mul_modulus_cpow hχ]
    simp only [a]
    split_ifs with hk
    · exact mul_le_mul_of_nonneg_right (hC _) (zpow_nonneg hρ0.le _)
    · have : f u = 0 := by
        by_contra h0
        exact hk ((mem_valBall_iff_le_ord u.ne_zero).mp (hM _ h0))
      rw [this, norm_zero, zero_mul]
  refine (lintegral_multHaar_le_tsum _ (fun k => ENNReal.ofReal (a k)) hbound).trans_lt ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hsum.summable]
  exact ENNReal.ofReal_lt_top

open scoped Classical in

theorem localZeta_eq_sum (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {M N : ℤ} (hMN : M ≤ N)
    (hM : ∀ x, f x ≠ 0 → x ∈ valBall K M) (hN : ∀ x ∈ valBall K N, f x = f 0) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    localZeta f χ s =
      ∑ k ∈ Finset.Ico M N, (∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K) *
          ((residueCard K : ℂ) ^ (-s)) ^ k +
        if IsUnramifiedChar χ then
          f 0 * (((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N *
            (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
        else 0 := by
  set T := (residueCard K : ℂ) ^ (-s) with hT
  set α := ((χ (unifUnit K) : ℂˣ) : ℂ) with hα
  let Z : ℤ → ℂ := fun k => ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K
  have hsum := hasSum_setIntegral_ordShell (integrable_localZeta hf hχ hs)
  have hterm : ∀ k, ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K = Z k * T ^ k := by
    intro k
    simp only [Z]
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    rw [modulus_cpow_eq_zpow, mem_ordShell.mp hu]
  simp only [hterm] at hsum
  have hlow : ∀ k, k < M → Z k = 0 := by
    intro k hk
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    have : f u = 0 := by
      by_contra h0
      have := (mem_valBall_iff_le_ord u.ne_zero).mp (hM _ h0)
      rw [mem_ordShell.mp hu] at this
      omega
    rw [this, zero_mul]
  have hhigh : ∀ k, N ≤ k → Z k = f 0 * (if IsUnramifiedChar χ then α ^ k else 0) := by
    intro k hk
    rw [← setIntegral_ordShell_quasiChar hχ k, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    rw [hN u ((mem_valBall_iff_le_ord u.ne_zero).mpr (by rw [mem_ordShell.mp hu]; exact hk))]
  have hαT : ‖α * T‖ < 1 := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  have hαT0 : α * T ≠ 0 := mul_ne_zero (χ _).ne_zero (qpow_ne_zero s)
  have h1 : HasSum (fun k => if k < N then Z k * T ^ k else 0)
      (∑ k ∈ Finset.Ico M N, Z k * T ^ k) := by
    have : HasSum (fun k => if k < N then Z k * T ^ k else 0)
        (∑ k ∈ Finset.Ico M N, if k < N then Z k * T ^ k else 0) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
        rcases hk with hk | hk
        · simp [hlow k hk]
        · simp [not_lt.mpr hk])
    convert this using 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Ico.mp hk).2]
  have h2 : HasSum (fun k => if k < N then 0 else Z k * T ^ k)
      (if IsUnramifiedChar χ then f 0 * (α * T) ^ N * (1 - α * T)⁻¹ else 0) := by
    by_cases hu : IsUnramifiedChar χ
    · rw [if_pos hu]
      refine hasSum_int_of_shift N (fun k hk => by simp [hk]) ?_
      have e : (fun n : ℕ => if N + (n : ℤ) < N then 0 else Z (N + n) * T ^ (N + (n : ℤ))) =
          fun n : ℕ => f 0 * (α * T) ^ N * (α * T) ^ n := by
        funext n
        rw [if_neg (by omega), hhigh _ (by omega), if_pos hu, mul_assoc, ← mul_zpow,
          zpow_add₀ hαT0, zpow_natCast, mul_assoc]
      rw [e]
      exact (hasSum_geometric_of_norm_lt_one hαT).mul_left _
    · rw [if_neg hu]
      convert hasSum_zero with k
      split_ifs with hk
      · rfl
      · rw [hhigh k (not_lt.mp hk), if_neg hu, mul_zero, zero_mul]
  have h12 := h1.add h2
  have e : (fun k => (if k < N then Z k * T ^ k else 0) + (if k < N then 0 else Z k * T ^ k)) =
      fun k => Z k * T ^ k := by
    funext k
    split_ifs <;> simp
  rw [e] at h12
  exact hsum.unique h12

theorem exists_localZeta_eq_mul_evalQpow (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) :
    ∃ P : LaurentPolynomial ℂ, ∀ s : ℂ, -quasiCharExponent χ < s.re →
      localZeta f χ s = localLFactor χ s * evalQpow K P s := by
  obtain ⟨N₀, M, hN₀, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  set N := max N₀ M
  have hMN : M ≤ N := le_max_right _ _
  have hN : ∀ x ∈ valBall K N, f x = f 0 := fun x hx => by
    have := hN₀ 0 x (valBall_antitone (le_max_left _ _) hx)
    rwa [zero_add] at this
  let Z : ℤ → ℂ := fun k => ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K
  let Q : LaurentPolynomial ℂ :=
    ∑ k ∈ Finset.Ico M N, LaurentPolynomial.C (Z k) * LaurentPolynomial.T k
  have hQ : ∀ s, evalQpow K Q s = ∑ k ∈ Finset.Ico M N, Z k * ((residueCard K : ℂ) ^ (-s)) ^ k :=
    fun s => by simp only [Q, evalQpow_sum, evalQpow_C_mul_T]
  by_cases hu : IsUnramifiedChar χ
  · set α := ((χ (unifUnit K) : ℂˣ) : ℂ)
    refine ⟨(1 - LaurentPolynomial.C α * LaurentPolynomial.T 1) * Q +
      LaurentPolynomial.C (f 0 * α ^ N) * LaurentPolynomial.T N, fun s hs => ?_⟩
    rw [localZeta_eq_sum hf hχ hMN hM hN hs, if_pos hu, localLFactor_of_isUnramified hu,
      evalQpow_add, evalQpow_mul, evalQpow_sub, evalQpow_one, evalQpow_C_mul_T, evalQpow_C_mul_T,
      hQ, zpow_one]
    have hne := one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hχ hs
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_zpow]
    ring
  · refine ⟨Q, fun s hs => ?_⟩
    rw [localZeta_eq_sum hf hχ hMN hM hN hs, if_neg hu, localLFactor_of_not_isUnramified hu, hQ,
      add_zero, one_mul]

open Classical in

def localZetaRatio (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if h : ∃ P : LaurentPolynomial ℂ, ∀ s : ℂ, -quasiCharExponent χ < s.re →
      localZeta f χ s = localLFactor χ s * evalQpow K P s then
    evalQpow K h.choose s
  else 0





omit [MeasurableSpace K] [BorelSpace K] in
theorem meromorphicOn_localLFactor (χ : Kˣ →* ℂˣ) : MeromorphicOn (localLFactor χ) Set.univ := by
  intro s _
  by_cases h : IsUnramifiedChar χ
  · have e : localLFactor χ = fun s =>
        (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ :=
      funext fun s => localLFactor_of_isUnramified h s
    rw [e]
    exact ((((differentiable_qpow (K := K)).const_mul _).const_sub 1).analyticAt s).meromorphicAt.inv
  · have e : localLFactor χ = fun _ => (1 : ℂ) :=
      funext fun s => localLFactor_of_not_isUnramified h s
    rw [e]
    exact analyticAt_const.meromorphicAt


end ZetaNonvanishing₂

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

section Symmetric

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ

theorem integral_mul_localFourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) (y : K) :
    ∫ x, f x * localFourier μ ψ g (x * y) ∂μ = ∫ x, g x * localFourier μ ψ f (x * y) ∂μ := by
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have hfi := integrable_of_mem_schwartzBruhat μ hf
  have hgi := integrable_of_mem_schwartzBruhat μ hg
  let G : K → K → ℂ := fun x z => f x * (g z * (ψ (z * (x * y)) : ℂ))
  have hG : Integrable (Function.uncurry G) (μ.prod μ) := by
    have hdom : Integrable (fun p : K × K => ‖f p.1‖ * ‖g p.2‖) (μ.prod μ) :=
      hfi.norm.mul_prod hgi.norm
    refine hdom.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun p => ?_)
    · exact (hf.1.continuous.comp continuous_fst).mul ((hg.1.continuous.comp continuous_snd).mul
        (hψc.comp (continuous_snd.mul (continuous_fst.mul continuous_const))))
    · simp [G, Function.uncurry, Circle.norm_coe]
  have e1 : ∫ x, f x * localFourier μ ψ g (x * y) ∂μ = ∫ x, ∫ z, G x z ∂μ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [localFourier, G]
    rw [integral_const_mul]
  have e2 : ∫ x, g x * localFourier μ ψ f (x * y) ∂μ = ∫ z, ∫ x, G x z ∂μ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [localFourier, G]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [show x * (z * y) = z * (x * y) by ring]
    ring
  rw [e1, e2, integral_integral_swap hG]

end Symmetric

section Multiplicative

theorem haarIntegers_singleton_zero : haarIntegers K {0} = 0 := by
  have hq : (1 : ℝ≥0) < (residueCard K : ℝ≥0) := one_lt_residueCard_nnreal
  have ht : Tendsto (fun n : ℕ => (((residueCard K : ℝ≥0) ^ (-(n : ℤ)) : ℝ≥0) : ℝ≥0∞)) atTop
      (𝓝 0) := by
    rw [← ENNReal.coe_zero, ENNReal.tendsto_coe]
    have e : (fun n : ℕ => (residueCard K : ℝ≥0) ^ (-(n : ℤ))) =
        fun n : ℕ => ((residueCard K : ℝ≥0)⁻¹) ^ n := by
      funext n
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [e]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (inv_lt_one_of_one_lt₀ hq)
  refine le_antisymm (ge_of_tendsto' ht fun n => ?_) (by simp)
  rw [← haarIntegers_valBall]
  exact measure_mono (Set.singleton_subset_iff.mpr (zero_mem _))

theorem integral_multHaar_mul_modulus (h : K → ℂ) :
    ∫ u, h u * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      (multHaarConst K).toReal * ∫ x, h x ∂haarIntegers K := by
  rw [integral_multHaar (fun x => h x * ((modulus x : ℝ) : ℂ)), Complex.real_smul]
  congr 1
  have hae : ∀ᵐ x ∂haarIntegers K, x ∈ ({0}ᶜ : Set K) := by
    rw [ae_iff]
    simpa using haarIntegers_singleton_zero (K := K)
  conv_rhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]
  refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have hm : ((modulus x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos hx).ne'
  rw [Complex.real_smul, Complex.ofReal_inv, mul_comm, mul_assoc, mul_inv_cancel₀ hm, mul_one]

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ

theorem integral_multHaar_mul_localFourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) (y : K) :
    ∫ u, f u * localFourier μ ψ g ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      ∫ u, g u * localFourier μ ψ f ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K := by
  rw [integral_multHaar_mul_modulus (fun x => f x * localFourier μ ψ g (x * y)),
    integral_multHaar_mul_modulus (fun x => g x * localFourier μ ψ f (x * y))]
  congr 1
  have hμ := eq_smul_haarIntegers μ
  have key := integral_mul_localFourier_comm μ hψ hf hg y
  have hc : (μ (𝒪[K] : Set K)).toReal ≠ 0 := by
    refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
    · rw [← coe_valBall_zero]
      exact ((isOpen_valBall 0).measure_pos μ ⟨0, zero_mem _⟩).ne'
    · rw [← coe_valBall_zero]
      exact (isCompact_valBall 0).measure_lt_top.ne
  have hJ : ∀ F : K → ℂ, ∫ x, F x ∂μ = ((μ (𝒪[K] : Set K)).toReal : ℂ) * ∫ x, F x ∂haarIntegers K :=
    fun F => by
      conv_lhs => rw [hμ]
      rw [integral_smul_measure, Complex.real_smul]
  rw [hJ, hJ] at key
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc) key

end Multiplicative

section Tate

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
  (hψ1 : ψ ≠ 1) {χ : Kˣ →* ℂˣ} (hχ : Continuous χ)
include hψ hψ1 hχ

theorem localZeta_mul_localZeta_fourier_eq {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s) =
      ∫ y, ((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
        ∫ x, f x * localFourier μ ψ g ((x : K) * (y : K)) * ((modulus (x : K) : ℝ) : ℂ)
          ∂multHaar K ∂multHaar K := by
  set F₁ : Kˣ → ℂ := fun u => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s
  set G₁ : Kˣ → ℂ := fun u => localFourier μ ψ g u * (((χ⁻¹) u : ℂˣ) : ℂ) *
    ((modulus (u : K) : ℝ) : ℂ) ^ (1 - s)
  have hF₁ : Integrable F₁ (multHaar K) := integrable_localZeta hf hχ hs1
  have hG₁ : Integrable G₁ (multHaar K) :=
    integrable_localZeta (localFourier_mem_schwartzBruhat μ hψ hψ1 hg) (continuous_quasiChar_inv hχ)
      (by rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]; linarith)
  have hP : Integrable (fun p : Kˣ × Kˣ => F₁ p.1 * G₁ p.2) ((multHaar K).prod (multHaar K)) :=
    hF₁.mul_prod hG₁
  have hH : Integrable (Function.uncurry fun x y : Kˣ => F₁ x * G₁ (x * y))
      ((multHaar K).prod (multHaar K)) :=
    (measurePreserving_prod_mul (multHaar K) (multHaar K)).integrable_comp_of_integrable hP
  have hpt : ∀ x y : Kˣ, F₁ x * G₁ (x * y) =
      ((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
        (f x * localFourier μ ψ g ((x : K) * (y : K)) * ((modulus (x : K) : ℝ) : ℂ)) := by
    intro x y
    have hx0 : ((modulus (x : K) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos x.ne_zero).ne'
    have e1 : (((χ⁻¹) (x * y) : ℂˣ) : ℂ) = ((χ x : ℂˣ) : ℂ)⁻¹ * ((χ y : ℂˣ) : ℂ)⁻¹ := by
      rw [MonoidHom.inv_apply, map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val]
    have e2 : ((modulus ((x * y : Kˣ) : K) : ℝ) : ℂ) ^ (1 - s) =
        ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) := by
      rw [Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    have e3 : ((modulus (x : K) : ℝ) : ℂ) ^ s * ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) =
        ((modulus (x : K) : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hx0, add_sub_cancel, Complex.cpow_one]
    have hχx : ((χ x : ℂˣ) : ℂ) * ((χ x : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (χ x).ne_zero
    simp only [F₁, G₁]
    rw [e1, e2, Units.val_mul]
    calc f x * ((χ x : ℂˣ) : ℂ) * ((modulus (x : K) : ℝ) : ℂ) ^ s *
          (localFourier μ ψ g ((x : K) * (y : K)) * (((χ x : ℂˣ) : ℂ)⁻¹ * ((χ y : ℂˣ) : ℂ)⁻¹) *
            (((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s)))
        = (((χ x : ℂˣ) : ℂ) * ((χ x : ℂˣ) : ℂ)⁻¹) *
            (((modulus (x : K) : ℝ) : ℂ) ^ s * ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s)) *
            (((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
              (f x * localFourier μ ψ g ((x : K) * (y : K)))) := by ring
      _ = _ := by rw [hχx, e3]; ring
  calc localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s)
      = (∫ x, F₁ x ∂multHaar K) * ∫ y, G₁ y ∂multHaar K := rfl
    _ = ∫ x, F₁ x * ∫ y, G₁ y ∂multHaar K ∂multHaar K := (integral_mul_const _ _).symm
    _ = ∫ x, ∫ y, F₁ x * G₁ (x * y) ∂multHaar K ∂multHaar K := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [integral_const_mul, integral_mul_left_eq_self G₁ x]
    _ = ∫ y, ∫ x, F₁ x * G₁ (x * y) ∂multHaar K ∂multHaar K := integral_integral_swap hH
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hpt]
        rw [integral_const_mul]

theorem localZeta_mul_localZeta_fourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s) =
      localZeta g χ s * localZeta (localFourier μ ψ f) χ⁻¹ (1 - s) := by
  rw [localZeta_mul_localZeta_fourier_eq μ hψ hψ1 hχ hf hg hs1 hs2,
    localZeta_mul_localZeta_fourier_eq μ hψ hψ1 hχ hg hf hs1 hs2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_multHaar_mul_localFourier_comm μ hψ hf hg]

end Tate

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Powers

theorem qcpow_zpow (z : ℂ) (n : ℤ) :
    ((residueCard K : ℂ) ^ z) ^ n = (residueCard K : ℂ) ^ ((n : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex,
    Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex, ← Complex.exp_int_mul]
  ring_nf

theorem qcpow_mul_qcpow (a b : ℂ) :
    (residueCard K : ℂ) ^ a * (residueCard K : ℂ) ^ b = (residueCard K : ℂ) ^ (a + b) :=
  (Complex.cpow_add _ _ residueCard_ne_zero_complex).symm

theorem modulus_cpow_eq_qcpow {x : K} (hx : x ≠ 0) (z : ℂ) :
    ((modulus x : ℝ) : ℂ) ^ z = (residueCard K : ℂ) ^ (-(ord x : ℂ) * z) := by
  have := modulus_cpow_eq_zpow (Units.mk0 x hx) z
  rw [Units.val_mk0] at this
  rw [this, qcpow_zpow]
  congr 1
  ring

theorem ofReal_qrpow (r : ℝ) :
    (((residueCard K : ℝ) ^ r : ℝ) : ℂ) = (residueCard K : ℂ) ^ (r : ℂ) := by
  rw [Complex.ofReal_cpow residueCard_pos_real.le, Complex.ofReal_natCast]

theorem ofReal_qzpow (n : ℤ) :
    (((residueCard K : ℝ) ^ n : ℝ) : ℂ) = (residueCard K : ℂ) ^ (n : ℂ) := by
  rw [← Real.rpow_intCast, ofReal_qrpow]
  push_cast
  rfl

end Powers

section Characters

variable {χ : Kˣ →* ℂˣ}

theorem isUnramifiedChar_inv_iff : IsUnramifiedChar χ⁻¹ ↔ IsUnramifiedChar χ := by
  simp only [isUnramifiedChar_iff, MonoidHom.inv_apply, inv_eq_one]

theorem quasiCharConductor_inv : quasiCharConductor χ⁻¹ = quasiCharConductor χ := by
  have : (χ⁻¹).ker = χ.ker := by
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
  simp only [quasiCharConductor, this]

theorem unitFiltration_sub_one_mem_valBall {j : ℕ} {v : Kˣ} (hv : v ∈ unitFiltrationUnits K j) :
    (v : K) - 1 ∈ valBall K j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 : (v : K) ∈ valBall K 0 := by
      rw [mem_valBall_iff_le_ord v.ne_zero, mem_unitFiltrationUnits_zero_iff_ord.mp hv]
    have h1 : (1 : K) ∈ valBall K 0 := by
      rw [mem_valBall_iff_le_ord one_ne_zero, ord_one]
    simpa using sub_mem h0 h1
  · exact (mem_unitFiltrationUnits_iff_valBall hj).mp hv

variable (χ) in
open Classical in

def quasiCharExt (x : K) : ℂ := if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem quasiCharExt_units (u : Kˣ) : quasiCharExt χ (u : K) = ((χ u : ℂˣ) : ℂ) := by
  simp [quasiCharExt, u.ne_zero]

end Characters

section SchwartzBruhat

theorem indicator_valBall_mem_schwartzBruhat (k : ℤ) :
    (valBall K k : Set K).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat K := by
  refine ⟨isLocallyConstant_of_add_valBall (N := k) fun x h hh => ?_, ?_⟩
  · have hiff : x + h ∈ valBall K k ↔ x ∈ valBall K k :=
      ⟨fun h' => by simpa using sub_mem h' hh, fun h' => add_mem h' hh⟩
    by_cases hx : x ∈ valBall K k
    · rw [Set.indicator_of_mem (show x + h ∈ (valBall K k : Set K) from hiff.mpr hx),
        Set.indicator_of_mem (show x ∈ (valBall K k : Set K) from hx)]
    · rw [Set.indicator_of_notMem (show x + h ∉ (valBall K k : Set K) from mt hiff.mp hx),
        Set.indicator_of_notMem (show x ∉ (valBall K k : Set K) from hx)]
  · exact HasCompactSupport.intro (isCompact_valBall k) fun x hx => Set.indicator_of_notMem hx _

end SchwartzBruhat

variable [MeasurableSpace K] [BorelSpace K]

section Epsilon

open Classical in

def localEpsilon (χ : Kˣ →* ℂˣ) (ψ : AddChar K Circle) (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then
    ((χ (unifUnit K ^ addCharConductor ψ) : ℂˣ) : ℂ)⁻¹ *
      ((modulus ((unifUnit K ^ addCharConductor ψ : Kˣ) : K) : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s)
  else
    ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
        valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
      quasiCharExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-s) * (ψ x : ℂ) ∂selfDualMeasure ψ

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}

theorem localEpsilon_of_isUnramified (h : IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s = ((χ (unifUnit K) : ℂˣ) : ℂ) ^ (-addCharConductor ψ) *
      (residueCard K : ℂ) ^ ((addCharConductor ψ : ℂ) * (s - 1 / 2)) := by
  rw [localEpsilon, if_pos h, map_zpow, Units.val_zpow_eq_zpow_val, ← zpow_neg,
    modulus_cpow_eq_qcpow (unifUnit K ^ addCharConductor ψ).ne_zero, ord_unifUnit_zpow]
  congr 2
  ring

theorem localEpsilon_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s =
      ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
          valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
        quasiCharExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-s) * (ψ x : ℂ) ∂selfDualMeasure ψ := by
  rw [localEpsilon, if_neg h]

end Epsilon

section ZetaBasics

variable {χ : Kˣ →* ℂˣ}

theorem localZeta_const_mul (c : ℂ) (f : K → ℂ) (s : ℂ) :
    localZeta (fun x => c * f x) χ s = c * localZeta f χ s := by
  unfold localZeta
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

theorem localZeta_indicator_valBall_of_isUnramified (hχ : Continuous χ) (hu : IsUnramifiedChar χ)
    (k : ℤ) {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    localZeta ((valBall K k : Set K).indicator fun _ => 1) χ s =
      (((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ k * localLFactor χ s := by
  rw [localZeta_eq_sum (indicator_valBall_mem_schwartzBruhat k) hχ le_rfl
    (fun x hx => by by_contra h; exact hx (Set.indicator_of_notMem h _))
    (fun x hx => by rw [Set.indicator_of_mem hx, Set.indicator_of_mem (zero_mem _)]) hs,
    if_pos hu, Finset.Ico_self, Finset.sum_empty, zero_add,
    Set.indicator_of_mem (show (0 : K) ∈ (valBall K k : Set K) from zero_mem _), one_mul,
    localLFactor_of_isUnramified hu]

theorem localFourier_indicator_valBall (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle}
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (k : ℤ) (y : K) :
    localFourier μ ψ ((valBall K k : Set K).indicator fun _ => 1) y =
      (μ.real (valBall K k) : ℂ) *
        (valBall K (addCharConductor ψ - k) : Set K).indicator (fun _ => 1) y := by
  classical
  have e : (fun x => (valBall K k : Set K).indicator (fun _ => (1 : ℂ)) x * (ψ (x * y) : ℂ)) =
      (valBall K k : Set K).indicator fun x => ((ψ.mulShift y) x : ℂ) := by
    funext x
    by_cases hx : x ∈ (valBall K k : Set K)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul, AddChar.mulShift_apply,
        mul_comm]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  unfold localFourier
  rw [e, integral_indicator (measurableSet_valBall k), integral_valBall_char]
  by_cases hy : y ∈ valBall K (addCharConductor ψ - k)
  · rw [if_pos ((isTrivialOn_mulShift_iff_mem hψ hψ1 y k).mpr hy),
      Set.indicator_of_mem (show y ∈ (valBall K (addCharConductor ψ - k) : Set K) from hy), mul_one]
  · rw [if_neg (mt (isTrivialOn_mulShift_iff_mem hψ hψ1 y k).mp hy),
      Set.indicator_of_notMem (show y ∉ (valBall K (addCharConductor ψ - k) : Set K) from hy),
      mul_zero]

end ZetaBasics

section Unramified

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ

theorem localZeta_fourier_indicator_integers (hu : IsUnramifiedChar χ) {s : ℂ}
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta (localFourier (selfDualMeasure ψ) ψ ((valBall K 0 : Set K).indicator fun _ => 1))
        χ⁻¹ (1 - s) =
      localEpsilon χ ψ s * localLFactor χ⁻¹ (1 - s) := by
  have hs' : -quasiCharExponent χ⁻¹ < (1 - s).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have e : localFourier (selfDualMeasure ψ) ψ ((valBall K 0 : Set K).indicator fun _ => 1) =
      fun y => ((selfDualMeasure ψ).real (valBall K 0) : ℂ) *
        (valBall K (addCharConductor ψ) : Set K).indicator (fun _ => 1) y := by
    funext y
    rw [localFourier_indicator_valBall _ hψ hψ1 0 y, sub_zero]
  rw [e, localZeta_const_mul, localZeta_indicator_valBall_of_isUnramified
    (continuous_quasiChar_inv hχ) (isUnramifiedChar_inv_iff.mpr hu) _ hs',
    localEpsilon_of_isUnramified hu, selfDualMeasure_real_valBall_zero, ofReal_qrpow,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val, mul_zpow, inv_zpow', qcpow_zpow]
  calc _ = ((χ (unifUnit K) : ℂˣ) : ℂ) ^ (-addCharConductor ψ) *
        ((residueCard K : ℂ) ^ ((((addCharConductor ψ : ℝ) / 2 : ℝ)) : ℂ) *
          (residueCard K : ℂ) ^ ((addCharConductor ψ : ℂ) * -(1 - s))) *
        localLFactor χ⁻¹ (1 - s) := by ring
    _ = _ := by
      rw [qcpow_mul_qcpow, show ((((addCharConductor ψ : ℝ) / 2 : ℝ) : ℂ) +
          (addCharConductor ψ : ℂ) * -(1 - s)) = (addCharConductor ψ : ℂ) * (s - 1 / 2) by
        push_cast; ring]

end Unramified

section Ramified

def oneAddValBallIndicator (c : ℤ) : K → ℂ :=
  {x : K | x - 1 ∈ valBall K c}.indicator fun _ => 1

omit [MeasurableSpace K] [BorelSpace K] in
open Classical in
theorem oneAddValBallIndicator_apply (c : ℤ) (x : K) :
    oneAddValBallIndicator c x = if x - 1 ∈ valBall K c then 1 else 0 := by
  unfold oneAddValBallIndicator
  by_cases hx : x - 1 ∈ valBall K c
  · rw [Set.indicator_of_mem (show x ∈ {x : K | x - 1 ∈ valBall K c} from hx), if_pos hx]
  · rw [Set.indicator_of_notMem (show x ∉ {x : K | x - 1 ∈ valBall K c} from hx), if_neg hx]

omit [MeasurableSpace K] [BorelSpace K] in
theorem oneAddValBallIndicator_add_one (c : ℤ) (h : K) :
    oneAddValBallIndicator c (1 + h) = (valBall K c : Set K).indicator (fun _ => 1) h := by
  classical
  rw [oneAddValBallIndicator_apply, add_sub_cancel_left, Set.indicator_apply]
  rfl

omit [MeasurableSpace K] [BorelSpace K] in
theorem oneAddValBallIndicator_mem_schwartzBruhat {c : ℤ} (hc : 0 ≤ c) :
    oneAddValBallIndicator c ∈ schwartzBruhat K := by
  refine ⟨isLocallyConstant_of_add_valBall (N := c) fun x h hh => ?_, ?_⟩
  · have hiff : x + h - 1 ∈ valBall K c ↔ x - 1 ∈ valBall K c := by
      rw [show x + h - 1 = (x - 1) + h by ring]
      exact ⟨fun h' => by simpa using sub_mem h' hh, fun h' => add_mem h' hh⟩
    classical
    rw [oneAddValBallIndicator_apply, oneAddValBallIndicator_apply]
    exact if_congr hiff rfl rfl
  · refine HasCompactSupport.intro (isCompact_valBall 0) fun x hx => ?_
    classical
    rw [oneAddValBallIndicator_apply, if_neg]
    intro h1
    have h0 : (1 : K) ∈ valBall K 0 := by rw [mem_valBall_iff_le_ord one_ne_zero, ord_one]
    exact hx (by simpa using add_mem (valBall_antitone hc h1) h0)

theorem localFourier_oneAddValBallIndicator (μ : Measure K) [μ.IsAddHaarMeasure]
    {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (c : ℤ) (y : K) :
    localFourier μ ψ (oneAddValBallIndicator c) y =
      (ψ y : ℂ) * ((μ.real (valBall K c) : ℂ) *
        (valBall K (addCharConductor ψ - c) : Set K).indicator (fun _ => 1) y) := by
  rw [← localFourier_indicator_valBall μ hψ hψ1 c y]
  unfold localFourier
  rw [← integral_add_left_eq_self (fun x => oneAddValBallIndicator c x * (ψ (x * y) : ℂ)) 1,
    ← integral_const_mul]
  congr 1
  funext h
  rw [oneAddValBallIndicator_add_one, add_mul, one_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem setIntegral_ordShell_eq_haarIntegers (F : K → ℂ) (m : ℤ) :
    ∫ u in ordShell K m, F u ∂multHaar K =
      (((multHaarConst K).toReal * (residueCard K : ℝ) ^ m : ℝ) : ℂ) *
        ∫ x in (valBall K m : Set K) \ valBall K (m + 1), F x ∂haarIntegers K := by
  set S : Set K := (valBall K m : Set K) \ valBall K (m + 1) with hSdef
  have hS : MeasurableSet S := (measurableSet_valBall m).diff (measurableSet_valBall (m + 1))
  have hmem : ∀ u : Kˣ, u ∈ ordShell K m ↔ (u : K) ∈ S := fun u => by
    simp only [S, mem_ordShell, Set.mem_sdiff, SetLike.mem_coe, mem_valBall_iff_le_ord u.ne_zero]
    omega
  have hq : (residueCard K : ℂ) ≠ 0 := residueCard_ne_zero_complex
  let h : K → ℂ := S.indicator fun x => F x * (residueCard K : ℂ) ^ m
  have hpt : ∀ u : Kˣ, (ordShell K m).indicator (fun u : Kˣ => F u) u =
      h u * ((modulus (u : K) : ℝ) : ℂ) := by
    intro u
    simp only [h]
    by_cases hu : u ∈ ordShell K m
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((hmem u).mp hu),
        modulus_of_ne_zero u.ne_zero, mem_ordShell.mp hu]
      push_cast
      rw [mul_assoc, ← zpow_add₀ hq, add_neg_cancel, zpow_zero, mul_one]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt (hmem u).mpr hu), zero_mul]
  rw [← integral_indicator (measurableSet_ordShell m)]
  rw [show (fun u : Kˣ => (ordShell K m).indicator (fun u : Kˣ => F u) u) =
    fun u : Kˣ => h u * ((modulus (u : K) : ℝ) : ℂ) from funext hpt]
  rw [integral_multHaar_mul_modulus h, integral_indicator hS, integral_mul_const]
  push_cast
  ring

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}

theorem localZeta_oneAddValBallIndicator {c : ℕ} (hc : 1 ≤ c)
    (hker : unitFiltrationUnits K c ≤ χ.ker) (s : ℂ) :
    localZeta (oneAddValBallIndicator c) χ s =
      (multHaarConst K).toReal * (haarIntegers K).real (valBall K c) := by
  have hpt : ∀ u : Kˣ, oneAddValBallIndicator (c : ℤ) (u : K) * ((χ u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ s =
      oneAddValBallIndicator (c : ℤ) (u : K) * ((modulus (u : K) : ℝ) : ℂ) := by
    intro u
    by_cases hu : (u : K) - 1 ∈ valBall K c
    · have hU : u ∈ unitFiltrationUnits K c := (mem_unitFiltrationUnits_iff_valBall hc).mpr hu
      have hord : ord (u : K) = 0 :=
        mem_unitFiltrationUnits_zero_iff_ord.mp (unitFiltrationUnits_antitone (Nat.zero_le c) hU)
      have hmod : modulus (u : K) = 1 := modulus_eq_one_iff.mpr ⟨u.ne_zero, hord⟩
      rw [MonoidHom.mem_ker.mp (hker hU), hmod]
      simp
    · classical
      rw [oneAddValBallIndicator_apply, if_neg hu]
      simp
  unfold localZeta
  rw [show (fun u : Kˣ => oneAddValBallIndicator (c : ℤ) (u : K) * ((χ u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ s) =
    fun u : Kˣ => oneAddValBallIndicator (c : ℤ) (u : K) * ((modulus (u : K) : ℝ) : ℂ) from funext hpt,
    integral_multHaar_mul_modulus, ← integral_add_left_eq_self _ 1]
  simp only [oneAddValBallIndicator_add_one]
  rw [integral_indicator (measurableSet_valBall _), setIntegral_const, Complex.real_smul, mul_one]

theorem localZeta_oneAddValBallIndicator_ne_zero {c : ℕ} (hc : 1 ≤ c)
    (hker : unitFiltrationUnits K c ≤ χ.ker) (s : ℂ) :
    localZeta (oneAddValBallIndicator c) χ s ≠ 0 := by
  rw [localZeta_oneAddValBallIndicator hc hker]
  have h1 : (multHaarConst K).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
  have h2 : (haarIntegers K).real (valBall K c) ≠ 0 := by
    rw [measureReal_def, haarIntegers_valBall, ENNReal.coe_toReal]
    exact_mod_cast (zpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal) _).ne'
  exact_mod_cast mul_ne_zero h1 h2

theorem localEpsilon_of_not_isUnramified_eq (hr : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s =
      (residueCard K : ℂ) ^ (((addCharConductor ψ - quasiCharConductor χ : ℤ) : ℂ) * s) *
        (((residueCard K : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ) : ℂ) *
        ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
            valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
          quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K := by
  set m : ℤ := addCharConductor ψ - quasiCharConductor χ
  have hS : MeasurableSet ((valBall K m : Set K) \ valBall K (m + 1)) :=
    (measurableSet_valBall m).diff (measurableSet_valBall (m + 1))
  rw [localEpsilon_of_not_isUnramified hr]
  rw [setIntegral_congr_fun hS (g := fun x => (residueCard K : ℂ) ^ ((m : ℂ) * s) *
    (quasiCharExt χ⁻¹ x * (ψ x : ℂ))) fun x hx => by
      have hx0 : x ≠ 0 := fun h => hx.2 (h ▸ zero_mem _)
      have hord : ord x = m := by
        have a := (mem_valBall_iff_le_ord hx0).mp hx.1
        have b := mt (mem_valBall_iff_le_ord hx0).mpr hx.2
        omega
      simp only
      rw [modulus_cpow_eq_qcpow hx0, hord]
      ring_nf]
  rw [integral_const_mul, selfDualMeasure, Measure.restrict_smul, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul, NNReal.coe_rpow, NNReal.coe_natCast]
  ring

end Ramified

section RamifiedFourier

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ

theorem localZeta_fourier_oneAddValBallIndicator (hr : ¬ IsUnramifiedChar χ) {s : ℂ}
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta (localFourier (selfDualMeasure ψ) ψ (oneAddValBallIndicator (quasiCharConductor χ)))
        χ⁻¹ (1 - s) =
      localEpsilon χ ψ s * localZeta (oneAddValBallIndicator (quasiCharConductor χ)) χ s := by
  set c := quasiCharConductor χ with hcdef
  set n := addCharConductor ψ with hndef
  set m : ℤ := n - c with hmdef
  set μ := selfDualMeasure ψ
  have hc : 1 ≤ c := quasiCharConductor_pos hχ hr
  have hs' : -quasiCharExponent χ⁻¹ < (1 - s).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hr' : ¬ IsUnramifiedChar χ⁻¹ := mt isUnramifiedChar_inv_iff.mp hr
  set g := localFourier μ ψ (oneAddValBallIndicator c) with hgdef
  have hg : ∀ y, g y = (ψ y : ℂ) * ((μ.real (valBall K c) : ℂ) *
      (valBall K m : Set K).indicator (fun _ => 1) y) :=
    fun y => localFourier_oneAddValBallIndicator μ hψ hψ1 c y
  have hgSB : g ∈ schwartzBruhat K :=
    localFourier_mem_schwartzBruhat μ hψ hψ1 (oneAddValBallIndicator_mem_schwartzBruhat (by omega))
  have hmn : m ≤ n := by omega
  have hM : ∀ y, g y ≠ 0 → y ∈ valBall K m := fun y hy => by
    by_contra h
    rw [hg y, Set.indicator_of_notMem (show y ∉ (valBall K m : Set K) from h)] at hy
    simp at hy
  have hN : ∀ y ∈ valBall K n, g y = g 0 := fun y hy => by
    rw [hg y, hg 0, isTrivialOn_addCharConductor hψ hψ1 y hy, AddChar.map_zero_eq_one,
      Set.indicator_of_mem (show y ∈ (valBall K m : Set K) from valBall_antitone hmn hy),
      Set.indicator_of_mem (show (0 : K) ∈ (valBall K m : Set K) from zero_mem _)]

  obtain ⟨v, hv, hv1⟩ := exists_apply_ne_one_of_not_isUnramified hχ hr
  have hvord : ord (v : K) = 0 :=
    mem_unitFiltrationUnits_zero_iff_ord.mp (unitFiltrationUnits_antitone (Nat.zero_le _) hv)
  have hvm : (v : K) - 1 ∈ valBall K ((c - 1 : ℕ) : ℤ) := unitFiltration_sub_one_mem_valBall hv
  have hvanish : ∀ k ∈ Finset.Ico m n, k ≠ m →
      (∫ u in ordShell K k, g u * (((χ⁻¹) u : ℂˣ) : ℂ) ∂multHaar K) *
        ((residueCard K : ℂ) ^ (-(1 - s))) ^ k = 0 := by
    intro k hk hkm
    have hk1 : m + 1 ≤ k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    rw [setIntegral_ordShell_eq_zero (fun u => g u * (((χ⁻¹) u : ℂˣ) : ℂ)) hvord
      (a := ((χ v : ℂˣ) : ℂ)⁻¹) (fun h => hv1 (by
        have : ((χ v : ℂˣ) : ℂ) = 1 := inv_eq_one.mp h
        exact Units.val_eq_one.mp this)) k (fun u hu => ?_), zero_mul]
    have hu0 := u.ne_zero
    have huk : ord (u : K) = k := mem_ordShell.mp hu
    have hvu : ((v * u : Kˣ) : K) - (u : K) ∈ valBall K n := by
      rw [Units.val_mul, show (v : K) * u - u = ((v : K) - 1) * u by ring]
      have := mul_mem_valBall hvm ((mem_valBall_iff_le_ord hu0).mpr le_rfl)
      refine valBall_antitone ?_ this
      rw [huk]
      omega
    have hψvu : (ψ ((v * u : Kˣ) : K) : ℂ) = (ψ (u : K) : ℂ) := by
      have := isTrivialOn_addCharConductor hψ hψ1 _ hvu
      rw [show ((v * u : Kˣ) : K) = (u : K) + (((v * u : Kˣ) : K) - u) by ring,
        AddChar.map_add_eq_mul, this, mul_one]
    have hmemu : (u : K) ∈ valBall K m := (mem_valBall_iff_le_ord hu0).mpr (by omega)
    have hmemvu : ((v * u : Kˣ) : K) ∈ valBall K m :=
      (mem_valBall_iff_le_ord (v * u).ne_zero).mpr (by rw [ord_units_mul, hvord]; omega)
    rw [hg, hg, hψvu, Set.indicator_of_mem (show ((v * u : Kˣ) : K) ∈ (valBall K m : Set K) from hmemvu),
      Set.indicator_of_mem (show (u : K) ∈ (valBall K m : Set K) from hmemu), map_mul,
      Units.val_mul, MonoidHom.inv_apply, MonoidHom.inv_apply]
    simp only [Units.val_inv_eq_inv_val]
    ring
  have hZg : localZeta g χ⁻¹ (1 - s) =
      (∫ u in ordShell K m, g u * (((χ⁻¹) u : ℂˣ) : ℂ) ∂multHaar K) *
        ((residueCard K : ℂ) ^ (-(1 - s))) ^ m := by
    rw [localZeta_eq_sum hgSB (continuous_quasiChar_inv hχ) hmn hM hN hs', if_neg hr', add_zero,
      Finset.sum_eq_single_of_mem m (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) hvanish]

  have hshell : ∫ u in ordShell K m, g u * (((χ⁻¹) u : ℂˣ) : ℂ) ∂multHaar K =
      (μ.real (valBall K c) : ℂ) *
        ∫ u in ordShell K m, quasiCharExt χ⁻¹ (u : K) * (ψ (u : K) : ℂ) ∂multHaar K := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_ordShell m) fun u hu => ?_
    have hmemu : (u : K) ∈ valBall K m :=
      (mem_valBall_iff_le_ord u.ne_zero).mpr (by rw [mem_ordShell.mp hu])
    rw [hg, Set.indicator_of_mem (show (u : K) ∈ (valBall K m : Set K) from hmemu),
      quasiCharExt_units]
    ring
  rw [hZg, hshell, setIntegral_ordShell_eq_haarIntegers (fun x => quasiCharExt χ⁻¹ x * (ψ x : ℂ)),
    localEpsilon_of_not_isUnramified_eq hr, localZeta_oneAddValBallIndicator hc
      (unitFiltrationUnits_quasiCharConductor_le_ker hχ)]
  have hμc : μ.real (valBall K c) =
      (residueCard K : ℝ) ^ ((n : ℝ) / 2) * (haarIntegers K).real (valBall K c) := by
    simp only [μ, selfDualMeasure, measureReal_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_rpow, NNReal.coe_natCast]
    rfl
  rw [hμc, qcpow_zpow, ← hndef, ← hcdef, ← hmdef]
  set A := ∫ x in (valBall K m : Set K) \ valBall K (m + 1), quasiCharExt χ⁻¹ x * (ψ x : ℂ)
    ∂haarIntegers K
  set B := (haarIntegers K).real (valBall K c)
  set C := (multHaarConst K).toReal
  set r := (residueCard K : ℝ) ^ ((n : ℝ) / 2)
  have hpow : (residueCard K : ℂ) ^ m * (residueCard K : ℂ) ^ ((m : ℂ) * -(1 - s)) =
      (residueCard K : ℂ) ^ ((m : ℂ) * s) := by
    rw [← Complex.cpow_intCast, qcpow_mul_qcpow]
    congr 1
    ring
  push_cast
  linear_combination ((r : ℂ) * (B : ℂ) * (C : ℂ) * A) * hpow

end RamifiedFourier

section FunctionalEquation

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ

theorem exists_localZeta_test {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    ∃ g : K → ℂ, g ∈ schwartzBruhat K ∧ localZeta g χ s ≠ 0 ∧
      localZeta (localFourier (selfDualMeasure ψ) ψ g) χ⁻¹ (1 - s) * localLFactor χ s =
        localEpsilon χ ψ s * localZeta g χ s * localLFactor χ⁻¹ (1 - s) := by
  by_cases hu : IsUnramifiedChar χ
  · refine ⟨_, indicator_valBall_mem_schwartzBruhat 0, ?_, ?_⟩
    · rw [localZeta_indicator_valBall_of_isUnramified hχ hu 0 hs1, zpow_zero, one_mul]
      exact localLFactor_ne_zero hχ hs1
    · rw [localZeta_fourier_indicator_integers hψ hψ1 hχ hu hs2,
        localZeta_indicator_valBall_of_isUnramified hχ hu 0 hs1, zpow_zero, one_mul]
      ring
  · refine ⟨_, oneAddValBallIndicator_mem_schwartzBruhat (Nat.cast_nonneg _),
      localZeta_oneAddValBallIndicator_ne_zero (quasiCharConductor_pos hχ hu)
        (unitFiltrationUnits_quasiCharConductor_le_ker hχ) s, ?_⟩
    rw [localZeta_fourier_oneAddValBallIndicator hψ hψ1 hχ hu hs2,
      localLFactor_of_not_isUnramified hu,
      localLFactor_of_not_isUnramified (mt isUnramifiedChar_inv_iff.mp hu)]

theorem localZeta_functionalEquation {f : K → ℂ} (hf : f ∈ schwartzBruhat K) {s : ℂ}
    (hs1 : -quasiCharExponent χ < s.re) (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta (localFourier (selfDualMeasure ψ) ψ f) χ⁻¹ (1 - s) / localLFactor χ⁻¹ (1 - s) =
      localEpsilon χ ψ s * (localZeta f χ s / localLFactor χ s) := by
  have hs' : -quasiCharExponent χ⁻¹ < (1 - s).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hL1 := localLFactor_ne_zero hχ hs1
  have hL2 := localLFactor_ne_zero (continuous_quasiChar_inv hχ) hs'
  obtain ⟨g, hg, hZg, hkey⟩ := exists_localZeta_test hψ hψ1 hχ hs1 hs2
  have hT := localZeta_mul_localZeta_fourier_comm (selfDualMeasure ψ) hψ hψ1 hχ hf hg hs1 hs2
  have hmain : localZeta (localFourier (selfDualMeasure ψ) ψ f) χ⁻¹ (1 - s) * localLFactor χ s =
      localEpsilon χ ψ s * localZeta f χ s * localLFactor χ⁻¹ (1 - s) := by
    refine mul_left_cancel₀ hZg ?_
    linear_combination (-localLFactor χ s) * hT + localZeta f χ s * hkey
  rw [eq_comm, ← mul_div_assoc, div_eq_div_iff hL1 hL2]
  linear_combination -hmain

end FunctionalEquation

end GroundTheory.LocalField
end
end
