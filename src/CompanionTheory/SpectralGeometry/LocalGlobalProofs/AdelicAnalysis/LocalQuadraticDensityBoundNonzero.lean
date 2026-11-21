import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteFieldQuadraticFormPointCount
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import BuildAid.ForwardExisting
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroups
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsResidueEqZeroIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
import GroundTheory.GlobalFields.LocalAtPlace

section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_field_quadratic_form_point_count : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even | exact GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even | (intros; apply GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even <;> assumption)
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero

namespace GlobalTheory.CompanionTheory.SW.QuadIso

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]

def vball (x : K) (γ : ℤᵐ⁰) : Set K := {y | Valued.v (y - x) < γ}

lemma vball_eq_of_mem {x y : K} {γ : ℤᵐ⁰} (h : y ∈ vball x γ) : vball y γ = vball x γ := by
  ext z
  simp only [vball, Set.mem_setOf_eq] at h ⊢
  constructor
  · intro hz
    have : z - x = (z - y) + (y - x) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hz h
  · intro hz
    have : z - y = (z - x) + (-(y - x)) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hz (by rwa [Valuation.map_neg])

def IsRadius (K : Type) [Field K] [Valued K ℤᵐ⁰] (γ : ℤᵐ⁰) : Prop :=
  ∃ u : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v : Valuation K ℤᵐ⁰)))ˣ,
    MonoidWithZeroHom.ValueGroup₀.embedding u.1 = γ

lemma IsRadius.ne_zero {γ : ℤᵐ⁰} (h : IsRadius K γ) : γ ≠ 0 := by
  obtain ⟨u, rfl⟩ := h
  exact map_ne_zero _ |>.2 u.ne_zero

lemma isOpen_ball_of_isRadius {γ : ℤᵐ⁰} (h : IsRadius K γ) : IsOpen {y : K | Valued.v y < γ} := by
  obtain ⟨u, rfl⟩ := h
  have := Valued.isOpen_ball K u.1
  simpa only [Valuation.restrict_lt_iff_lt_embedding] using this

lemma isOpen_vball (x : K) {γ : ℤᵐ⁰} (h : IsRadius K γ) : IsOpen (vball x γ) :=
  (isOpen_ball_of_isRadius h).preimage (continuous_sub_right x)

lemma isTopologicalBasis_vball :
    TopologicalSpace.IsTopologicalBasis {s : Set K | ∃ (x : K) (γ : ℤᵐ⁰), s = vball x γ ∧ IsRadius K γ} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨x, γ, rfl, hγ⟩
    exact isOpen_vball x hγ
  · intro a u ha hu
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (hu.mem_nhds ha)
    have hr : IsRadius K (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) := ⟨γ, rfl⟩
    refine ⟨vball a _, ⟨a, _, rfl, hr⟩, ?_, ?_⟩
    · simpa [vball] using zero_lt_iff.2 hr.ne_zero
    · intro y hy
      apply hγ
      simpa only [vball, Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] using hy

lemma isPiSystem_vball :
    IsPiSystem {s : Set K | ∃ (x : K) (γ : ℤᵐ⁰), s = vball x γ ∧ IsRadius K γ} := by
  rintro _ ⟨x, γ, rfl, hγ⟩ _ ⟨y, δ, rfl, hδ⟩ ⟨z, hzx, hzy⟩
  rcases le_total γ δ with h | h
  · refine ⟨x, γ, ?_, hγ⟩
    rw [← vball_eq_of_mem hzx, ← vball_eq_of_mem hzy]
    refine Set.inter_eq_left.2 fun w hw => lt_of_lt_of_le hw h
  · refine ⟨y, δ, ?_, hδ⟩
    rw [← vball_eq_of_mem hzx, ← vball_eq_of_mem hzy]
    refine Set.inter_eq_right.2 fun w hw => lt_of_lt_of_le hw h

lemma le_exp_neg_one {x : ℤᵐ⁰} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

lemma quad_sub (a c t t' : K) :
    (a * t + c * t ^ 2) - (a * t' + c * t' ^ 2) = (t - t') * (a + c * (t + t')) := by ring

lemma v_lin_eq_one {a c s : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hs : Valued.v s < 1) : Valued.v (a + c * s) = 1 := by
  have : Valued.v (c * s) < Valued.v a := by
    rw [ha, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hs
  rw [Valuation.map_add_eq_of_lt_left _ this, ha]

lemma v_quad_sub {a c t t' : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (ht : Valued.v t < 1) (ht' : Valued.v t' < 1) :
    Valued.v ((a * t + c * t ^ 2) - (a * t' + c * t' ^ 2)) = Valued.v (t - t') := by
  rw [quad_sub, map_mul, v_lin_eq_one ha hc (Valuation.map_add_lt _ ht ht'), mul_one]

lemma v_quad_lt {a c t : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (ht : Valued.v t < 1) : Valued.v (a * t + c * t ^ 2) < 1 := by
  have := v_quad_sub ha hc ht (t' := 0) (by simp)
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, sub_zero] at this
  rwa [this]

lemma exists_approx {a c x : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hx : Valued.v x < 1) (n : ℕ) :
    ∃ t : K, Valued.v t < 1 ∧
      Valued.v ((a * t + c * t ^ 2) - x) ≤ WithZero.exp (-(n + 1 : ℤ)) := by
  induction n with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa using le_exp_neg_one hx
  | succ n ih =>
    obtain ⟨t, ht, he⟩ := ih
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha
      exact zero_ne_one ha
    set e := (a * t + c * t ^ 2) - x with he_def
    have hlt : Valued.v e < 1 := Valuation.map_sub_lt _ (v_quad_lt ha hc ht) hx
    have hae : Valued.v (a⁻¹ * e) = Valued.v e := by
      rw [map_mul, map_inv₀, ha]; simp
    have ht' : Valued.v (t - a⁻¹ * e) < 1 := Valuation.map_sub_lt _ ht (by rwa [hae])
    refine ⟨t - a⁻¹ * e, ht', ?_⟩
    have key : (a * (t - a⁻¹ * e) + c * (t - a⁻¹ * e) ^ 2) - x =
        -(a⁻¹ * e * c * (t + (t - a⁻¹ * e))) := by
      have h1 : a * (a⁻¹ * e) = e := by field_simp
      have h2 : x = (a * t + c * t ^ 2) - e := by rw [he_def]; ring
      rw [h2]
      linear_combination (-1 : K) * h1
    rw [key, Valuation.map_neg, map_mul, map_mul, hae]
    have hs : Valued.v (t + (t - a⁻¹ * e)) ≤ WithZero.exp (-1 : ℤ) :=
      le_exp_neg_one (Valuation.map_add_lt _ ht ht')
    calc Valued.v e * Valued.v c * Valued.v (t + (t - a⁻¹ * e))
        ≤ WithZero.exp (-(n + 1 : ℤ)) * 1 * WithZero.exp (-1 : ℤ) := by gcongr
      _ = WithZero.exp (-((n + 1 : ℕ) + 1 : ℤ)) := by
        rw [mul_one, ← WithZero.exp_add]
        congr 1

lemma exists_near {a c x : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hx : Valued.v x < 1) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    ∃ t : K, Valued.v t < 1 ∧ Valued.v ((a * t + c * t ^ 2) - x) < γ := by
  obtain ⟨t, ht, h⟩ := exists_approx ha hc hx (WithZero.log γ).natAbs.succ
  refine ⟨t, ht, lt_of_le_of_lt h ?_⟩
  conv_rhs => rw [← WithZero.exp_log hγ]
  rw [WithZero.exp_lt_exp]
  have := neg_abs_le (WithZero.log γ)
  push_cast
  omega

variable [MeasurableSpace K] [BorelSpace K]

lemma measure_ball (lam : Measure K) [lam.IsAddLeftInvariant] {a c : K}
    (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1) (x : K) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    lam ((fun t => a * t + c * t ^ 2) ⁻¹' vball x γ ∩ {s | Valued.v s < 1}) =
      lam (vball x γ ∩ {s | Valued.v s < 1}) := by
  by_cases hne : (vball x γ ∩ {s : K | Valued.v s < 1}).Nonempty
  · obtain ⟨y, hyB, hyM⟩ := hne
    rw [← vball_eq_of_mem hyB]
    rcases le_or_gt 1 γ with h1 | h1
    · have hsub : ∀ s : K, Valued.v s < 1 → s ∈ vball y γ := fun s hs =>
        lt_of_lt_of_le (Valuation.map_sub_lt _ hs hyM) h1
      congr 1
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hsub _ h.2, h.2⟩, fun h => ⟨hsub _ (v_quad_lt ha hc h.2), h.2⟩⟩
    · obtain ⟨t₀, ht₀, hnear⟩ := exists_near ha hc hyM hγ
      have hB : vball y γ = vball (a * t₀ + c * t₀ ^ 2) γ := (vball_eq_of_mem hnear).symm
      have hsubM : ∀ (z : K), Valued.v z < 1 → vball z γ ⊆ {s : K | Valued.v s < 1} := by
        intro z hz s hs
        have : s = (s - z) + z := by ring
        rw [Set.mem_setOf_eq, this]
        exact Valuation.map_add_lt _ (lt_trans hs h1) hz
      have e1 : (fun t => a * t + c * t ^ 2) ⁻¹' vball y γ ∩ {s | Valued.v s < 1} = vball t₀ γ := by
        rw [hB]
        ext t
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h, hM⟩
          simpa only [vball, Set.mem_setOf_eq, v_quad_sub ha hc hM ht₀] using h
        · intro h
          have hM := hsubM t₀ ht₀ h
          refine ⟨?_, hM⟩
          simpa only [vball, Set.mem_setOf_eq, v_quad_sub ha hc hM ht₀] using h
      have e2 : vball y γ ∩ {s | Valued.v s < 1} = vball y γ :=
        Set.inter_eq_left.2 (hsubM y hyM)
      rw [e1, e2]
      have e3 : vball t₀ γ = (fun h => (y - t₀) + h) ⁻¹' vball y γ := by
        ext h
        simp only [vball, Set.mem_preimage, Set.mem_setOf_eq]
        have : y - t₀ + h - y = h - t₀ := by ring
        rw [this]
      rw [e3, measure_preimage_add]
  · have hem : (fun t => a * t + c * t ^ 2) ⁻¹' vball x γ ∩ {s | Valued.v s < 1} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨h, hM⟩
      exact hne ⟨_, h, v_quad_lt ha hc hM⟩
    rw [hem, Set.not_nonempty_iff_eq_empty.1 hne]

theorem measure_quad [SecondCountableTopology K] [IsTopologicalRing K] (lam : Measure K) [lam.IsAddLeftInvariant]
    (hfin : lam {s | Valued.v s < 1} ≠ ⊤) {a c : K}
    (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1) {A : Set K} (hA : MeasurableSet A) :
    lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  have hMo : IsOpen {s : K | Valued.v s < 1} := isOpen_ball_of_isRadius ⟨1, by simp⟩
  have hM : MeasurableSet {s : K | Valued.v s < 1} := hMo.measurableSet
  have hf : Measurable (fun t : K => a * t + c * t ^ 2) := by
    apply Continuous.measurable
    fun_prop
  haveI : IsFiniteMeasure (lam.restrict {s | Valued.v s < 1}) :=
    ⟨by simpa using hfin.lt_top⟩
  haveI : IsFiniteMeasure ((lam.restrict {s | Valued.v s < 1}).map fun t : K => a * t + c * t ^ 2) :=
    Measure.isFiniteMeasure_map _ _
  have hmeas : (lam.restrict {s | Valued.v s < 1}).map (fun t : K => a * t + c * t ^ 2) =
      lam.restrict {s | Valued.v s < 1} := by
    refine ext_of_generate_finite _
      (BorelSpace.measurable_eq.trans isTopologicalBasis_vball.borel_eq_generateFrom)
      isPiSystem_vball ?_ ?_
    · rintro _ ⟨x, γ, rfl, hγ⟩
      have hB := (isOpen_vball x hγ).measurableSet
      rw [Measure.map_apply hf hB, Measure.restrict_apply (hf hB), Measure.restrict_apply hB]
      exact measure_ball lam ha hc x hγ.ne_zero
    · rw [Measure.map_apply hf MeasurableSet.univ]
      simp
  have key : ((lam.restrict {s | Valued.v s < 1}).map fun t : K => a * t + c * t ^ 2) A =
      lam.restrict {s | Valued.v s < 1} A := by rw [hmeas]
  rw [Measure.map_apply hf hA, Measure.restrict_apply (hf hA), Measure.restrict_apply hA] at key
  rw [← key]
  congr 1
  ext t
  simp [and_comm]

end GlobalTheory.CompanionTheory.SW.QuadIso

theorem GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ a c : Fv F v, Valued.v a = 1 → c ∈ v.adicCompletionIntegers F → ∀ A : Set (Fv F v), MeasurableSet A → lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  intro F _ _ v lam hlam _ a c ha hc A hA
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hH, h1⟩ := hlam
  haveI := hH
  obtain ⟨_, _, hsc, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := hsc
  have hfin : lam {s : Fv F v | Valued.v s < 1} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
    rw [← h1]
    refine measure_mono fun s hs => ?_
    exact (Valuation.mem_integer_iff _ _).2 (le_of_lt hs)
  exact GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad lam hfin ha hc hA
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_quadratic_substitution_invariant : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ a c : Fv F v, Valued.v a = 1 → c ∈ v.adicCompletionIntegers F → ∀ A : Set (Fv F v), MeasurableSet A → lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Vol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_integers : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

theorem isOpen_integers : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

def mulAdd (c : Fv F v) (hc : c ≠ 0) : Fv F v ≃+ Fv F v where
  toFun t := c * t
  invFun t := c⁻¹ * t
  left_inv t := by simp [hc]
  right_inv t := by simp [hc]
  map_add' := mul_add c

theorem mulAdd_continuous (c : Fv F v) (hc : c ≠ 0) : Continuous (mulAdd v c hc) :=
  continuous_const.mul continuous_id

theorem mulAdd_symm_continuous (c : Fv F v) (hc : c ≠ 0) : Continuous (mulAdd v c hc).symm :=
  continuous_const.mul continuous_id

theorem vol_lt_one (lam : Measure (Fv F v)) (h : IsStdV v lam) :
    lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have key := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v (Fv F v) lam Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm {0}
  have e1 : {x : Fv F v | ∃ y : Unit → v.adicCompletionIntegers F,
      (∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm x i = (y i : Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈
        ({0} : Set (Unit → IsLocalRing.ResidueField (v.adicCompletionIntegers F)))} =
      {t | Valued.v t < 1} := by
    ext x
    simp only [Set.mem_setOf_eq, ← GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff v x]
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨y (), h1 (), congrFun h2 ()⟩
    · rintro ⟨y, h1, h2⟩
      exact ⟨fun _ => y, fun _ => h1, funext fun _ => h2⟩
  have e2 : {x : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm x i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext x
    simp
  rw [e1, e2, GroundTheory.Global.natCard_residueField_adicCompletionIntegers v] at key
  simp only [Fintype.card_unit, pow_one, Set.ncard_singleton, Nat.cast_one, one_mul] at key
  have hO : lam.real (v.adicCompletionIntegers F : Set (Fv F v)) = 1 := by
    simp [measureReal_def, h.2]
  rw [hO] at key
  have hfin : lam {t | Valued.v t < 1} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := lam (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ?_
    · rw [h.2]; exact ENNReal.one_ne_top
    · exact measure_mono fun t (ht : Valued.v t < 1) => (le_of_lt ht : Valued.v t ≤ 1)
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  refine (ENNReal.toReal_eq_one_iff _).1 ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  exact key

theorem absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast this

theorem map_unit (lam : Measure (Fv F v)) (h : IsStdV v lam) (u : Fv F v) (hu : Valued.v u = 1) :
    lam.map (fun t => u * t) = lam := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨_, hl, hs, ht, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open (Fv F v) (Fv F v) lam lam (mulAdd v u hu0) (mulAdd_continuous v u hu0)
    (mulAdd_symm_continuous v u hu0)).2 (v.adicCompletionIntegers F : Set (Fv F v))
    (v.adicCompletionIntegers F : Set (Fv F v)) (isCompact_integers v) (isOpen_integers v)
    ⟨0, zero_mem _⟩ (fun x => ?_) rfl
  change Valued.v (u * x) ≤ 1 ↔ Valued.v x ≤ 1
  rw [map_mul, hu, one_mul]

theorem exp_neg_one_mul_lt_one_iff (a : WithZero (Multiplicative ℤ)) :
    WithZero.exp (-1 : ℤ) * a < 1 ↔ a ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← WithZero.exp_log ha, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp,
      WithZero.exp_le_exp]
    omega

theorem map_unif (lam : Measure (Fv F v)) (h : IsStdV v lam) (π : Fv F v)
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨_, hl, hs, ht, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hq0 := absNorm_ne_zero v
  have hqt : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  haveI : ((Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul lam hq0 hqt
  refine (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open (Fv F v) (Fv F v) lam ((Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam)
    (mulAdd v π hπ0) (mulAdd_continuous v π hπ0) (mulAdd_symm_continuous v π hπ0)).2
    (v.adicCompletionIntegers F : Set (Fv F v)) {t | Valued.v t < 1} (isCompact_integers v)
    (isOpen_integers v) ⟨0, zero_mem _⟩ (fun x => ?_) ?_
  · change Valued.v (π * x) < 1 ↔ Valued.v x ≤ 1
    rw [map_mul, hπ]
    exact exp_neg_one_mul_lt_one_iff _
  · rw [h.2, Measure.smul_apply, vol_lt_one v lam h, smul_eq_mul, ENNReal.mul_inv_cancel hq0 hqt]

theorem volumes_in_completion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ∧ (∀ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) → lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam) ∧ (∀ u : Fv F v, Valued.v u = 1 → lam.map (fun t => u * t) = lam) ∧ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal :=
  fun F _ _ v lam h => ⟨vol_lt_one v lam h, map_unif v lam h, map_unit v lam h,
    GroundTheory.Global.natCard_residueField_adicCompletionIntegers v⟩

end GlobalTheory.CompanionTheory.SW.Vol
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_local_haar_properties : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ∧ (∀ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) → lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam) ∧ (∀ u : Fv F v, Valued.v u = 1 → lam.map (fun t => u * t) = lam) ∧ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.Vol.volumes_in_completion
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Hensel

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem mem_int {x : Fv F v} : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := Iff.rfl

theorem v_le_of_close {x y : Fv F v} (hy : Valued.v y ≤ 1) (h : Valued.v (x - y) < 1) :
    Valued.v x ≤ 1 := by
  have : x = (x - y) + y := by ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans (max_le h.le hy)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mulVec_le {B : Matrix ι ι (Fv F v)} (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    {x : ι → Fv F v} (hx : ∀ i, Valued.v (x i) ≤ 1) (k : ι) : Valued.v ((B *ᵥ x) k) ≤ 1 := by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hB k j) (hx j)

theorem mulVec_lt {B : Matrix ι ι (Fv F v)} (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    {x : ι → Fv F v} (hx : ∀ i, Valued.v (x i) < 1) (k : ι) : Valued.v ((B *ᵥ x) k) < 1 := by
  refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hB k j)) (hx j)

theorem dot_close {B : Matrix ι ι (Fv F v)} (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    {x y : ι → Fv F v} (hy : ∀ i, Valued.v (y i) ≤ 1) (h : ∀ i, Valued.v (x i - y i) < 1) :
    Valued.v (x ⬝ᵥ (B *ᵥ x) - y ⬝ᵥ (B *ᵥ y)) < 1 := by
  have hx : ∀ i, Valued.v (x i) ≤ 1 := fun i => v_le_of_close (hy i) (h i)
  have e : x ⬝ᵥ (B *ᵥ x) - y ⬝ᵥ (B *ᵥ y) = (x - y) ⬝ᵥ (B *ᵥ x) + y ⬝ᵥ (B *ᵥ (x - y)) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (mulVec_le hB hx j)) (h j)
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hy j)) (mulVec_lt hB (x := x - y) h j)

theorem exists_unit_coord {B : Matrix ι ι (Fv F v)} (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    (hdet : Valued.v B.det = 1) {x : ι → Fv F v} (hx : ∀ i, Valued.v (x i) ≤ 1)
    (hp : ∃ i, Valued.v (x i) = 1) : ∃ i, Valued.v ((B *ᵥ x) i) = 1 := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i, Valued.v ((B *ᵥ x) i) < 1 := fun i =>
    lt_of_le_of_ne (mulVec_le hB hx i) (hcon i)
  obtain ⟨i, hi⟩ := hp
  let O := v.adicCompletionIntegers F
  let B' : Matrix ι ι O := fun a b => ⟨B a b, hB a b⟩
  have hmap : B = (O.subtype : O →+* Fv F v).mapMatrix B' := by
    ext a b; rfl
  have hadj : ∀ a b, Valued.v (B.adjugate a b) ≤ 1 := by
    intro a b
    rw [hmap, ← RingHom.map_adjugate]
    exact (B'.adjugate a b).2
  have h1 : (B.adjugate *ᵥ (B *ᵥ x)) i = B.det * x i := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  have h2 := mulVec_lt hadj hlt i
  rw [h1, map_mul, hdet, hi, one_mul] at h2
  exact lt_irrefl _ h2

theorem dot_add_single {B : Matrix ι ι (Fv F v)} (hs : B.IsSymm) (x : ι → Fv F v) (i : ι)
    (s : Fv F v) :
    (x + Pi.single i s) ⬝ᵥ (B *ᵥ (x + Pi.single i s)) =
      x ⬝ᵥ (B *ᵥ x) + 2 * (B *ᵥ x) i * s + B i i * s ^ 2 := by
  have hv : x ᵥ* B = B *ᵥ x := by
    conv_lhs => rw [← hs.eq]
    exact Matrix.vecMul_transpose B x
  have h1 : x ⬝ᵥ (B *ᵥ Pi.single i s) = (B *ᵥ x) i * s := by
    rw [Matrix.dotProduct_mulVec, hv, dotProduct_single]
  have h2 : (Pi.single i s : ι → Fv F v) ⬝ᵥ (B *ᵥ x) = (B *ᵥ x) i * s := by
    rw [single_dotProduct, mul_comm]
  have h3 : (Pi.single i s : ι → Fv F v) ⬝ᵥ (B *ᵥ Pi.single i s) = B i i * s ^ 2 := by
    rw [single_dotProduct]
    simp [Matrix.mulVec_single]
    ring
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h1, h2, h3]
  ring

section Meas

variable {lam : Measure (Fv F v)}

theorem isOpen_maxIdeal : IsOpen {t : Fv F v | Valued.v t < 1} := by
  simpa using Valued.isOpen_ball (Fv F v) 1

theorem measurableSet_close (b : Fv F v) : MeasurableSet {t : Fv F v | Valued.v (t - b) < 1} := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact (isOpen_maxIdeal.preimage (continuous_sub_right b)).measurableSet

theorem slice (hstd : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1) {a c : Fv F v}
    (ha : Valued.v a = 1) (hc : c ∈ v.adicCompletionIntegers F) (q b : Fv F v)
    {A : Set (Fv F v)} (hA : MeasurableSet A) :
    lam {t | Valued.v (t - b) < 1 ∧ q + a * (t - b) + c * (t - b) ^ 2 ∈ A} =
      lam (A ∩ {s | Valued.v (s - q) < 1}) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨htop, hlc, hsc, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := hstd.1
  have hA' : MeasurableSet ((fun h => q + h) ⁻¹' A) := (measurable_const_add q) hA
  have key := GlobalTheory.T.local_haar_quadratic_substitution_invariant F v lam hstd h2 a c ha hc _ hA'
  have e1 : {t | Valued.v (t - b) < 1 ∧ q + a * (t - b) + c * (t - b) ^ 2 ∈ A} =
      (fun h => -b + h) ⁻¹' {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ (fun h => q + h) ⁻¹' A} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, neg_add_eq_sub, add_assoc]
  have e2 : (fun h => q + h) ⁻¹' A ∩ {s | Valued.v s < 1} =
      (fun h => q + h) ⁻¹' (A ∩ {s | Valued.v (s - q) < 1}) := by
    ext t
    simp
  rw [e1, measure_preimage_add, key, e2, measure_preimage_add]

end Meas

section Main

variable {lam : Measure (Fv F v)}

theorem measurable_form (B : Matrix ι ι (Fv F v)) :
    Measurable fun x : ι → Fv F v => (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨htop, hlc, hsc, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have : Continuous fun x : ι → Fv F v => (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  exact this.measurable

theorem slice_form (hstd : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    {B : Matrix ι ι (Fv F v)} (hs : B.IsSymm) (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    {x₀ : ι → Fv F v} (hx₀ : ∀ i, Valued.v (x₀ i) ≤ 1) {i : ι}
    (hi : Valued.v ((B *ᵥ x₀) i) = 1) {A : Set (Fv F v)} (hA : MeasurableSet A)
    {x : ι → Fv F v} (hx : ∀ j, j ≠ i → Valued.v (x j - x₀ j) < 1) :
    lam {t | Function.update x i t ∈ {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
        (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A}} =
      lam (A ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) := by
  set x' : ι → Fv F v := Function.update x i (x₀ i) with hx'def
  have hclose : ∀ j, Valued.v (x' j - x₀ j) < 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [x']
    · simpa [x', Function.update_of_ne hj] using hx j hj
  have h2ne : (2 : Fv F v) ≠ 0 := by
    intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
  have hinv : Valued.v ((2 : Fv F v)⁻¹) = 1 := by rw [map_inv₀, h2, inv_one]
  have hupd : ∀ t, Function.update x i t = x' + Pi.single i (t - x₀ i) := by
    intro t
    ext j
    by_cases hj : j = i
    · subst hj; simp [x']
    · simp [x', Function.update_of_ne hj, Pi.single_eq_of_ne hj]
  have ha : Valued.v ((B *ᵥ x') i) = 1 := by
    have hd : Valued.v ((B *ᵥ x') i - (B *ᵥ x₀) i) < 1 := by
      have := mulVec_lt hB (x := x' - x₀) hclose i
      simpa [Matrix.mulVec_sub] using this
    have : (B *ᵥ x') i = (B *ᵥ x') i - (B *ᵥ x₀) i + (B *ᵥ x₀) i := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (by rwa [hi]), hi]
  have hc : (2 : Fv F v)⁻¹ * B i i ∈ v.adicCompletionIntegers F := by
    rw [mem_int, map_mul, hinv, one_mul]; exact hB i i
  have hq : Valued.v ((2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1 := by
    rw [← mul_sub, map_mul, hinv, one_mul]
    exact dot_close hB hx₀ hclose
  have e1 : {t | Function.update x i t ∈ {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
        (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A}} =
      {t | Valued.v (t - x₀ i) < 1 ∧ (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) +
        (B *ᵥ x') i * (t - x₀ i) + ((2 : Fv F v)⁻¹ * B i i) * (t - x₀ i) ^ 2 ∈ A} := by
    ext t
    have hform : (2 : Fv F v)⁻¹ * (Function.update x i t ⬝ᵥ (B *ᵥ Function.update x i t)) =
        (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) + (B *ᵥ x') i * (t - x₀ i) +
          ((2 : Fv F v)⁻¹ * B i i) * (t - x₀ i) ^ 2 := by
      rw [hupd t, dot_add_single hs]
      field_simp
    simp only [Set.mem_setOf_eq, hform]
    refine and_congr_left fun _ => ⟨fun h => by simpa using h i, fun h j => ?_⟩
    by_cases hj : j = i
    · subst hj; simpa using h
    · simpa [Function.update_of_ne hj] using hx j hj
  have e2 : {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x'))) < 1} =
      {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1} := by
    ext s
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have : s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀)) =
          (s - (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x'))) +
            ((2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) := by ring
      rw [this]
      exact Valuation.map_add_lt _ h hq
    · intro h
      have : s - (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) =
          (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) -
            ((2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) := by ring
      rw [this]
      exact Valuation.map_sub_lt _ h hq
  rw [e1, slice hstd h2 ha hc _ _ hA, e2]

theorem pi_eq_mul [SigmaFinite lam] (i : ι) {S E : Set (ι → Fv F v)} (hS : MeasurableSet S)
    (hE : MeasurableSet E) (C : ℝ≥0∞) (hC : C ≠ ⊤) (x₀ : ι → Fv F v)
    (h1 : ∀ x, x ∈ E → lam {t | Function.update x i t ∈ S} = C)
    (h0 : ∀ x, x ∉ E → lam {t | Function.update x i t ∈ S} = 0) :
    (Measure.pi fun _ : ι => lam) S =
      C * (∫⋯∫⁻_(Finset.univ.erase i), E.indicator 1 ∂(fun _ : ι => lam)) x₀ := by
  have hf : Measurable (S.indicator (1 : (ι → Fv F v) → ℝ≥0∞)) := measurable_one.indicator hS
  have hg : Measurable (E.indicator (1 : (ι → Fv F v) → ℝ≥0∞)) := measurable_one.indicator hE
  have hU : (Finset.univ : Finset ι) = Finset.univ.erase i ∪ {i} := by
    ext j; by_cases hj : j = i <;> simp [hj]
  have hdis : Disjoint (Finset.univ.erase i) ({i} : Finset ι) := by simp
  have hin : (∫⋯∫⁻_{i}, S.indicator 1 ∂(fun _ : ι => lam)) =
      fun x => C * E.indicator (1 : (ι → Fv F v) → ℝ≥0∞) x := by
    rw [lmarginal_singleton]
    ext x
    have hsl : ∫⁻ t, S.indicator (1 : (ι → Fv F v) → ℝ≥0∞) (Function.update x i t) ∂lam =
        lam {t | Function.update x i t ∈ S} := by
      have hm : MeasurableSet {t | Function.update x i t ∈ S} := measurable_update x hS
      rw [← lintegral_indicator_one hm]
      refine lintegral_congr fun t => ?_
      by_cases ht : Function.update x i t ∈ S
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ {t | Function.update x i t ∈ S} from ht)]
        rfl
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ {t | Function.update x i t ∈ S} from ht)]
    rw [hsl]
    by_cases hx : x ∈ E
    · simp [h1 x hx, hx]
    · simp [h0 x hx, hx]
  calc (Measure.pi fun _ : ι => lam) S
      = ∫⁻ x, S.indicator 1 x ∂(Measure.pi fun _ : ι => lam) := (lintegral_indicator_one hS).symm
    _ = (∫⋯∫⁻_Finset.univ, S.indicator 1 ∂(fun _ : ι => lam)) x₀ := lintegral_eq_lmarginal_univ x₀
    _ = (∫⋯∫⁻_(Finset.univ.erase i), (∫⋯∫⁻_{i}, S.indicator 1 ∂(fun _ : ι => lam))
          ∂(fun _ : ι => lam)) x₀ := by
        rw [← lmarginal_union _ _ hf hdis, ← hU]
    _ = C * (∫⋯∫⁻_(Finset.univ.erase i), E.indicator 1 ∂(fun _ : ι => lam)) x₀ := by
        rw [hin]
        exact lintegral_const_mul C (hg.comp measurable_updateFinset)

end Main

end SlopeTestRemainingChoices

theorem measure_residue_class : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ x₀ : ι → Fv F v, (∀ i, x₀ i ∈ v.adicCompletionIntegers F) → (∃ i, Valued.v (x₀ i) = 1) → ∀ A : Set (Fv F v), MeasurableSet A → (Measure.pi fun _ : ι => lam) {x | (∀ i, Valued.v (x i - x₀ i) < 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1) * lam (A ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) := by
  intro F _ _ v lam hstd h2 ι _ _ B hs hB hdet x₀ hx₀ hp A hA
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨htop, hlc, hsc, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := hstd.1
  have hB' : ∀ i j, Valued.v (B i j) ≤ 1 := hB
  have hx₀' : ∀ i, Valued.v (x₀ i) ≤ 1 := hx₀
  obtain ⟨i, hi⟩ := exists_unit_coord hB' hdet hx₀' hp
  set Nn : ℝ≥0∞ := (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ with hNn
  have hvol : lam {t | Valued.v t < 1} = Nn := (GlobalTheory.T.standard_local_haar_properties F v lam hstd).1
  have hball : ∀ b : Fv F v, lam {s | Valued.v (s - b) < 1} = Nn := by
    intro b
    have : {s | Valued.v (s - b) < 1} = (fun h => -b + h) ⁻¹' {t | Valued.v t < 1} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_preimage, neg_add_eq_sub]
    rw [this, measure_preimage_add, hvol]
  have hN0 : Nn ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hNt : Nn ≠ ⊤ := by
    rw [← hvol]
    refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
    rw [← hstd.2]
    exact measure_mono fun t ht => show t ∈ v.adicCompletionIntegers F from mem_int.2 (le_of_lt ht)
  set E : Set (ι → Fv F v) := {x | ∀ j, j ≠ i → Valued.v (x j - x₀ j) < 1} with hEdef
  have hsec : ∀ j, MeasurableSet {y : ι → Fv F v | Valued.v (y j - x₀ j) < 1} := fun j =>
    (measurable_pi_apply (X := fun _ : ι => Fv F v) j) (measurableSet_close (x₀ j))
  have hE : MeasurableSet E := by
    simp only [hEdef, Set.setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hsec j
  have hD : MeasurableSet {y : ι → Fv F v | ∀ j, Valued.v (y j - x₀ j) < 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter hsec
  have hform : ∀ A' : Set (Fv F v), MeasurableSet A' →
      (Measure.pi fun _ : ι => lam) {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
          (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A'} =
        lam (A' ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) *
          (∫⋯∫⁻_(Finset.univ.erase i), E.indicator 1 ∂(fun _ : ι => lam)) x₀ := by
    intro A' hA'
    have hS : MeasurableSet {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
        (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A'} :=
      hD.inter ((measurable_form B) hA')
    refine pi_eq_mul i hS hE _ ?_ x₀ ?_ ?_
    · refine ne_top_of_le_ne_top hNt ?_
      rw [← hball ((2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀)))]
      exact measure_mono Set.inter_subset_right
    · intro x hx
      exact slice_form hstd h2 hs hB' hx₀' hi hA' hx
    · intro x hx
      simp only [hEdef, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨j, hj, hjx⟩ := hx
      have : {t | Function.update x i t ∈ {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
          (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A'}} = ∅ := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd (by simpa [Function.update_of_ne hj] using h j) hjx
      rw [this, measure_empty]
  have hpi : (Measure.pi fun _ : ι => lam) {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
      (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ Set.univ} = Nn ^ Fintype.card ι := by
    have : {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
        (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ Set.univ} =
        Set.univ.pi fun j => {t | Valued.v (t - x₀ j) < 1} := by
      ext y
      simp
    rw [this, Measure.pi_pi]
    simp [hball]
  have hW : (∫⋯∫⁻_(Finset.univ.erase i), E.indicator 1 ∂(fun _ : ι => lam)) x₀ =
      Nn ^ (Fintype.card ι - 1) := by
    have h := hform Set.univ MeasurableSet.univ
    rw [hpi, Set.univ_inter, hball] at h
    have hcard : Fintype.card ι = (Fintype.card ι - 1) + 1 :=
      (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨i⟩)).symm
    rw [hcard, pow_succ'] at h
    exact ((ENNReal.mul_right_inj hN0 hNt).mp h).symm
  rw [hform A hA, hW, mul_comm]

end GlobalTheory.CompanionTheory.SW.Hensel
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_vector_quadratic_level_measure : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ x₀ : ι → Fv F v, (∀ i, x₀ i ∈ v.adicCompletionIntegers F) → (∃ i, Valued.v (x₀ i) = 1) → ∀ A : Set (Fv F v), MeasurableSet A → (Measure.pi fun _ : ι => lam) {x | (∀ i, Valued.v (x i - x₀ i) < 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1) * lam (A ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.Hensel.measure_residue_class
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.LGPrim

theorem real_bound (q N Nf : ℝ) (hq : 0 < q) (M : ℕ) (hM : 1 ≤ M)
    (h : |Nf - q ^ (2 * M - 1)| ≤ q ^ M) (h1 : N ≤ Nf) (h2 : Nf ≤ N + 1) :
    |N * (q⁻¹) ^ (2 * M - 1) - 1| ≤ 1 / q ^ (M - 1) + 1 / q ^ (2 * M - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1] at h ⊢
  rw [e2]
  have hQ : q ^ (2 * m + 1) = q ^ (m + 1) * q ^ m := by rw [← pow_add]; congr 1; omega
  have hQpos : 0 < q ^ (2 * m + 1) := by positivity
  have habs : |N - q ^ (2 * m + 1)| ≤ q ^ (m + 1) + 1 := by
    obtain ⟨h3, h4⟩ := abs_le.1 h
    have hp : 0 ≤ q ^ (m + 1) := by positivity
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have e3 : N * (q⁻¹) ^ (2 * m + 1) - 1 = (N - q ^ (2 * m + 1)) / q ^ (2 * m + 1) := by
    rw [inv_pow]; field_simp
  rw [e3, abs_div, abs_of_pos hQpos, div_le_iff₀ hQpos]
  have e4 : (1 / q ^ m + 1 / q ^ (2 * m + 1)) * q ^ (2 * m + 1) = q ^ (m + 1) + 1 := by
    rw [add_mul, one_div, one_div, inv_mul_cancel₀ hQpos.ne', hQ]
    have : q ^ m ≠ 0 := by positivity
    field_simp
  rw [e4]
  exact habs

theorem map_quad {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S)
    (B : Matrix ι ι R) (x : ι → R) :
    f (x ⬝ᵥ (B *ᵥ x)) = (f ∘ x) ⬝ᵥ ((B.map f) *ᵥ (f ∘ x)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact RingHom.map_mulVec f B x i

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "𝓴" => IsLocalRing.ResidueField (HeightOneSpectrum.adicCompletionIntegers F v)
local notation "res" => IsLocalRing.residue (HeightOneSpectrum.adicCompletionIntegers F v)

theorem res_eq_zero_iff (a : 𝒪) : res a = 0 ↔ Valued.v (a : Fv F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h
    have h1 : Valued.v (a : Fv F v) ≤ 1 := a.2
    refine lt_of_le_of_ne h1 fun h2 => h ?_
    have ha0 : (a : Fv F v) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h2
      exact zero_ne_one h2
    have hinv : (a : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
      show Valued.v ((a : Fv F v)⁻¹) ≤ 1
      rw [map_inv₀, h2, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(a : Fv F v)⁻¹, hinv⟩ : v.adicCompletionIntegers F) ?_
    apply Subtype.ext
    show (a : Fv F v) * (a : Fv F v)⁻¹ = 1
    exact mul_inv_cancel₀ ha0
  · intro h hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have h3 : Valued.v ((a : Fv F v) * (b : Fv F v)) = 1 := by
      have : (a : Fv F v) * (b : Fv F v) = 1 := congrArg Subtype.val hb
      rw [this, map_one]
    rw [map_mul] at h3
    have hb1 : Valued.v (b : Fv F v) ≤ 1 := b.2
    have h4 : Valued.v (a : Fv F v) * Valued.v (b : Fv F v) < 1 := by
      calc _ ≤ Valued.v (a : Fv F v) * 1 := by gcongr
        _ < 1 := by simpa using h
    exact absurd h3 (ne_of_lt h4)

theorem res_eq_iff (a b : 𝒪) : res a = res b ↔ Valued.v ((a : Fv F v) - b) < 1 := by
  rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
  rfl

def lift (y : 𝓴) : 𝒪 := Function.surjInv IsLocalRing.residue_surjective y

theorem res_lift (y : 𝓴) : res (lift y) = y := Function.surjInv_eq _ y

def lf {ι : Type} (y : ι → 𝓴) : ι → Fv F v := fun i => (lift (y i) : 𝒪)

theorem cover {ι : Type} (x : ι → Fv F v) :
    ((∀ i, x i ∈ 𝒪) ∧ ∃ i, Valued.v (x i) = 1) ↔
      ∃ y : ι → 𝓴, y ≠ 0 ∧ ∀ i, Valued.v (x i - lf y i) < 1 := by
  constructor
  · rintro ⟨hx, i₀, hi₀⟩
    refine ⟨fun i => res ⟨x i, hx i⟩, ?_, fun i => ?_⟩
    · intro h0
      have h1 := (res_eq_zero_iff (⟨x i₀, hx i₀⟩ : 𝒪)).1 (congrFun h0 i₀)
      exact absurd hi₀ (ne_of_lt h1)
    · exact (res_eq_iff (⟨x i, hx i⟩ : 𝒪) (lift _)).1 (res_lift _).symm
  · rintro ⟨y, hy, h⟩
    have hx : ∀ i, x i ∈ 𝒪 := by
      intro i
      have e : x i = (x i - lf y i) + lf y i := by ring
      show Valued.v (x i) ≤ 1
      rw [e]
      exact Valuation.map_add_le _ (h i).le (lift (y i)).2
    refine ⟨hx, ?_⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    refine ⟨i, le_antisymm (hx i) (not_lt.1 fun hlt => hi ?_)⟩
    have e : res (⟨x i, hx i⟩ : 𝒪) = y i := by
      rw [(res_eq_iff (⟨x i, hx i⟩ : 𝒪) (lift (y i))).2 (h i), res_lift]
    rw [← e]
    exact (res_eq_zero_iff _).2 hlt

theorem eq_of_close {ι : Type} (x : ι → Fv F v) (y y' : ι → 𝓴)
    (h : ∀ i, Valued.v (x i - lf y i) < 1) (h' : ∀ i, Valued.v (x i - lf y' i) < 1) : y = y' := by
  funext i
  have h1 := Valuation.map_sub_lt _ (h' i) (h i)
  have e : (x i - lf y' i) - (x i - lf y i) = lf y i - lf y' i := by ring
  rw [e] at h1
  have h2 := (res_eq_iff (lift (y i)) (lift (y' i))).2 h1
  rwa [res_lift, res_lift] at h2

abbrev phi : 𝒪 →+* Fv F v := ValuationSubring.subtype _

theorem res_Q {ι : Type} [Fintype ι] (c : 𝒪) (hc : (c : Fv F v) = 2⁻¹) (hr : res c = 2⁻¹)
    (BO : Matrix ι ι 𝒪) (y : ι → 𝓴) :
    ∃ a : 𝒪, (a : Fv F v) = (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y)) ∧
      res a = (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y)) := by
  refine ⟨c * ((lift ∘ y) ⬝ᵥ (BO *ᵥ (lift ∘ y))), ?_, ?_⟩
  · have h1 := map_quad phi BO (lift ∘ y)
    have h2 : (phi : 𝒪 →+* Fv F v) (c * ((lift ∘ y) ⬝ᵥ (BO *ᵥ (lift ∘ y)))) = phi c * phi ((lift ∘ y) ⬝ᵥ (BO *ᵥ (lift ∘ y))) := map_mul _ _ _
    rw [h1] at h2
    have h3 : phi c = (2 : Fv F v)⁻¹ := hc
    rw [h3] at h2
    exact h2
  · rw [map_mul, hr, map_quad]
    have : (⇑res ∘ lift ∘ y) = y := by
      funext i
      exact res_lift _
    rw [this]

theorem core (lam : Measure (Fv F v)) (hlam : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)) (hBs : B.IsSymm)
    (hBint : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hBdet : Valued.v B.det = 1)
    (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M) (s : Fv F v)
    (hs : s ∈ v.adicCompletionIntegers F) :
    ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) +
        1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ∧
      ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} →
        (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  classical
  have hLoc := GlobalTheory.T.completion_is_local_ring F v
  haveI : SecondCountableTopology (Fv F v) := hLoc.2.2.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, hcard⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hlam
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  haveI : Finite 𝓴 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq0)
  letI : Fintype 𝓴 := Fintype.ofFinite _
  have hcardk : Fintype.card 𝓴 = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨BO, rfl⟩ : ∃ BO : Matrix ι ι 𝒪, BO.map phi = B :=
    ⟨Matrix.of fun i j => ⟨B i j, hBint i j⟩, by ext i j; rfl⟩
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  let c : 𝒪 := ⟨2⁻¹, by show Valued.v ((2 : Fv F v)⁻¹) ≤ 1; rw [map_inv₀, h2, inv_one]⟩
  have hc : (c : Fv F v) = 2⁻¹ := rfl
  have hc2 : c * 2 = 1 := by
    apply Subtype.ext
    have e : (phi : 𝒪 →+* Fv F v) (c * 2) = phi c * phi 2 := map_mul _ _ _
    have e2 : (phi : 𝒪 →+* Fv F v) 2 = 2 := map_ofNat _ 2
    have e3 : phi c = (2 : Fv F v)⁻¹ := hc
    rw [e2, e3, inv_mul_cancel₀ h20] at e
    exact e
  have hr1 : res c * 2 = 1 := by
    have := congrArg res hc2
    rwa [map_mul, map_one, map_ofNat] at this
  have hr : res c = 2⁻¹ := eq_inv_of_mul_eq_one_left hr1
  have hchar : ringChar 𝓴 ≠ 2 := by
    intro h
    have h0 : (2 : 𝓴) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := 𝓴)
      rw [h] at this
      exact_mod_cast this
    rw [h0, mul_zero] at hr1
    exact zero_ne_one hr1
  have hBO : BO.IsSymm := by
    exact Matrix.IsSymm.ext fun i j => Subtype.ext (congrFun (congrFun hBs i) j)
  have hBks : (BO.map res).IsSymm := hBO.map _
  have hBkdet : (BO.map res).det ≠ 0 := by
    intro h0
    have e : res BO.det = (BO.map res).det := RingHom.map_det res BO
    rw [← e] at h0
    have h3 := (res_eq_zero_iff _).1 h0
    have e2 : ((BO.det : 𝒪) : Fv F v) = (BO.map phi).det := RingHom.map_det phi BO
    rw [e2, hBdet] at h3
    exact lt_irrefl _ h3
  set sb : 𝓴 := res (⟨s, hs⟩ : 𝒪) with hsb
  have hcount := GlobalTheory.T.finite_field_quadratic_form_point_count 𝓴 hchar ι M hM hM1 (BO.map res) hBks hBkdet sb
  let qk : (ι → 𝓴) → 𝓴 := fun y => (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y))
  let Fl : Finset (ι → 𝓴) := Finset.univ.filter fun y => qk y = sb
  let T : Finset (ι → 𝓴) := Fl.filter fun y => y ≠ 0
  have hN : Nat.card {x : ι → 𝓴 // (2 : 𝓴)⁻¹ * (x ⬝ᵥ ((BO.map res) *ᵥ x)) = sb} = Fl.card :=
    Nat.subtype_card Fl (fun x => by simp [Fl, qk])
  rw [hN, hcardk] at hcount
  have hle1 : T.card ≤ Fl.card := Finset.card_filter_le _ _
  have hle2 : Fl.card ≤ T.card + 1 := by
    have hsub : Fl ⊆ insert 0 T := by
      intro y hy
      by_cases h0 : y = 0
      · simp [h0]
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy, h0⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hqpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  refine ⟨(T.card : ℝ≥0) * ((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ (2 * M - 1), ?_, fun A hA hAs => ?_⟩
  · push_cast
    exact real_bound _ _ (Fl.card : ℝ) hqpos M hM1 hcount (by exact_mod_cast hle1)
      (by exact_mod_cast hle2)
  · set Qf : (ι → Fv F v) → Fv F v := fun x => (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) with hQf
    have hQc : Continuous Qf := by
      refine continuous_const.mul ?_
      exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    let P : (ι → 𝓴) → Set (ι → Fv F v) := fun y =>
      {x | (∀ i, Valued.v (x i - lf y i) < 1) ∧ Qf x ∈ A}
    let T0 : Finset (ι → 𝓴) := Finset.univ.filter fun y => y ≠ 0
    have hS : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
        (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
        ⋃ y ∈ T0, P y := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨h1, h3, h4⟩
        obtain ⟨y, hy, h⟩ := (cover x).1 ⟨h1, h3⟩
        exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, h, h4⟩
      · rintro ⟨y, hy, h, h4⟩
        obtain ⟨h1, h3⟩ := (cover x).2 ⟨y, (Finset.mem_filter.1 hy).2, h⟩
        exact ⟨h1, h3, h4⟩
    have hball : MeasurableSet {a : Fv F v | Valued.v a < 1} :=
      by
      have h := (Valued.isOpen_ball (Fv F v) 1).measurableSet
      simpa [Valuation.restrict_lt_iff_lt_embedding] using h
    have hmeas : ∀ y ∈ T0, MeasurableSet (P y) := by
      intro y _
      have e : P y = (⋂ i, (fun x : ι → Fv F v => x i - lf y i) ⁻¹' {a | Valued.v a < 1}) ∩ Qf ⁻¹' A := by
        ext x
        simp [P]
      rw [e]
      refine (MeasurableSet.iInter fun i => ?_).inter (hQc.measurable hA)
      exact ((continuous_apply i).sub continuous_const).measurable hball
    have hdisj : Set.PairwiseDisjoint (↑T0) P := by
      intro y _ y' _ hne
      exact Set.disjoint_left.2 fun x hx hx' => hne (eq_of_close x y y' hx.1 hx'.1)
    have hclass : ∀ y ∈ T0, (Measure.pi fun _ : ι => lam) (P y) =
        if qk y = sb then ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (2 * M - 1)) * lam A else 0 := by
      intro y hy
      have hy0 : y ≠ 0 := (Finset.mem_filter.1 hy).2
      obtain ⟨hint, hprim⟩ := (cover (lf y)).2 ⟨y, hy0, fun i => by simp⟩
      obtain ⟨a, haQ, har⟩ := res_Q c hc hr BO y
      have key := GlobalTheory.T.primitive_vector_quadratic_level_measure F v lam hlam h2 ι (BO.map phi) hBs hBint hBdet (lf y) hint hprim A hA
      have hkey : (Measure.pi fun _ : ι => lam) (P y) = _ := key
      rw [hkey, hM]
      have hcl : Valued.v (s - Qf (lf y)) < 1 ↔ qk y = sb := by
        have := res_eq_iff (⟨s, hs⟩ : 𝒪) a
        rw [har] at this
        rw [show Qf (lf y) = (a : Fv F v) from haQ.symm]
        exact ⟨fun h => (this.2 h).symm, fun h => this.1 h.symm⟩
      split_ifs with he
      · have hlt := hcl.2 he
        have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = A := by
          refine Set.inter_eq_left.2 fun z hz => ?_
          have h5 : Valued.v (z - s) < 1 := hAs hz
          have h6 := Valuation.map_add_lt _ h5 hlt
          have e : z - s + (s - Qf (lf y)) = z - Qf (lf y) := by ring
          rw [e] at h6
          exact h6
        rw [this]
      · have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun z hz => he (hcl.1 ?_)
          have h5 : Valued.v (z - s) < 1 := hAs hz.1
          have h6 : Valued.v (z - Qf (lf y)) < 1 := hz.2
          have h7 := Valuation.map_sub_lt _ h6 h5
          have e : z - Qf (lf y) - (z - s) = s - Qf (lf y) := by ring
          rw [e] at h7
          exact h7
        rw [this, measure_empty, mul_zero]
    rw [hS, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hclass, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    have hT : T0.filter (fun y => qk y = sb) = T := by
      ext y
      simp [T0, T, Fl, and_comm]
    rw [hT]
    have hq0' : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by exact_mod_cast hq0
    push_cast [ENNReal.coe_inv hq0']
    rw [mul_assoc]

theorem density_primitive : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ M : ℕ, Fintype.card ι = 2 * M → 1 ≤ M → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ∧ ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} → (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  intro F _ _ v lam hlam h2 ι _ _ B hBs hBint hBdet M hM hM1 s hs
  exact core lam hlam h2 ι B hBs hBint hBdet M hM hM1 s hs

end GlobalTheory.CompanionTheory.SW.LGPrim
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_quadratic_density_near_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ M : ℕ, Fintype.card ι = 2 * M → 1 ≤ M → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ∧ ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} → (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  first | exact @GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive | exact GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive | (intros; apply GlobalTheory.CompanionTheory.SW.LGPrim.density_primitive <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GBall

variable {F : Type} [Field F] [NumberField F]

theorem exists_unif (v : HeightOneSpectrum (𝓞 F)) : ∃ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  exact ⟨((π : v.adicCompletion F) : Fv F v), by rw [v.valuedAdicCompletion_eq_valuation', hπ]⟩

theorem le_exp_of_lt_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  · rw [← WithZero.exp_log ha] at h ⊢
    have h' : WithZero.log a < 0 := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_zero]; exact h
    rw [WithZero.exp_le_exp]
    omega

variable {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι]

theorem mem_int {x : Fv F v} : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := by
  exact Iff.rfl

theorem q_int (h2 : Valued.v (2 : Fv F v) = 1) {B : Matrix ι ι (Fv F v)}
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) {y : ι → Fv F v}
    (hy : ∀ i, y i ∈ v.adicCompletionIntegers F) :
    Valued.v ((2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y))) ≤ 1 := by
  have hmem : y ⬝ᵥ (B *ᵥ y) ∈ v.adicCompletionIntegers F := by
    simp only [dotProduct, Matrix.mulVec]
    exact sum_mem fun i _ => mul_mem (hy i) (sum_mem fun j _ => mul_mem (hB i j) (hy j))
  rw [map_mul, map_inv₀, h2, inv_one, one_mul]
  exact hmem

theorem q_smul (B : Matrix ι ι (Fv F v)) (π : Fv F v) (y : ι → Fv F v) :
    (2 : Fv F v)⁻¹ * ((fun i => π * y i) ⬝ᵥ (B *ᵥ fun i => π * y i)) =
      π * (π * ((2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)))) := by
  have hf : (fun i => π * y i) = π • y := rfl
  rw [hf, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

theorem borel_Fv : BorelSpace (Fv F v) := by
  exact ⟨rfl⟩

private theorem sigmaFinite_nnreal_smul {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    (c : ℝ≥0) : SigmaFinite ((c : ℝ≥0∞) • ν) := by
  refine ⟨⟨⟨spanningSets ν, fun _ => trivial, fun i => ?_, iUnion_spanningSets ν⟩⟩⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_spanningSets_lt_top ν i)

theorem pi_const_smul (ι : Type) [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    (c : ℝ≥0) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => ν) := by
  haveI := sigmaFinite_nnreal_smul ν c
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

private theorem sigmaFinite_of_isStdV {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    SigmaFinite lam := by
  haveI := borel_Fv (F := F) (v := v)
  obtain ⟨π, hπ⟩ := exists_unif v
  obtain ⟨-, hmap, -, -⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hstd
  have hm := hmap π hπ
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (Fv F v)) :=
    (Valued.isOpen_valuationSubring (Fv F v)).measurableSet
  have hpk : ∀ k : ℕ, Valued.v (π ^ k) = WithZero.exp (-(k : ℤ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [pow_succ, map_mul, ihk, hπ, ← WithZero.exp_add]
      congr 1
      push_cast
      ring
  let S : ℕ → Set (Fv F v) := fun n => (fun x => π ^ n * x) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => (measurable_const_mul _) hO
  have hSfin : ∀ n, lam (S n) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ n := by
    intro n
    induction n with
    | zero =>
      show lam ((fun x => π ^ 0 * x) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) = _
      simp only [pow_zero, one_mul, Set.preimage_id', hstd.2]
    | succ n ihn =>
      have hS : S (n + 1) = (fun t => π * t) ⁻¹' S n := by
        ext x
        simp only [S, Set.mem_preimage, pow_succ, mul_assoc]
      rw [hS, ← Measure.map_apply (measurable_const_mul π) (hSmeas n), hm, Measure.smul_apply, ihn,
        smul_eq_mul, pow_succ, mul_comm]
  refine ⟨⟨⟨S, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [hSfin]
    exact ENNReal.pow_lt_top (ENNReal.natCast_lt_top _)
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    rcases eq_or_ne x 0 with rfl | hx
    · refine ⟨0, ?_⟩
      show Valued.v (π ^ 0 * 0) ≤ 1
      rw [mul_zero, map_zero]
      exact zero_le
    · have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      show Valued.v (π ^ (WithZero.log (Valued.v x)).toNat * x) ≤ 1
      rw [map_mul, hpk, ← WithZero.exp_log hvx, ← WithZero.exp_add]
      refine (WithZero.exp_le_exp.mpr ?_).trans_eq WithZero.exp_zero
      rw [WithZero.log_exp]
      omega

theorem pi_scale {lam : Measure (Fv F v)} (hstd : IsStdV v lam) {π : Fv F v}
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) (T : Set (ι → Fv F v)) :
    (Measure.pi fun _ : ι => lam) {y | (fun i => π * y i) ∈ T} =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ Fintype.card ι * (Measure.pi fun _ : ι => lam) T := by
  haveI := borel_Fv (F := F) (v := v)
  haveI := sigmaFinite_of_isStdV hstd
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨-, hmap, -, -⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hstd
  have hm := hmap π hπ
  have hN : (Ideal.absNorm v.asIdeal : ℝ≥0∞) = ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.coe_natCast _).symm
  let e : (ι → Fv F v) ≃ᵐ (ι → Fv F v) :=
    MeasurableEquiv.piCongrRight (fun _ : ι => MeasurableEquiv.mulLeft₀ π hπ0)
  have hpre : {y : ι → Fv F v | (fun i => π * y i) ∈ T} = e ⁻¹' T := rfl
  haveI hsf : SigmaFinite (lam.map (fun t => π * t)) := by
    rw [hm, hN]; exact sigmaFinite_nnreal_smul lam _
  have hmapPi : (Measure.pi fun _ : ι => lam).map (fun x i => π * x i) =
      Measure.pi (fun _ : ι => lam.map (fun t => π * t)) :=
    Measure.pi_map_pi (fun _ => (measurable_const_mul π).aemeasurable)
  rw [hpre, ← MeasurableEquiv.map_apply]
  have he : (⇑e : (ι → Fv F v) → ι → Fv F v) = fun x i => π * x i := rfl
  rw [he, hmapPi, hm, hN, pi_const_smul ι lam, Measure.smul_apply, smul_eq_mul]

theorem lam_scale {lam : Measure (Fv F v)} (hstd : IsStdV v lam) {π : Fv F v}
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) {A : Set (Fv F v)} (hA : MeasurableSet A) :
    MeasurableSet {z | π * (π * z) ∈ A} ∧
    lam {z | π * (π * z) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ 2 * lam A := by
  haveI := borel_Fv (F := F) (v := v)
  have hmeas : Measurable (fun z : Fv F v => π * (π * z)) :=
    (measurable_const_mul π).comp (measurable_const_mul π)
  refine ⟨hmeas hA, ?_⟩
  obtain ⟨-, hmap, -, -⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hstd
  have hm := hmap π hπ
  have h1 : (lam.map (fun t => π * t)).map (fun t => π * t) A = lam {z | π * (π * z) ∈ A} := by
    rw [Measure.map_map (measurable_const_mul π) (measurable_const_mul π), Measure.map_apply ((measurable_const_mul π).comp (measurable_const_mul π)) hA]
    rfl
  rw [← h1, hm, Measure.map_smul, hm, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, sq]

theorem isOpen_unit_sphere : IsOpen {x : Fv F v | Valued.v x = 1} := by
  obtain ⟨π, hπ⟩ := exists_unif v
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hO : IsOpen {x : Fv F v | Valued.v x ≤ 1} := Valued.isOpen_valuationSubring (Fv F v)
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y => π⁻¹ * (y - x)) ⁻¹' {x : Fv F v | Valued.v x ≤ 1}, ?_, ?_, ?_⟩
  · intro y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy hx ⊢
    have h1 : Valued.v (y - x) < Valued.v x := by
      have he : y - x = π * (π⁻¹ * (y - x)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]
      rw [he, map_mul, hπ, hx]
      calc WithZero.exp (-1 : ℤ) * Valued.v (π⁻¹ * (y - x)) ≤ WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul_of_nonneg_left hy zero_le
        _ < 1 := by
          rw [mul_one]
          exact (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)).trans_eq WithZero.exp_zero
    rw [← hx]
    exact Valuation.map_eq_of_sub_lt _ h1
  · exact hO.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  · simp only [Set.mem_preimage, Set.mem_setOf_eq, sub_self, mul_zero, map_zero]
    exact zero_le

theorem meas_prim : MeasurableSet {x : ι → Fv F v | ∃ i, Valued.v (x i) = 1} := by
  haveI := borel_Fv (F := F) (v := v)
  have he : {x : ι → Fv F v | ∃ i, Valued.v (x i) = 1} =
      ⋃ i, (fun x : ι → Fv F v => x i) ⁻¹' {z | Valued.v z = 1} := by
    ext x; simp
  rw [he]
  exact MeasurableSet.iUnion fun i => isOpen_unit_sphere.measurableSet.preimage (measurable_pi_apply i)

theorem val_inv {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    Valued.v π⁻¹ = WithZero.exp (1 : ℤ) := by
  rw [map_inv₀, hπ, ← WithZero.exp_neg, neg_neg]

theorem pi_ne_zero {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) : π ≠ 0 := by
  intro h0
  rw [h0, map_zero] at hπ
  exact WithZero.exp_ne_zero hπ.symm

theorem div_int {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) {a : Fv F v}
    (h1 : Valued.v a ≤ 1) (h2 : Valued.v a ≠ 1) : Valued.v (π⁻¹ * a) ≤ 1 := by
  have hlt : Valued.v a < 1 := lt_of_le_of_ne h1 h2
  have hle := le_exp_of_lt_one hlt
  rw [map_mul, val_inv hπ]
  calc WithZero.exp (1 : ℤ) * Valued.v a ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) :=
        mul_le_mul_of_nonneg_left hle zero_le
    _ = 1 := by rw [← WithZero.exp_add]; simp

theorem pi_mul_lt {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) {a : Fv F v}
    (h1 : Valued.v a ≤ 1) : Valued.v (π * a) < 1 := by
  rw [map_mul, hπ]
  calc WithZero.exp (-1 : ℤ) * Valued.v a ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul_of_nonneg_left h1 zero_le
    _ < 1 := by
      rw [mul_one]
      exact (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)).trans_eq WithZero.exp_zero

theorem val_pp {π : Fv F v} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) (a : Fv F v) :
    Valued.v (π * (π * a)) = WithZero.exp (-2 : ℤ) * Valued.v a := by
  rw [map_mul, map_mul, hπ, ← mul_assoc, ← WithZero.exp_add]
  norm_num

theorem q_nonprim (h2 : Valued.v (2 : Fv F v) = 1) {B : Matrix ι ι (Fv F v)}
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) {π : Fv F v}
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) {x : ι → Fv F v}
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) (hnp : ¬ ∃ i, Valued.v (x i) = 1) :
    Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x))) ≤ WithZero.exp (-2 : ℤ) := by
  have hlt : ∀ i, Valued.v (x i) ≠ 1 := fun i h => hnp ⟨i, h⟩
  obtain ⟨y, hy, rfl⟩ : ∃ y : ι → Fv F v, (∀ i, y i ∈ v.adicCompletionIntegers F) ∧
      x = fun i => π * y i :=
    ⟨fun i => π⁻¹ * x i, fun i => div_int hπ (hx i) (hlt i), by
      funext i; rw [← mul_assoc, mul_inv_cancel₀ (pi_ne_zero hπ), one_mul]⟩
  rw [q_smul, val_pp hπ]
  calc WithZero.exp (-2 : ℤ) * Valued.v ((2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)))
      ≤ WithZero.exp (-2 : ℤ) * 1 := mul_le_mul_of_nonneg_left (q_int h2 hB hy) zero_le
    _ = WithZero.exp (-2 : ℤ) := mul_one _

theorem bound_step {q : ℝ} {M : ℕ} (hq : 2 ≤ q) (hM : 3 ≤ M) {Dp D' : ℝ}
    (hD' : |D' - 1| ≤ 2 / q ^ (M - 1))
    (hDp : |Dp - 1| ≤ 1 / q ^ (M - 1) + 1 / q ^ (2 * M - 1)) :
    |Dp + q ^ 2 / q ^ (2 * M) * D' - 1| ≤ 2 / q ^ (M - 1) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 3 := ⟨M - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e2 : 2 * (k + 3) - 1 = 2 * (k + 2) + 1 := by omega
  have e3 : 2 * (k + 3) = 2 * (k + 2) + 2 := by omega
  rw [e1] at hD' hDp ⊢
  rw [e2] at hDp
  rw [e3]
  have f1 : q ^ (2 * (k + 2) + 1) = (q ^ (k + 2)) ^ 2 * q := by rw [pow_succ, pow_mul']
  have f2 : q ^ (2 * (k + 2) + 2) = (q ^ (k + 2)) ^ 2 * q ^ 2 := by rw [pow_add, pow_mul']
  rw [f1] at hDp
  rw [f2]
  have ht4 : 4 ≤ q ^ (k + 2) := by
    have h1 : q ^ 2 ≤ q ^ (k + 2) := pow_le_pow_right₀ (by linarith) (by omega)
    nlinarith
  generalize q ^ (k + 2) = t at ht4 hD' hDp ⊢
  have htpos : 0 < t := by linarith
  have hqr : q ^ 2 / (t ^ 2 * q ^ 2) * D' = (1 / t) ^ 2 * D' := by
    field_simp
  have hf1 : 1 / (t ^ 2 * q) = (1 / t) ^ 2 * (1 / q) := by field_simp
  have hf2 : 2 / t = 2 * (1 / t) := by ring
  rw [hqr, hf2]
  rw [hf2] at hD'
  rw [hf1] at hDp
  have hu0 : 0 < 1 / t := by positivity
  have hu4 : 1 / t ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) ht4
  have hr0 : 0 < 1 / q := by positivity
  have hr2 : 1 / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
  generalize 1 / t = u at hu0 hu4 hD' hDp ⊢
  generalize 1 / q = r at hr0 hr2 hDp
  rw [abs_le] at hD' hDp ⊢
  obtain ⟨hb1, hb2⟩ := hD'
  obtain ⟨ha1, ha2⟩ := hDp
  have p1 := mul_le_mul_of_nonneg_left hb2 (sq_nonneg u)
  have p2 := mul_le_mul_of_nonneg_left hb1 (sq_nonneg u)
  have p3 := mul_le_mul_of_nonneg_left hr2 (sq_nonneg u)
  have p4 := mul_le_mul_of_nonneg_left hu4 hu0.le
  have p5 := mul_le_mul_of_nonneg_left hu4 (sq_nonneg u)
  have p6 := mul_nonneg (sq_nonneg u) hr0.le
  constructor <;> nlinarith

theorem local_quadratic_density_bound_at_level {lam : Measure (Fv F v)} (hstd : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    [DecidableEq ι] (B : Matrix ι ι (Fv F v)) (hsym : B.IsSymm)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hdet : Valued.v B.det = 1)
    (M : ℕ) (hc : Fintype.card ι = 2 * M) (hM : 3 ≤ M) (n : ℕ) :
    ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 → WithZero.exp (-(n : ℤ)) ≤ Valued.v s →
      ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) ∧
        ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
          (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
            (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  haveI := borel_Fv (F := F) (v := v)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hs0 hsn
  obtain ⟨π, hπ⟩ := exists_unif v
  have hπ0 : π ≠ 0 := pi_ne_zero hπ
  have hN1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hq2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
    exact_mod_cast this
  obtain ⟨Dp, hDpb, hP⟩ := GlobalTheory.T.local_quadratic_density_near_one F v lam hstd h2 ι B hsym hB hdet M hc (by omega) s hs
  have hvs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs0
  have hL : Valued.v s = WithZero.exp (WithZero.log (Valued.v s)) := (WithZero.exp_log hvs0).symm
  have hLn : -(n : ℤ) ≤ WithZero.log (Valued.v s) := by
    have h := hsn
    rw [hL, WithZero.exp_le_exp] at h
    exact h
  have hvs1 : Valued.v s ≤ 1 := hs
  have hmeasPrim : MeasurableSet {x : ι → Fv F v | ∃ i, Valued.v (x i) = 1} := meas_prim
  have hinter : ∀ A : Set (Fv F v),
      {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} ∩
        {x | ∃ i, Valued.v (x i) = 1} =
      {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧
        (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} := by
    intro A
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  have hsplit : ∀ A : Set (Fv F v),
      (Measure.pi fun _ : ι => lam)
        {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} =
      (Measure.pi fun _ : ι => lam)
        ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} ∩
          {x | ∃ i, Valued.v (x i) = 1}) +
      (Measure.pi fun _ : ι => lam)
        ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \
          {x | ∃ i, Valued.v (x i) = 1}) :=
    fun A => (measure_inter_add_diff _ hmeasPrim).symm
  rcases le_or_gt (-1 : ℤ) (WithZero.log (Valued.v s)) with hbig | hsmall
  · refine ⟨Dp, ?_, fun A hA hA' => ?_⟩
    · have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have hpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) := by positivity
      have h1 : 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M - 1) ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) :=
        one_div_le_one_div_of_le hpos hpow
      have h2' : 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) =
          1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) := by ring
      rw [h2']
      linarith
    · have hsub1 : A ⊆ {z | Valued.v (z - s) < 1} := fun z hz => lt_of_lt_of_le (hA' hz) hvs1
      have hempty : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \ {x | ∃ i, Valued.v (x i) = 1} = ∅ := by
        refine Set.subset_empty_iff.mp (fun x hx => ?_)
        obtain ⟨⟨hint, hQ⟩, hnp⟩ := hx
        have hle := q_nonprim h2 hB hπ hint hnp
        have heq : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x))) = Valued.v s :=
          Valuation.map_eq_of_sub_lt _ (hA' hQ)
        rw [heq, hL, WithZero.exp_le_exp] at hle
        exact absurd hle (by omega)
      rw [hsplit A, hempty, measure_empty, add_zero, hinter A, hP A hA hsub1]
  · obtain ⟨s', hss⟩ : ∃ s' : Fv F v, π * (π * s') = s :=
      ⟨π⁻¹ * (π⁻¹ * s), by rw [mul_inv_cancel_left₀ hπ0, mul_inv_cancel_left₀ hπ0]⟩
    have hrel : Valued.v s = WithZero.exp (-2 : ℤ) * Valued.v s' := by rw [← hss, val_pp hπ]
    have hvs'0 : Valued.v s' ≠ 0 := by
      intro h0
      apply hvs0
      rw [hrel, h0, mul_zero]
    have hL' : Valued.v s' = WithZero.exp (WithZero.log (Valued.v s')) := (WithZero.exp_log hvs'0).symm
    have hLL : WithZero.log (Valued.v s) = -2 + WithZero.log (Valued.v s') := by
      have h := hrel
      rw [hL, hL', ← WithZero.exp_add] at h
      have h1 := WithZero.exp_le_exp.mp h.le
      have h2'' := WithZero.exp_le_exp.mp h.ge
      omega
    have hs'int : s' ∈ v.adicCompletionIntegers F := by
      show Valued.v s' ≤ 1
      rw [hL']
      exact (WithZero.exp_le_exp.mpr (by omega : WithZero.log (Valued.v s') ≤ 0)).trans_eq WithZero.exp_zero
    have hs'0 : s' ≠ 0 := (Valuation.ne_zero_iff _).mp hvs'0
    have hn2 : 2 ≤ n := by omega
    have hs'n : WithZero.exp (-((n - 2 : ℕ) : ℤ)) ≤ Valued.v s' := by
      rw [hL', WithZero.exp_le_exp]
      omega
    obtain ⟨D', hD'b, hD'P⟩ := ih (n - 2) (by omega) s' hs'int hs'0 hs'n
    set K : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (2 * M) with hK
    have hK0 : K ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN0)
    set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ 2 / K with hc'
    have hcK : K * c = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ 2 := by
      rw [hc', mul_div_assoc', mul_div_cancel_left₀ _ hK0]
    refine ⟨Dp + c * D', ?_, fun A hA hA' => ?_⟩
    · have hcast : ((Dp + c * D' : ℝ≥0) : ℝ) =
          (Dp : ℝ) + (Ideal.absNorm v.asIdeal : ℝ) ^ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * M) * (D' : ℝ) := by
        rw [hc', hK]
        push_cast
        ring
      rw [hcast]
      exact bound_step hq2 hM hD'b hDpb
    · have hsub1 : A ⊆ {z | Valued.v (z - s) < 1} := fun z hz => lt_of_lt_of_le (hA' hz) hvs1
      obtain ⟨hA'meas, hlamA'⟩ := lam_scale hstd hπ hA
      have hA'sub : {z | π * (π * z) ∈ A} ⊆ {z | Valued.v (z - s') < Valued.v s'} := by
        intro z hz
        have h := hA' hz
        simp only [Set.mem_setOf_eq] at h ⊢
        have he : π * (π * z) - s = π * (π * (z - s')) := by rw [← hss]; ring
        rw [he, val_pp hπ, hrel] at h
        by_contra hcon
        have := mul_le_mul_of_nonneg_left (not_lt.mp hcon) (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-2 : ℤ))
        exact absurd h (not_lt.mpr this)
      have hD'A := hD'P _ hA'meas hA'sub
      have hset : {y : ι → Fv F v | (fun i => π * y i) ∈
          ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \
            {x | ∃ i, Valued.v (x i) = 1})} =
          {y | (∀ i, y i ∈ v.adicCompletionIntegers F) ∧
            (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ {z | π * (π * z) ∈ A}} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_diff]
        constructor
        · rintro ⟨⟨hint, hQ⟩, hnp⟩
          refine ⟨fun i => ?_, ?_⟩
          · have h1 : Valued.v (π * y i) ≤ 1 := hint i
            have h2' : Valued.v (π * y i) ≠ 1 := fun h => hnp ⟨i, h⟩
            have h3 := div_int hπ h1 h2'
            rwa [← mul_assoc, inv_mul_cancel₀ hπ0, one_mul] at h3
          · rw [← q_smul]
            exact hQ
        · rintro ⟨hyint, hQ⟩
          refine ⟨⟨fun i => (pi_mul_lt hπ (hyint i)).le, ?_⟩, ?_⟩
          · rw [q_smul]
            exact hQ
          · rintro ⟨i, hi⟩
            exact absurd hi (pi_mul_lt hπ (hyint i)).ne
      have hscale := pi_scale hstd hπ
        ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \
          {x | ∃ i, Valued.v (x i) = 1})
      rw [hset, hD'A, hlamA', hc] at hscale
      have hKe : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (2 * M) = (K : ℝ≥0∞) := by
        rw [hK]; push_cast; rfl
      rw [hKe] at hscale
      have hnp : (Measure.pi fun _ : ι => lam)
          ({x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} \
            {x | ∃ i, Valued.v (x i) = 1}) = ((c * D' : ℝ≥0) : ℝ≥0∞) * lam A := by
        apply (ENNReal.mul_right_inj (a := (K : ℝ≥0∞)) (by exact_mod_cast hK0) ENNReal.coe_ne_top).mp
        rw [← hscale, ← mul_assoc (K : ℝ≥0∞), ← ENNReal.coe_mul, ← mul_assoc K c D', hcK]
        push_cast
        ring
      rw [hsplit A, hnp, hinter A, hP A hA hsub1]
      push_cast
      ring

theorem density_near_value : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ M : ℕ, Fintype.card ι = 2 * M → 3 ≤ M → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 → ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) ∧ ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} → (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  intro F _ _ v lam hstd h2 ι _ _ B hsym hB hdet M hc hM s hs hs0
  have hvs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs0
  have hL : Valued.v s = WithZero.exp (WithZero.log (Valued.v s)) := (WithZero.exp_log hvs0).symm
  have hle : WithZero.log (Valued.v s) ≤ 0 := by
    have h1 : WithZero.exp (WithZero.log (Valued.v s)) ≤ WithZero.exp (0 : ℤ) := by
      rw [← hL, WithZero.exp_zero]; exact hs
    exact WithZero.exp_le_exp.mp h1
  refine local_quadratic_density_bound_at_level hstd h2 B hsym hB hdet M hc hM (WithZero.log (Valued.v s)).natAbs s hs hs0 ?_
  rw [hL, WithZero.exp_le_exp, WithZero.log_exp]
  omega

end GlobalTheory.CompanionTheory.SW.GBall
end
end
