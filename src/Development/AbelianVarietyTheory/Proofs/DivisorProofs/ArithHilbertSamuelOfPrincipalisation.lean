import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelSmallSectionsChangeOfMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundCountRankAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelUpperBoundCountRankAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodSectionGroupFamilyAmpleMultiples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqOneOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRegPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreimagePositiveResidueDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubset
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPfA

section
section
open Filter Topology

namespace GlobalTheory

theorem hsGrowth_log_add_div_tendsto (D : ℕ) :
    Tendsto (fun m : ℕ => Real.log ((m : ℝ) + D) / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-(D : ℝ)) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right _ (D : ℝ) tendsto_natCast_atTop_atTop)
  refine h.congr (fun m => ?_)
  simp

theorem hsGrowth_log_floor_le {Y : ℝ} (hY : 0 < Y) :
    Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log 3 + |Real.log Y| := by
  have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  rcases lt_or_ge Y 1 with h | h
  · have : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr h
    simp only [this, mul_zero, zero_add, Nat.cast_one, Real.log_one]
    linarith [abs_nonneg (Real.log Y)]
  · have h1 : ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Y := by
      push_cast
      have := Nat.floor_le hY.le
      linarith
    calc Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (3 * Y) := Real.log_le_log (by positivity) h1
      _ = Real.log 3 + Real.log Y := Real.log_mul (by norm_num) hY.ne'
      _ ≤ Real.log 3 + |Real.log Y| := by linarith [le_abs_self (Real.log Y)]

theorem hsGrowth_exp_radius : ∀ (D e δ : ℕ) (N : ℕ → ℝ → ℕ) (κ t : ℝ), 0 < e → 0 < κ → κ ≤ 1 → 0 < t → (∀ m, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' → N m R ≤ N m R') → (∀ s : ℕ, s < e → ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, δ / ((e : ℝ) ^ D * D.factorial) * t - ε ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ∧ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ δ / ((e : ℝ) ^ D * D.factorial) * (t - Real.log κ / e) + ε := by
  intro D e δ N κ t he hκ hκ1 ht hmono h ε hε
  have h' : ∀ s : ℕ, ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ (s < e → ∀ (q : ℕ) (R : ℝ), 0 ≤ R →
      (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧
      N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) := by
    intro s
    by_cases hs : s < e
    · obtain ⟨c, c', C, C', h1, h2, h3⟩ := h s hs
      exact ⟨c, c', C, C', h1, h2, fun _ => h3⟩
    · exact ⟨0, 0, 1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose c c' C C' hC hC' hb using h'
  set L : ℝ := δ / ((e : ℝ) ^ D * D.factorial) with hL
  have hdiv : ∀ q s, s < e → (e * q + s) / e = q ∧ (e * q + s) % e = s := by
    intro q s hs
    constructor
    · rw [add_comm, Nat.add_mul_div_left _ _ he, Nat.div_eq_of_lt hs, zero_add]
    · rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have hlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D)
      atTop (𝓝 L) := by
    refine GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e - c (m % e) + D).choose D) he ?_
    intro s hs
    refine ⟨c s, 0, fun q => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hdiv (q + c s) s hs
      simp only [h1, h2, Nat.add_sub_cancel, le_refl]
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [h1, h2, add_zero]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))
  have hup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D)
      atTop (𝓝 L) := by
    refine GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e + c' (m % e) + D).choose D) he ?_
    intro s hs
    refine ⟨0, c' s, fun q => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [add_zero, h1, h2]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [h1, h2, le_refl]
  set B : ℝ := ∑ s ∈ Finset.range e, |Real.log (C s)| with hBdef
  set B' : ℝ := ∑ s ∈ Finset.range e, |Real.log (C' s)| with hB'def
  set P : ℝ := ∑ s ∈ Finset.range e, (c' s : ℝ) with hPdef
  set M : ℕ := ∑ s ∈ Finset.range e, c s with hMdef
  have hB : ∀ s, s < e → Real.log (C s) ≤ B := fun s hs => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun s => |Real.log (C s)|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.mpr hs))
  have hB' : ∀ s, s < e → |Real.log (C' s)| ≤ B' := fun s hs =>
    Finset.single_le_sum (f := fun s => |Real.log (C' s)|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.mpr hs)
  have hP : ∀ s, s < e → (c' s : ℝ) ≤ P := fun s hs =>
    Finset.single_le_sum (f := fun s => (c' s : ℝ)) (fun i _ => Nat.cast_nonneg _)
      (Finset.mem_range.mpr hs)
  have hlk : Real.log κ ≤ 0 := Real.log_nonpos hκ.le hκ1

  have hlowE : ∀ᶠ m : ℕ in atTop,
      ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
        (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) ≤
      Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop (e * M + 1)] with m hm
    have hm0' : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos _) hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm0'
    set s := m % e with hs_def
    have hse : s < e := Nat.mod_lt _ he
    have hcm : c s ≤ m / e := by
      have : M ≤ m / e := by
        rw [Nat.le_div_iff_mul_le he]
        rw [mul_comm]; linarith
      exact (Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr hse)).trans this
    set q := m / e - c s with hq
    have hqm : q ≤ m := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
    have hmq : e * (q + c s) + s = m := by
      rw [hq, Nat.sub_add_cancel hcm]; exact Nat.div_add_mod m e
    have hKpos : 0 < (q + D).choose D := Nat.choose_pos (by omega)
    have hKpos' : (0 : ℝ) < ((q + D).choose D : ℝ) := by exact_mod_cast hKpos
    have hCs := hC s
    set R : ℝ := Real.exp (t * m) / (C s * ((q + D).choose D : ℝ)) with hR
    have hRpos : 0 < R := by rw [hR]; positivity
    have hCKR : C s * ((q + D).choose D : ℝ) * R = Real.exp (t * m) := by
      rw [hR]; field_simp
    have hb1 := (hb s hse q R hRpos.le).1
    rw [hmq, hCKR] at hb1
    have hK1 : Real.log ((q + D).choose D : ℝ) ≤ D * Real.log ((m : ℝ) + D) := by
      rw [← Real.log_pow]
      apply Real.log_le_log hKpos'
      have : (q + D).choose D ≤ (m + D) ^ D :=
        (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
      exact_mod_cast this
    set K := (q + D).choose D with hK
    have hlogN : (δ * K : ℝ) * Real.log R ≤ Real.log (N m (Real.exp (t * m))) := by
      have h1 : R ≤ ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        have := Nat.lt_floor_add_one R
        have := Nat.cast_nonneg (α := ℝ) ⌊R⌋₊
        linarith
      have h2 : ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) ≤ N m (Real.exp (t * m)) := by
        exact_mod_cast hb1
      have h3 : (0 : ℝ) < (((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ) : ℝ) := by positivity
      calc (δ * K : ℝ) * Real.log R ≤ (δ * K : ℝ) * Real.log ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log hRpos h1) (by positivity)
        _ = Real.log ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) := by
            rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
        _ ≤ _ := Real.log_le_log h3 h2
    have hlogR : t * m - B - D * Real.log ((m : ℝ) + D) ≤ Real.log R := by
      rw [hR, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp,
        Real.log_mul hCs.ne' hKpos'.ne']
      linarith [hB s hse]
    have key : (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) ≤
        Real.log (N m (Real.exp (t * m))) :=
      (mul_le_mul_of_nonneg_left hlogR (by positivity)).trans hlogN
    rw [le_div_iff₀ (by positivity)]
    calc ((δ * K : ℕ) : ℝ) / (m : ℝ) ^ D * (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) *
          (m : ℝ) ^ (D + 1) = (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) := by
          push_cast; field_simp; ring
      _ ≤ _ := key

  have hupE : ∀ᶠ m : ℕ in atTop, Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤
      ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
        ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    set s := m % e with hs_def
    have hse : s < e := Nat.mod_lt _ he
    set q := m / e with hq
    have hmq : e * q + s = m := Nat.div_add_mod m e
    have hCs := hC' s
    set Y : ℝ := C' s * Real.exp (t * m) / κ ^ (q + c' s) with hY
    have hYpos : 0 < Y := by rw [hY]; positivity
    have hb2 := (hb s hse q (Real.exp (t * m)) (Real.exp_pos _).le).2
    rw [hmq, ← hY] at hb2
    set K := (q + c' s + D).choose D with hK
    have hlogN : Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|) := by
      have h0 : 0 ≤ Real.log 3 + |Real.log Y| := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); positivity
      rcases Nat.eq_zero_or_pos (N m (Real.exp (t * m))) with hN | hN
      · rw [hN, Nat.cast_zero, Real.log_zero]; positivity
      · calc Real.log (N m (Real.exp (t * m)))
            ≤ Real.log ((((2 * ⌊Y⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) :=
              Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hb2)
          _ = (δ * K : ℝ) * Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hsGrowth_log_floor_le hYpos) (by positivity)
    have hlogY : |Real.log Y| ≤ B' + t * m + (m / e + P) * (-Real.log κ) := by
      rw [hY, Real.log_div (by positivity) (by positivity),
        Real.log_mul hCs.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
      have hq1 : ((q : ℕ) : ℝ) ≤ (m : ℝ) / e := Nat.cast_div_le
      have hc1 := hP s hse
      have hx : ((q : ℝ) + c' s) * (-Real.log κ) ≤ ((m : ℝ) / e + P) * (-Real.log κ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have hx0 : 0 ≤ ((q : ℝ) + c' s) * (-Real.log κ) := mul_nonneg (by positivity) (by linarith)
      have ha := abs_le.mp (hB' s hse)
      have htm : 0 ≤ t * m := by positivity
      rw [abs_le]; push_cast; constructor <;> nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|) := hlogN
      _ ≤ (δ * K : ℝ) * (Real.log 3 + (B' + t * m + (m / e + P) * (-Real.log κ))) := by
          gcongr
      _ = ((δ * K : ℕ) : ℝ) / (m : ℝ) ^ D *
            ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e)) * (m : ℝ) ^ (D + 1) := by
          push_cast; field_simp; ring

  have hLlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
      (t - (B / m + D * (Real.log ((m : ℝ) + D) / m)))) atTop (𝓝 (L * t)) := by
    have h0 : Tendsto (fun m : ℕ => B / (m : ℝ) + D * (Real.log ((m : ℝ) + D) / m)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat B).add
        ((hsGrowth_log_add_div_tendsto D).const_mul (D : ℝ))
      simpa only [mul_zero, add_zero] using this
    have := hlow.mul ((tendsto_const_nhds (x := t)).sub h0)
    simpa only [sub_zero] using this
  have hLup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
      ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e))) atTop
      (𝓝 (L * (t - Real.log κ / e))) := by
    have := hup.mul ((tendsto_const_div_atTop_nhds_zero_nat (Real.log 3 + B' + P * (-Real.log κ))).add
      (tendsto_const_nhds (x := t - Real.log κ / e)))
    simpa only [zero_add] using this
  have e1 := hLlow.eventually (lt_mem_nhds (show L * t - ε < L * t by linarith))
  have e2 := hLup.eventually (gt_mem_nhds
    (show L * (t - Real.log κ / e) < L * (t - Real.log κ / e) + ε by linarith))
  filter_upwards [e1, e2, hlowE, hupE] with m h1 h2 h3 h4
  exact ⟨by linarith, by linarith⟩

end GlobalTheory
end

open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_growth_exponential_radii : ∀ (D e δ : ℕ) (N : ℕ → ℝ → ℕ) (κ t : ℝ), 0 < e → 0 < κ → κ ≤ 1 → 0 < t → (∀ m, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' → N m R ≤ N m R') → (∀ s : ℕ, s < e → ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, δ / ((e : ℝ) ^ D * D.factorial) * t - ε ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ∧ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ δ / ((e : ℝ) ^ D * D.factorial) * (t - Real.log κ / e) + ε := by
  atlas_forward_decl GlobalTheory.hsGrowth_exp_radius
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem lc_exp_bounds : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ κ t : ℝ, 0 < κ → κ ≤ 1 → 0 < t → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, gdeg P.L D / D.factorial * t - ε ≤ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ∧ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ≤ gdeg P.L D / D.factorial * (t - Real.log κ / e) + ε := by
  intro hA k _ X _ p D hp P hL e x hx κ t hκ hκ1 ht h1 h2 ε hε
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hA k X p D hp P hL e x hx
  have hup := GlobalTheory.T.arithHilbertSamuel_upperBound_count_rank_ample k X p D hp P hL e x hx
  have hlo := GlobalTheory.T.arithHilbertSamuel_lowerBound_count_rank_ample k X p D hp P hL e x hx
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hfin : ∀ (m : ℕ) (R : ℝ), 0 ≤ R → (P.Bl m 1 R).Finite := by
    intro m R hR
    obtain ⟨c, C, _, h⟩ := hup m 1
    have := ((h 0).2.2 R κ hR hκ h2).1
    simpa using this
  have key := GlobalTheory.T.count_growth_exponential_radii D e (Module.finrank (ratF x) X.functionField) (fun m R => (P.Bl m 1 R).ncard) κ t
    hx.pos hκ hκ1 ht
    (fun m R R' hR hRR' => Set.ncard_le_ncard
      (fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans hRR'⟩) (hfin m R' (hR.trans hRR')))
    (fun s _ => by
      obtain ⟨c, C, hC, h⟩ := hlo s 1
      obtain ⟨c', C', hC', h'⟩ := hup s 1
      refine ⟨c, c', C, C', hC, hC', fun q R hR => ⟨?_, ?_⟩⟩
      · have h3 := (h q).2 R hR h1
        have hf := hfin (e * (q + c) + s) (C * (q + D).choose D * R) (by positivity)
        have e1 : ((e * (q + c) + s : ℕ) : ℤ) = e * (q + c : ℕ) + s := by push_cast; ring
        rw [← e1, ← hf.cast_ncard_eq] at h3
        exact_mod_cast h3
      · have h3 := ((h' q).2.2 R κ hR hκ h2).2
        have e1 : ((e * q + s : ℕ) : ℤ) = e * q + s := by push_cast; ring
        rw [← e1] at h3
        exact h3) ε hε
  have e2 : (Module.finrank (ratF x) X.functionField : ℝ) / ((e : ℝ) ^ D * D.factorial) =
      gdeg P.L D / D.factorial := by
    rw [hdeg, mul_div_mul_left _ _ (pow_pos he D).ne']
  rw [e2] at key
  exact key

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionCount_growth_metric_near_generatorMax : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ κ t : ℝ, 0 < κ → κ ≤ 1 → 0 < t → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, gdeg P.L D / D.factorial * t - ε ≤ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ∧ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ≤ gdeg P.L D / D.factorial * (t - Real.log κ / e) + ε := by
  atlas_forward_decl GlobalTheory.HSAmp.lc_exp_bounds
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem canNorms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  intro k _ X _ p D _ P e x hx n u hn hu
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : 2 * n ≠ 0 := by omega
  have hup := GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u (e : ℤ) 0
  have hnn : ∀ (Q : Pair p) σ (y : CxPts p σ) f, 0 ≤ Q.nu e 0 σ y f := fun Q σ y f => by
    rw [← norm_val]; exact norm_nonneg _
  have hS : ∀ σ (y : CxPts p σ), 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y
    obtain ⟨l, hl⟩ := hx.cover (under y)
    have h := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2
    exact lt_of_lt_of_le (pow_pos h _) (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l))
  have key : ∀ σ (y : CxPts p σ) f, (upperParabolic P u).nu e 0 σ y f ^ (2 * n) =
      P.nu e 0 σ y f ^ (2 * n) / ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y f
    rw [(hup.2.2 σ y f).2, mul_pow, ← Real.exp_nat_mul, hu σ y]
    have : ((2 * n : ℕ) : ℝ) * (-(((e : ℤ) : ℝ) * (((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)))) / 2)
        = -Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)) := by
      push_cast; field_simp
    rw [this, Real.exp_neg, Real.exp_log (hS σ y), div_eq_mul_inv]
  refine ⟨fun l σ y => ?_, fun σ y => ?_, ⟨hx.pos, fun l => hup.1 ▸ hx.mem l, fun z => ?_⟩, ⟨?_, fun l => ?_, fun z => ?_⟩, ?_⟩
  · rw [← pow_le_pow_iff_left₀ (hnn _ σ y _) zero_le_one hn0, one_pow, key, div_le_one (hS σ y)]
    exact Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l)
  · obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => P.nu e 0 σ y (x l)) Finset.univ_nonempty
    refine ⟨l, ?_⟩
    rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (hnn _ σ y _) hn0, key, ← Real.exp_nat_mul]
    have e1 : ((2 * n : ℕ) : ℝ) * -(Real.log (D + 1) / (2 * n)) = -Real.log (D + 1) := by
      push_cast; field_simp
    have hD : (0 : ℝ) < D + 1 := by positivity
    rw [e1, Real.exp_neg, Real.exp_log hD, inv_eq_one_div, div_le_div_iff₀ hD (hS σ y), one_mul]
    calc ∑ i, P.nu e 0 σ y (x i) ^ (2 * n) ≤ ∑ _i : Fin (D + 1), P.nu e 0 σ y (x l) ^ (2 * n) :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hnn P σ y _) (hl i (Finset.mem_univ i)) _
      _ = P.nu e 0 σ y (x l) ^ (2 * n) * (D + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  · obtain ⟨l, hl⟩ := hx.cover z
    exact ⟨l, (hup.2.1 (x l)).symm ▸ hl⟩
  · exact Nat.mul_pos hx.pos hn
  · have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).1
    convert h using 2 <;> push_cast <;> ring
  · obtain ⟨l, hl⟩ := hx.cover z
    refine ⟨l, ?_⟩
    have h := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.1 n hn
    have e2 : ((e * n : ℕ) : ℤ) = (n : ℤ) * (e : ℤ) := by push_cast; ring
    have e3 : (0 : ℤ) = (n : ℤ) * 0 := by ring
    show z ∈ NV P ((e * n : ℕ) : ℤ) 0 (x l ^ n)
    rw [e2, e3, h]; exact hl
  · intro σ y
    have hp : ∀ l, P.nu ((e * n : ℕ) : ℤ) 0 σ y (x l ^ n) = P.nu e 0 σ y (x l) ^ n := fun l => by
      have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).2 σ y
      convert h using 2 <;> push_cast <;> ring
    rw [hu σ y]
    simp only [hp, ← pow_mul]
    push_cast
    ring_nf

end GlobalTheory.HSAmp
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  atlas_forward_decl GlobalTheory.HSAmp.canNorms
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem selfInter_canWeight_le : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∃ C : ℝ, ∀ (n : ℕ) (u : SmFn p) (a : ℝ), 1 ≤ n → IsCan P e n x u →
      (up P.L u).IsSelfInter a → |a| ≤ C / n := by
  intro hC k _ X _ p D hX P hA e x hG
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  have hf : 0 < Module.finrank ℤ k := Module.finrank_pos
  have he : 0 < e := hG.pos
  obtain ⟨hPI, -, -, -, -, -, -⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hA e x hG
  obtain ⟨hPV, -, -⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D

  obtain ⟨Φ₀, hΦ₀⟩ := ((hC.arExists k (PSpace k D) (PSpace.str k D) D hPV).2 Unit
    fun _ => ProjSpace.hermitianTwistingSheaf k D).1
  have hH := ((hC.arIso k (PSpace k D) (PSpace.str k D) D hPV).2 Unit _ Φ₀ hΦ₀).1 ()
  set H := Φ₀ (MvPolynomial.X () ^ (D + 1)) with hHdef
  set g := gdeg P.L D
  refine ⟨|g * H| / ((Module.finrank ℤ k : ℝ) * e), fun n u a hn hu ha => ?_⟩
  obtain ⟨-, -, -, hG', hu'⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hG n u hn hu
  obtain ⟨hPI', π, hπ, hgen, hd, hdf, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hA (e * n) _ hG'
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hC k X p D hX P hA (e * n) _ hG'
  have hpow := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hC k X p D hX).2 (up P.L u) (e * n) a ha
  have hpull := ((hC.arProj k (PSpace k D) X (PSpace.str k D) p D hPV hX π hπ hgen hd).1 _ H hH)

  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => (up P.L u).pow (e * n)).1
  have hI := hC.arIso k X p D hX
  have h₁ := (hI.2 Unit _ Φ hΦ).1 ()
  have hΦ' := (hI.2 Unit _ Φ hΦ).2.1 (fun _ => (ProjSpace.hermitianTwistingSheaf k D).pull π hπ) fun _ => hiso u hu'
  have h₂ := (hI.2 Unit _ Φ hΦ').1 ()
  have e₁ := HermLB.IsSelfInter.unique hX hpow h₁
  have e₂ := HermLB.IsSelfInter.unique hX hpull h₂

  set d : ℝ := ((π.residueDegree (genericPoint X) : ℕ) : ℝ)
  set f : ℝ := ((Module.finrank ℤ k : ℕ) : ℝ)
  set E : ℝ := ((e * n : ℕ) : ℝ)
  have hE : 0 < E := by positivity
  have hfpos : (0 : ℝ) < f := Nat.cast_pos.mpr hf
  have key1 : E ^ (D + 1) * a = d * H := e₁.trans e₂.symm
  have key2 : d * f = E ^ D * g := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hdf
    simp only [Nat.cast_mul] at this
    rw [← hdeg]; exact this
  have ha' : a = g * H / (f * E) := by
    field_simp
    have : E ^ (D + 1) * a * f = E ^ D * g * H := by rw [key1, ← key2]; ring
    have hED : E ^ D ≠ 0 := pow_ne_zero _ hE.ne'
    apply mul_left_cancel₀ hED
    linear_combination this
  rw [ha', abs_div, abs_of_pos (by positivity : (0:ℝ) < f * E)]
  have : f * E = (f * e) * n := by simp [E, f]; ring
  rw [this, div_div]

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfIntersection_canonicalWeights_tendsto_zero : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ C : ℝ, ∀ (n : ℕ) (u : SmFn p) (a : ℝ), 1 ≤ n → IsCan P e n x u → (up P.L u).IsSelfInter a → |a| ≤ C / n := by
  atlas_forward_decl GlobalTheory.HSAmp.selfInter_canWeight_le
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace GlobalTheory.HSAmp

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

theorem semiPos_up_of_isCan : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x →
    ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (up P.L u).SemiPos D := by
  intro k _ X _ p D _ P e x hx n u hn hu σ i c y hy ξ
  set j := pick (P.A.φ σ).isLB y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick (P.A.φ σ).isLB y
  set O := ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef
  have hO : IsOpen O := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hen : (0 : ℝ) < (e : ℝ) * n := mul_pos he hn'

  have key : ∀ z ∈ O, 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) ∧
      (P.L.φ σ).φ i z + u.u σ z =
        ((e : ℝ) * n)⁻¹ * Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) := by
    intro z hz
    have hnu : ∀ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      intro l
      rw [GlobalTheory.VolBr.nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hz.1 hz.2, Complex.normSq_eq_norm_sq, norm_pow,
        mul_pow, ← pow_mul, ← Real.exp_nat_mul]
      congr 2
      · ring_nf
      · push_cast; ring
    have hsum : ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => hnu l
    have hpos : 0 < ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) := by
      obtain ⟨l, hl⟩ := hx.cover (under z)
      have h1 := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ z hl).2
      exact Finset.sum_pos' (fun l' _ => pow_nonneg (by unfold Pair.nu; positivity) _)
        ⟨l, Finset.mem_univ _, pow_pos h1 _⟩
    have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) := by
      rw [hsum] at hpos
      exact pos_of_mul_pos_left hpos (Real.exp_pos _).le
    refine ⟨hS, ?_⟩
    rw [hu σ z, hsum, Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
    ring
  have hyO : y ∈ O := ⟨hy.2, hj⟩
  have hW : IsOpen (c.e.target ∩ c.e.symm ⁻¹' O) := GlobalTheory.ChartGlue.isOpen_over c.e hO
  have hyW : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' O := GlobalTheory.ChartGlue.mem_over c.e hy.1 hyO
  have hG : ∀ l, ContDiffAt ℂ 2 (fun v => ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n) (c.e y) := fun l =>
    contDiffAt_two_of_holo hW (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P e 0 σ (x l) (hx.mem l) i j).2 D c).pow n) hyW
  have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm (c.e y)) ^ n) :=
    (key _ hyW.2).1
  have hf : ContDiffAt ℝ 2 (fun v => Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)))
      (c.e y) :=
    (ContDiffAt.sum fun l _ => contDiffAt_normSq_comp (hG l)).log hS.ne'
  have heq : (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((((e : ℝ) * n)⁻¹ *
        Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)) + 0 : ℝ) : ℂ) :=
    eventually_of_mem (hW.mem_nhds hyW) fun v hv => by
      dsimp only
      rw [add_zero, ← (key _ hv.2).2]
      rfl
  change 0 ≤ (leviV D (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) (c.e y) ξ).re
  rw [leviV_congr heq, leviV_const_mul hf _ 0, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.2 hen.le) (leviV_log_sum_nonneg (fun l => contDiffAt_normSq_comp (hG l))
    (fun l => logPshAt_normSq (hG l)) hS ξ)

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudyWeightIncrement_semiPositive_curvature : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (up P.L u).SemiPos D := by
  atlas_forward_decl GlobalTheory.HSAmp.semiPos_up_of_isCan
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_of_principalisation : GlobalTheory.Published.Principalisation → AmpleHS := by
  intro hPr k _ X _ p D hX P a hA hS ha
  have hC := GlobalTheory.MixHt.arCalc_of_principalisation hPr
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hA
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hx
  have hG := GlobalTheory.T.isGoodSectionGroupFamily_ampleMultiples hC k X p D hX P hA
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.arithHilbertSamuel_smallSections_change_of_metric hPr k X p D hX P a hS ha hG
  obtain ⟨C, hCb⟩ := GlobalTheory.T.selfIntersection_canonicalWeights_tendsto_zero hC k X p D hX P hA e x hx
  refine ⟨max (t₀ + B) 1, fun t ht => ?_⟩
  have ht1 : t₀ + B ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hball : ∀ (u : SmFn p) (m : ℕ) (R : ℝ), ballIn (upperParabolic P u) (P.H m 1) m 1 R = (upperParabolic P u).Bl m 1 R :=
    fun _ _ _ => rfl
  have hball' : ∀ (m : ℕ) (R : ℝ), ballIn P (P.H m 1) m 1 R = P.Bl m 1 R := fun _ _ => rfl
  have hF : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hF1 : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hLg : 0 ≤ Real.log ((D : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  set g := gdeg P.L D with hg
  have hc : (a + ((D : ℝ) + 1) * t * g) / ((D + 1).factorial : ℝ) = g / D.factorial * t + a / (D + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) - (g / D.factorial * t + a / (D + 1).factorial)|
        ≤ |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * n) / e) + |C| / n / (D + 1).factorial + 2 * ε := by
    intro n hn ε hε
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨u, hu, huB⟩ := hB n hn
    have hsemi := GlobalTheory.T.fubiniStudyWeightIncrement_semiPositive_curvature k X p D hX P e x hx n u hn hu
    obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (up P.L u)
    have hsi : (up P.L u).IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    have han := hCb n u _ hn hu hsi
    have hdiff := ht₀ u B _ hB0 huB hsemi hsi t ht1
    obtain ⟨hnu1, hnu2, hgu, -, -⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hx n u hn hu
    have hκ1 : Real.exp (-(Real.log ((D : ℝ) + 1) / (2 * n))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hLg (by positivity)))
    have hcnt := GlobalTheory.T.sectionCount_growth_metric_near_generatorMax hC k X p D hX (upperParabolic P u) hA e x hgu _ t (Real.exp_pos _) hκ1 ht2 hnu1 hnu2 ε hε
    rw [show (upperParabolic P u).L = up P.L u from rfl, GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hC k X p D hX P.L u, Real.log_exp, ← hg] at hcnt
    simp only [hball, hball'] at hdiff
    have hd := hdiff.eventually (Metric.ball_mem_nhds _ hε)
    set an := h (genericPoint X)
    set T := Real.log ((D : ℝ) + 1) / (2 * n) / e with hT
    have hT0 : 0 ≤ T := by positivity
    have hup : g / D.factorial * (t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e) ≤ g / D.factorial * t + |g| / D.factorial * T := by
      rw [show t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e = t + T by rw [hT]; ring, mul_add]
      gcongr
      exact le_abs_self g
    have han1 : an / (D + 1).factorial ≤ |C| / n / (D + 1).factorial :=
      div_le_div_of_nonneg_right ((le_abs_self an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    have hgT : 0 ≤ |g| / D.factorial * T := by positivity
    have han2 : -(an / (D + 1).factorial) ≤ |C| / n / (D + 1).factorial := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right ((neg_le_abs an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    filter_upwards [hd, hcnt] with m hm1 hm2
    rw [Real.dist_eq, abs_sub_lt_iff] at hm1
    have hsplit : P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) =
        (upperParabolic P u).lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) -
          (Real.log ((upperParabolic P u).Bl m 1 (Real.exp (t * m))).ncard - Real.log (P.Bl m 1 (Real.exp (t * m))).ncard) /
            (m : ℝ) ^ (D + 1) := by
      simp only [Pair.lc]; ring
    have hq : (an - a) / ((D + 1).factorial : ℝ) = an / (D + 1).factorial - a / (D + 1).factorial := sub_div _ _ _
    rw [hsplit, abs_le]
    constructor <;> linarith [hm2.1, hm2.2]
  rw [hc]
  refine Metric.tendsto_nhds.2 fun δ hδ => ?_
  set K := |g| / D.factorial * (Real.log ((D : ℝ) + 1) / 2 / e) + |C| / (D + 1).factorial with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / δ)
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hKn : |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) / e) +
      |C| / ((n + 1 : ℕ) : ℝ) / (D + 1).factorial = K / ((n + 1 : ℕ) : ℝ) := by
    rw [hK]; field_simp
  have hKlt : K / ((n + 1 : ℕ) : ℝ) < δ / 2 := by
    have h1 : 2 * K / δ < ((n + 1 : ℕ) : ℝ) := hn.trans (by exact_mod_cast Nat.lt_succ_self n)
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ hn1]
    linarith
  filter_upwards [key (n + 1) (Nat.le_add_left 1 n) (δ / 8) (by positivity)] with m hm
  rw [hKn] at hm
  rw [Real.dist_eq]
  linarith

end GlobalTheory.HSNef
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.HSNef.AmpleHS := by
  atlas_forward_decl GlobalTheory.HSNef.ampleHS_of_principalisation
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.Points GlobalTheory.SemiPosBir

namespace GlobalTheory.SemiPosEtale

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}

theorem exists_map_eq_of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range j) :
    ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  obtain ⟨v, hv⟩ := hy
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := y.1) v _ hv
  have : JacobsonSpace ↥(pullback j y.1) := LocallyOfFiniteType.jacobsonSpace (pullback.snd j y.1)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback j y.1)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨⟨pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hj, Category.assoc, pullback.condition_assoc, pointOfClosedPoint_comp_assoc]
    exact y.2
  · change (pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1) ≫ j = y.1
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

def img (j : Z ⟶ X) [Etale j] : X.Opens := ⟨Set.range j, j.isOpenMap.isOpen_range⟩

theorem PosOn.of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ (img j)) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq_of_etale j hj (mem_ptsIn.1 hy.2.2)
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

end GlobalTheory.SemiPosEtale

namespace GlobalTheory.SemiPosEtale

theorem semiPos_of_pull_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  intro k _ X Y _ _ p q D hp _ π hπ V hV hE L hL σ i
  have := hp.isDomain
  have := hp.finite
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Etale (V.ι ≫ π) := hE
  have hj : (V.ι ≫ π) ≫ p = V.ι ≫ q := by rw [Category.assoc, hπ]
  have hU : ((img (V.ι ≫ π) : X.Opens) : Set X).Nonempty := by
    obtain ⟨v, hv⟩ := hV
    exact ⟨_, ⟨v, hv⟩, rfl⟩
  change PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))
  refine PosOn.of_inter hσ (isOpen_ptsIn _) (L.cInf σ i) hU (PosOn.of_etale (V.ι ≫ π) hj ?_)
  let J : (L.B.pull π).ι := fun _ => i
  have h₀ : PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J)) := hL σ J
  have e₁ : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i) := Set.ext fun z => by
    rw [Set.mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
  have e₂ : ((L.φ σ).pull π hπ).φ J = fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  rw [e₁, e₂] at h₀
  have h₁ := h₀.pull V.ι (q := V.ι ≫ q) rfl
  have e₃ (w : CxPts (V.ι ≫ q) σ) : PtsOver.map π hπ _ (PtsOver.map V.ι rfl _ w) =
      PtsOver.map (V.ι ≫ π) hj _ w := Subtype.ext (Category.assoc _ _ _)
  simp only [e₃] at h₁
  exact h₁

end GlobalTheory.SemiPosEtale
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_of_pullback_generically_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  atlas_forward_decl GlobalTheory.SemiPosEtale.semiPos_of_pull_etale
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermLB

open Set GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPos_pull_of_genSmooth : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k) (D E : ℕ), GenSmooth p D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p),
    L.SemiPos D → (L.pull π hπ).SemiPos E := by
  intro k _ X Y p q D E hX π hπ L hL σ
  obtain ⟨R⟩ := hX σ
  intro i c y hy ξ
  set φ := L.φ σ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨a, h0⟩ := R.cover (m y)
  set c0 := R.chart a
  have him : m y ∈ ptsIn p σ (L.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V E → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn E _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L.cInf σ).contDiffAt c0 h0 him)
  have e : (fun v => ((L.pull π hπ).φ σ |>.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  show 0 ≤ (leviV E (fun v => ((L.pull π hπ).φ σ |>.φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp E D g F U hU _ hyU hF hg ξ, hFy]
  exact hL σ (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.HermLB
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_pull_of_genericallySmooth : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), GenSmooth p D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.SemiPos D → (L.pull π hπ).SemiPos E := by
  atlas_forward_decl GlobalTheory.HermLB.semiPos_pull_of_genSmooth
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GenEtale

theorem exists_opens_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hd
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper π := IsProper.of_comp π p
  have := hp.isLocallyNoetherian
  have := hp.charZero
  obtain ⟨U, -, hU, hxU, hW, -, hE, -⟩ :=
    GlobalTheory.GenFiniteEtale.exists_finite_etale_of_isProper π hη hd ⊤ (Opens.mem_top _)
  refine ⟨π ⁻¹ᵁ U, ⟨genericPoint Y, show π _ ∈ U from hη ▸ hxU⟩, ?_⟩
  have : IsAffine U := hU
  have : IsAffine (π ⁻¹ᵁ U) := hW
  have hE' : ∀ U' : X.Opens, U' = U → (π.app U').hom.Etale := by
    rintro _ rfl
    exact hE
  have e : U.ι ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have h1 : Etale (π ∣_ U) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
    exact (RingHom.Etale.respectsIso).cancel_right_isIso _ _ |>.2 (hE' _ e)
  rw [← morphismRestrict_ι]
  infer_instance

end GlobalTheory.GenEtale
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_opens_etale_generically_finite_dominant : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  atlas_forward_decl GlobalTheory.GenEtale.exists_opens_etale
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLift

open Limits GlobalTheory.MixHt

theorem exists_cover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X']
    [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D →
    IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X →
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧
      IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧
      g.residueDegree (genericPoint Y') ≠ 0 := by
  intro k _ X X' Y _ _ _ p D E ρ π hX hX' hY hρ

  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  obtain ⟨N', j', _, hj'⟩ := hX'.isProjOver
  have : IsProper (ρ ≫ p) := hj' ▸ inferInstance
  have : IsProper ρ := IsProper.of_comp ρ p
  have hs : Function.Surjective ρ := by
    rw [← Set.range_eq_univ]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def, ← ρ.isClosedMap.isClosed_range.closure_eq]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hρ⟩)
  have : Surjective ρ := ⟨hs⟩

  obtain ⟨z, hz, hdeg⟩ := exists_residueDegree_pos_of_mem_range _ _ (pullback.fst π ρ) (genericPoint Y)
    ((inferInstance : Surjective (pullback.fst π ρ)).surj _)
  set g := cloι z ≫ pullback.fst π ρ with hgdef
  have hg : g (genericPoint (clo z)) = genericPoint Y := by
    rw [hgdef, Scheme.Hom.comp_apply, cloι_genericPoint, hz]
  have hdeg' : g.residueDegree (genericPoint (clo z)) ≠ 0 := by
    rw [hgdef, CurveDegreesCompare.residueDegree_comp, Published.residueDegree_of_isClosedImmersion (cloι z), mul_one,
      cloι_genericPoint]
    exact hdeg.ne'

  have hP : IsProjOver (pullback.fst π ρ ≫ π ≫ p) :=
    FlagFamily.isProjOver_pullback_over hX.isProjOver hY.isProjOver hX'.isProjOver
  have hA : IsAmb (g ≫ π ≫ p) := by
    have := (IsAmb.mk hX.1 hX.2 hP).sub (cloι z)
    rwa [← Category.assoc] at this
  have hAY : IsAmb (π ≫ p) := isAmb_of_isArithVar hY

  obtain ⟨⟨m, hm⟩, -, -, -, -, hgen⟩ := hasDim_basic k (clo z) (g ≫ π ≫ p) hA
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo z))
  have hdY : HasDim (g (genericPoint (clo z))) (E + 1) := by
    rw [hg]
    exact (DimBasic.hasDim_genericPoint_iff Y (E + 1)).2 hY.dim_eq
  have hcmp := DimDeg.dim_le_and_residueDegree_ne_zero_iff k Y (clo z) (π ≫ p) (g ≫ π ≫ p) hAY hA g rfl
    (genericPoint (clo z)) d (E + 1) hd hdY
  have hdim : topologicalKrullDim (clo z) = (E + 1 : ℕ) := (hgen (clo z) (E + 1)).1 (hcmp.2.1 hdeg' ▸ hd)

  have hcY : CharZero Γ(Y, ⊤) := hY.charZero
  have h₁ : CharZero Y.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Y.Opens) (Opens.mem_top _))
  have h₂ : CharZero (Y.residueField (genericPoint Y)) := by
    let f : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue _).hom
    exact charZero_of_injective_ringHom f.injective
  have h₃ : CharZero (Y.residueField (g (genericPoint (clo z)))) := hg ▸ h₂
  have h₄ : CharZero ((clo z).residueField (genericPoint (clo z))) :=
    charZero_of_injective_ringHom (g.residueFieldMap _).hom.injective
  have h₅ : CharZero (clo z).functionField := by
    let f : (clo z).functionField →+* (clo z).residueField (genericPoint (clo z)) := ((clo z).residue _).hom
    exact (RingHom.charZero_iff f.injective).2 h₄
  have h₆ : CharZero Γ(clo z, ⊤) :=
    (RingHom.charZero_iff (fnOf_injective (⊤ : (clo z).Opens) (Opens.mem_top _))).2 h₅
  refine ⟨clo z, inferInstance, g, cloι z ≫ pullback.snd π ρ, ?_,
    ⟨hX.1, hX.2, inferInstance, hA.isProjOver, (flat_int_iff_charZero _).2 h₆, hdim⟩, hg, hdeg'⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]

end GlobalTheory.CoverLift
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithmeticCover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D → IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X → ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧ IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧ g.residueDegree (genericPoint Y') ≠ 0 := by
  atlas_forward_decl GlobalTheory.CoverLift.exists_cover_over_modification
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.SemiPosUp

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem levi_pull_nonneg {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {D D' : ℕ} {B : LB X}
    (φ : Weight p σ B) (hC : φ.IsCInf) (hSP : φ.SemiPosReg D) (i : (B.pull π).ι)
    (c : AlgChart q σ D') {y : CxPts q σ} (hy : y ∈ c.e.source ∩ ptsIn q σ ((B.pull π).U i))
    (c0 : AlgChart p σ D) (h0 : PtsOver.map π hπ (spMap σ) y ∈ c0.e.source) (ξ : Fin D' → ℂ) :
    0 ≤ (leviV D' (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re := by
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U :=
    GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

theorem semiPos_pull_of_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  intro k _ X Y _ _ p q D hp hq π hπ V hV he L hL
  have := hq.isDomain
  have := hq.finite
  obtain ⟨T, hT, hηT, hch⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k X p D hp
  let U : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨v, hv⟩ := hV
  obtain ⟨v', -, hv'⟩ := Flat.generalizingMap (V.ι ≫ π)
    (genericPoint_specializes ((V.ι ≫ π) ⟨v, hv⟩))
  have hW : ((π ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
    refine ⟨V.ι v', ?_⟩
    show π (V.ι v') ∈ Tᶜ
    rw [← Scheme.Hom.comp_apply, hv']
    exact hηT
  intro σ
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  intro i
  refine GlobalTheory.SemiPosBir.PosOn.of_inter hσ (isOpen_ptsIn _) ((L.cInf σ).pull π hπ i) hW ?_
  rintro c y ⟨hyc, hyS, hyW⟩ ξ
  obtain ⟨c0, h0⟩ := hch σ (PtsOver.map π hπ (spMap σ) y) (mem_ptsIn.1 hyW)
  exact levi_pull_nonneg π hπ (L.φ σ) (L.cInf σ) (hL σ) i c ⟨hyc, hyS⟩ c0 h0 ξ

end GlobalTheory.SemiPosUp
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPositive_pullback_generically_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  atlas_forward_decl GlobalTheory.SemiPosUp.semiPos_pull_of_etale
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SemiPullAll

theorem isometric_pull_pull {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem semiPull_of_principalisation : GlobalTheory.Published.Principalisation → SemiPull := by
  intro hP k _ X Y p q D E hp hq π hπ L hL
  have := hp.isIntegral
  have := hq.isIntegral
  obtain ⟨X', _, ρ, hρ, hsm, hgen, hdeg⟩ := GlobalTheory.GenRes.exists_birational_genSmooth hP k X p D hp
  obtain ⟨V, hV, het⟩ := GlobalTheory.T.exists_opens_etale_generically_finite_dominant k X X' p (ρ ≫ p) D hp hρ ρ rfl hgen (by rw [hdeg]; exact one_ne_zero)
  have h₁ : (L.pull ρ rfl).SemiPos D := GlobalTheory.T.semiPositive_pullback_generically_etale k X X' p (ρ ≫ p) D hp hρ ρ rfl V hV het L hL
  have hπp : IsArithVar (π ≫ p) E := by rw [hπ]; exact hq
  obtain ⟨Y', _, g, π', hcomm, hY', hggen, hgdeg⟩ := GlobalTheory.T.exists_arithmeticCover_over_modification k X X' Y p D E ρ π hp hρ hπp hgen
  have hY'q : IsArithVar (g ≫ q) E := by rw [← hπ]; exact hY'
  have e₁ : π' ≫ ρ ≫ p = g ≫ q := by rw [← Category.assoc, hcomm, Category.assoc, hπ]
  have e₂ : (g ≫ π) ≫ p = g ≫ q := by rw [Category.assoc, hπ]
  have h₂ : ((L.pull ρ rfl).pull π' e₁).SemiPos E :=
    GlobalTheory.T.semiPos_pull_of_genericallySmooth k X' Y' (ρ ≫ p) (g ≫ q) D E hsm π' e₁ (L.pull ρ rfl) h₁
  have iso : ((L.pull ρ rfl).pull π' e₁).Isometric ((L.pull π hπ).pull g rfl) :=
    (isometric_pull_pull L ρ rfl π' e₁ (g ≫ π) e₂ hcomm).trans
      (isometric_pull_pull L π hπ g rfl (g ≫ π) e₂ rfl).symm
  have h₃ : ((L.pull π hπ).pull g rfl).SemiPos E :=
    (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric (GlobalTheory.MixHt.arCalc_of_principalisation hP) k Y' (g ≫ q) E hY'q _ _ iso).1 h₂
  obtain ⟨W, hW, hWet⟩ := GlobalTheory.T.exists_opens_etale_generically_finite_dominant k Y Y' q (g ≫ q) E hq hY'q g rfl hggen hgdeg
  exact GlobalTheory.T.semiPos_of_pullback_generically_etale k Y Y' q (g ≫ q) E hq hY'q g rfl W hW hWet (L.pull π hπ) h₃

end GlobalTheory.SemiPullAll
end
end

section
namespace GlobalTheory

theorem arithHilbertSamuel_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel :=
  fun h => GlobalTheory.T.arithHilbertSamuel_nef_of_ample (GlobalTheory.MixHt.arCalc_of_principalisation h) (GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation h)
    (GlobalTheory.SemiPullAll.semiPull_of_principalisation h)

end GlobalTheory
end
