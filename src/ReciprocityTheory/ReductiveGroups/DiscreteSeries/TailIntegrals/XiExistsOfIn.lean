import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergHaarFactsHold
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiIntStepOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailFinOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.FormulaFOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.OscillatoryBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.AStepSuccOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.SphericalFunctionFixedUnitaryEqOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.BStepSuccOf

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem aAll_of (hb : AStepBase) (hs : AStepSucc) : ∀ k r : ℕ, 1 ≤ k → AAt k r := by
  intro k r hk
  induction r with
  | zero => exact hb k hk
  | succ r' ih => exact hs k (r' + 1) r' (by omega) hk ih

theorem bAll_of (hb : BStepBase) (hs : BStepSucc) :
    ∀ k r : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r δ := by
  intro k r hk
  induction r with
  | zero => intro δ hδ _; exact hb k hk δ hδ
  | succ r' ih =>
    intro δ hδ hδ'
    exact hs k (r' + 1) r' (by omega) hk δ hδ hδ' (ih (δ / 4) (by positivity) (by linarith))

theorem xiExists_of (hA : ∀ k r : ℕ, 1 ≤ k → AAt k r) (hB : ∀ k r : ℕ, 1 ≤ k → BAt k r (1 / 2))
    (hC : CoefStep) (hX : XiIntStep) : XiExists := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA'
  obtain ⟨eS, heS, hBs⟩ := hB k r D.k_pos
  have he0 : 0 < min eS (1 / 10 : ℝ) := lt_min heS (by norm_num)
  have adm : SAdm k r (fun l => s0 k r l - min eS (1 / 10)) := fun l => by
    simp only [sub_sub_cancel]; exact ⟨he0, min_le_right _ _⟩
  have adm' : ∀ l, 0 < s0 k r l - (s0 k r l - min eS (1 / 10)) ∧ s0 k r l - (s0 k r l - min eS (1 / 10)) ≤ eS :=
    fun l => by simp only [sub_sub_cancel]; exact ⟨he0, min_le_left _ _⟩
  exact ⟨xiN k r _, hC k r Wp Wq D A _ adm hA' (hA k r D.k_pos _ adm D.μG D.haarG A hA'),
    hX k r Wp Wq D _ adm (hBs _ adm' D.z D.z_mem D.T_pos D.μN D.haarN)
      (hBs _ adm' D.z' D.z'_mem D.T'_pos D.μN D.haarN)⟩

theorem xiExists_of_induction_steps (hAb : AStepBase) (hAs : AStepSucc) (hBb : BStepBase) (hBs : BStepSucc)
    (hC : CoefStep) (hX : XiIntStep) : XiExists :=
  xiExists_of (aAll_of hAb hAs) (fun k r hk => bAll_of hBb hBs k r hk (1 / 2) (by norm_num) le_rfl) hC hX

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace subgroupData

def qv (c : Fin 3 → ℂ) (t : ℝ) : ℂ := c 0 + c 1 * t + c 2 * t ^ 2

lemma qv_cont (c : Fin 3 → ℂ) : Continuous (qv c) := by
  unfold qv; fun_prop

lemma term_bd {z : ℂ} {w d la W D : ℝ} (hz : ‖z‖ ≤ la) (hw : |w| ≤ W) (hD : 0 < D) (hd : D ≤ |d|) :
    ‖z * (w : ℂ) / (d : ℂ)‖ ≤ la * W / D := by
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hW : 0 ≤ W := (abs_nonneg _).trans hw
  rw [div_le_div_iff₀ (by linarith) hD]
  have hla : 0 ≤ la := (norm_nonneg _).trans hz
  exact mul_le_mul (mul_le_mul hz hw (abs_nonneg _) hla) hd hD.le (by positivity)

lemma lagrange (c : Fin 3 → ℂ) {t1 t2 t3 g la : ℝ} (hg : 0 < g) (h1 : 1 ≤ t1) (h3 : t3 ≤ 2)
    (h12 : g ≤ t2 - t1) (h23 : g ≤ t3 - t2)
    (p1 : ‖qv c t1‖ ≤ la) (p2 : ‖qv c t2‖ ≤ la) (p3 : ‖qv c t3‖ ≤ la) :
    ‖c‖ ≤ 12 * la / g ^ 2 := by
  have hla : 0 ≤ la := (norm_nonneg _).trans p1
  have d1 : g ^ 2 ≤ |(t1 - t2) * (t1 - t3)| := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have d2 : g ^ 2 ≤ |(t2 - t1) * (t2 - t3)| := by
    rw [abs_of_nonpos (by nlinarith)]; nlinarith
  have d3 : g ^ 2 ≤ |(t3 - t1) * (t3 - t2)| := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hg2 : 0 < g ^ 2 := by positivity
  have n1 : ((t1 - t2) * (t1 - t3) : ℂ) ≠ 0 := by
    have : (t1 - t2) * (t1 - t3) ≠ 0 := by intro h; rw [h, abs_zero] at d1; linarith
    exact_mod_cast this
  have n2 : ((t2 - t1) * (t2 - t3) : ℂ) ≠ 0 := by
    have : (t2 - t1) * (t2 - t3) ≠ 0 := by intro h; rw [h, abs_zero] at d2; linarith
    exact_mod_cast this
  have n3 : ((t3 - t1) * (t3 - t2) : ℂ) ≠ 0 := by
    have : (t3 - t1) * (t3 - t2) ≠ 0 := by intro h; rw [h, abs_zero] at d3; linarith
    exact_mod_cast this
  have a12 : (t1 : ℂ) - t2 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a13 : (t1 : ℂ) - t3 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a23 : (t2 : ℂ) - t3 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a21 : (t2 : ℂ) - t1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a31 : (t3 : ℂ) - t1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have a32 : (t3 : ℂ) - t2 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := Complex.ofReal_injective h; linarith
  have key : ∀ (w1 w2 w3 : ℝ), |w1| ≤ 4 → |w2| ≤ 4 → |w3| ≤ 4 →
      ‖qv c t1 * (w1 : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ) + qv c t2 * (w2 : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * (w3 : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ)‖ ≤ 12 * la / g ^ 2 := by
    intro w1 w2 w3 hw1 hw2 hw3
    refine (norm_add₃_le).trans ?_
    have := term_bd p1 hw1 hg2 d1
    have := term_bd p2 hw2 hg2 d2
    have := term_bd p3 hw3 hg2 d3
    have e : 12 * la / g ^ 2 = la * 4 / g ^ 2 + la * 4 / g ^ 2 + la * 4 / g ^ 2 := by ring
    linarith
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · have := key (t2 * t3) (t1 * t3) (t1 * t2) (by rw [abs_of_nonneg (by nlinarith)]; nlinarith)
      (by rw [abs_of_nonneg (by nlinarith)]; nlinarith) (by rw [abs_of_nonneg (by nlinarith)]; nlinarith)
    have e : c 0 = qv c t1 * ((t2 * t3 : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((t1 * t3 : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((t1 * t2 : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 0‖ ≤ _
    rw [e]; exact this
  · have := key (-(t2 + t3)) (-(t1 + t3)) (-(t1 + t2)) (by rw [abs_le]; constructor <;> nlinarith)
      (by rw [abs_le]; constructor <;> nlinarith) (by rw [abs_le]; constructor <;> nlinarith)
    have e : c 1 = qv c t1 * ((-(t2 + t3) : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((-(t1 + t3) : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((-(t1 + t2) : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 1‖ ≤ _
    rw [e]; exact this
  · have := key 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    have e : c 2 = qv c t1 * ((1 : ℝ) : ℂ) / (((t1 - t2) * (t1 - t3) : ℝ) : ℂ)
        + qv c t2 * ((1 : ℝ) : ℂ) / (((t2 - t1) * (t2 - t3) : ℝ) : ℂ)
        + qv c t3 * ((1 : ℝ) : ℂ) / (((t3 - t1) * (t3 - t2) : ℝ) : ℂ) := by
      simp only [qv]; push_cast; field_simp; ring
    show ‖c 2‖ ≤ _
    rw [e]; exact this

lemma E_closed (c : Fin 3 → ℂ) (la : ℝ) : IsClosed {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} :=
  isClosed_Icc.inter (isClosed_le (continuous_norm.comp (qv_cont c)) continuous_const)

lemma sublevel (c : Fin 3 → ℂ) {la g : ℝ} (hg : 0 < g)
    (hno : ∀ t1 t2 t3 : ℝ, 1 ≤ t1 → t3 ≤ 2 → g ≤ t2 - t1 → g ≤ t3 - t2 → ‖qv c t1‖ ≤ la →
      ‖qv c t2‖ ≤ la → ‖qv c t3‖ ≤ la → False) :
    volume {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} ≤ ENNReal.ofReal (2 * g) := by
  set E := {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} with hE
  have hcl : IsClosed E := E_closed c la
  have hbdd : BddBelow E := ⟨1, fun t ht => ht.1.1⟩
  rcases E.eq_empty_or_nonempty with h0 | hne
  · rw [h0, measure_empty]; exact bot_le
  set t1 := sInf E with ht1d
  have ht1 : t1 ∈ E := hcl.csInf_mem hne hbdd
  have hge1 : ∀ t ∈ E, t1 ≤ t := fun t ht => csInf_le hbdd ht
  set E2 := E ∩ Ici (t1 + g) with hE2
  rcases E2.eq_empty_or_nonempty with h2 | hne2
  · have hsub : E ⊆ Icc t1 (t1 + g) := by
      intro t ht
      refine ⟨hge1 t ht, ?_⟩
      by_contra hc
      have : t ∈ E2 := ⟨ht, le_of_lt (not_le.mp hc)⟩
      rw [h2] at this; exact this
    calc volume E ≤ volume (Icc t1 (t1 + g)) := measure_mono hsub
      _ = ENNReal.ofReal g := by rw [Real.volume_Icc]; ring_nf
      _ ≤ ENNReal.ofReal (2 * g) := ENNReal.ofReal_le_ofReal (by linarith)
  have hcl2 : IsClosed E2 := hcl.inter isClosed_Ici
  have hbdd2 : BddBelow E2 := ⟨1, fun t ht => ht.1.1.1⟩
  set t2 := sInf E2 with ht2d
  have ht2 : t2 ∈ E2 := hcl2.csInf_mem hne2 hbdd2
  have hge2 : ∀ t ∈ E2, t2 ≤ t := fun t ht => csInf_le hbdd2 ht
  have h12 : t1 + g ≤ t2 := Set.mem_Ici.mp ht2.2
  have hsub : E ⊆ Icc t1 (t1 + g) ∪ Icc t2 (t2 + g) := by
    intro t ht
    by_cases h : t < t1 + g
    · exact Or.inl ⟨hge1 t ht, h.le⟩
    · have htE2 : t ∈ E2 := ⟨ht, not_lt.mp h⟩
      refine Or.inr ⟨hge2 t htE2, ?_⟩
      by_contra hc
      exact hno t1 t2 t ht1.1.1 ht.1.2 (by linarith) (by linarith [not_le.mp hc]) ht1.2 ht2.1.2 ht.2
  calc volume E ≤ volume (Icc t1 (t1 + g) ∪ Icc t2 (t2 + g)) := measure_mono hsub
    _ ≤ volume (Icc t1 (t1 + g)) + volume (Icc t2 (t2 + g)) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * g) := by
        rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf

end subgroupData

open subgroupData in
theorem quadraticSublevelDecay' : SUB := by
  intro δ hδ0 hδ1
  refine ⟨22, ?_⟩
  intro c
  set M := ‖c‖ with hMd
  have hM0 : 0 ≤ M := norm_nonneg _
  have hint : ∀ t : ℝ, (1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ) ≤ 1 := fun t =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (c 0 + c 1 * t + c 2 * t ^ 2)])
      (by linarith)
  by_cases hM : M ≤ 1
  · calc (∫⁻ t in Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)))
        ≤ ∫⁻ t in Icc (1:ℝ) 2, 1 :=
          setLIntegral_mono' measurableSet_Icc (fun t _ => ENNReal.ofReal_le_one.mpr (hint t))
      _ = 1 := by rw [setLIntegral_const, Real.volume_Icc]; norm_num
      _ ≤ ENNReal.ofReal (22 * (1 + M) ^ (-δ / 2)) := by
          rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
          have : (2:ℝ) ^ (-1:ℝ) ≤ (1 + M) ^ (-δ / 2) := by
            calc (2:ℝ) ^ (-1:ℝ) ≤ 2 ^ (-δ / 2) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ ≤ (1 + M) ^ (-δ / 2) := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
          have h2 : (2:ℝ) ^ (-1:ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
          linarith
  push Not at hM
  set s := M ^ ((1:ℝ) / 4) with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s ^ 4 = M := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hs1 : 1 < s := by
    by_contra h; push Not at h
    have : s ^ 4 ≤ 1 := pow_le_one₀ hs0.le h
    linarith
  set E := {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ s ^ 2} with hE
  have hvol : volume E ≤ ENNReal.ofReal (2 * (5 / s)) := by
    apply sublevel c (by positivity)
    intro t1 t2 t3 h1 h3 h12 h23 p1 p2 p3
    have hl := lagrange c (by positivity) h1 h3 h12 h23 p1 p2 p3
    have e : 12 * s ^ 2 / (5 / s) ^ 2 = 12 * s ^ 4 / 25 := by field_simp; ring
    rw [e, hs4] at hl
    linarith
  have hEm : MeasurableSet E := (E_closed c _).measurableSet
  set K := (1 + s ^ 2) ^ (-δ) with hK
  have pw : ∀ t ∈ Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) ≤
      E.indicator 1 t + ENNReal.ofReal K := by
    intro t ht
    by_cases hp : ‖qv c t‖ ≤ s ^ 2
    · have htE : t ∈ E := ⟨ht, hp⟩
      rw [indicator_of_mem htE]
      exact le_trans (ENNReal.ofReal_le_one.mpr (hint t)) le_self_add
    · refine le_trans ?_ le_add_self
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by
        have : s ^ 2 < ‖qv c t‖ := not_le.mp hp
        simp only [qv] at this; linarith) (by linarith)
  have hfin : 2 * (5 / s) + K ≤ 22 * (1 + M) ^ (-δ / 2) := by
    have hA : K ≤ (1 + M) ^ (-δ / 2) := by
      have e : K = ((1 + s ^ 2) ^ 2) ^ (-δ / 2) := by
        rw [hK, ← Real.rpow_natCast (1 + s ^ 2) 2, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by rw [← hs4]; nlinarith) (by linarith)
    have hB : 1 / (2 * s) ≤ (1 + M) ^ (-δ / 2) := by
      calc 1 / (2 * s) ≤ (1 + s)⁻¹ := by
            rw [one_div]; exact inv_anti₀ (by positivity) (by linarith)
        _ = ((1 + s) ^ 4) ^ (-(1:ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one]; norm_num
        _ ≤ (1 + M) ^ (-(1:ℝ) / 4) := by
            apply Real.rpow_le_rpow_of_nonpos (by linarith) _ (by norm_num)
            rw [← hs4]; nlinarith [pow_pos hs0 3]
        _ ≤ (1 + M) ^ (-δ / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e2 : 2 * (5 / s) = 20 * (1 / (2 * s)) := by field_simp; ring
    have hX : 0 ≤ (1 + M) ^ (-δ / 2) := by positivity
    rw [e2]; linarith
  calc (∫⁻ t in Icc (1:ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)))
      ≤ ∫⁻ t in Icc (1:ℝ) 2, (E.indicator 1 t + ENNReal.ofReal K) := setLIntegral_mono' measurableSet_Icc pw
    _ = (∫⁻ t in Icc (1:ℝ) 2, E.indicator 1 t) + ∫⁻ _ in Icc (1:ℝ) 2, ENNReal.ofReal K :=
        lintegral_add_right _ measurable_const
    _ ≤ volume E + ENNReal.ofReal K := by
        gcongr
        · calc (∫⁻ t in Icc (1:ℝ) 2, E.indicator 1 t) ≤ ∫⁻ t, E.indicator 1 t := setLIntegral_le_lintegral _ _
            _ = volume E := lintegral_indicator_one hEm
        · rw [setLIntegral_const, Real.volume_Icc]; norm_num
    _ ≤ ENNReal.ofReal (2 * (5 / s)) + ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (2 * (5 / s) + K) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (22 * (1 + M) ^ (-δ / 2)) := ENNReal.ofReal_le_ofReal hfin
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace PolynomialGrowthIntegrals

lemma int_pos_rpow {R κ : ℝ} (hR : 0 < R) (hκ : κ < 1) :
    ∫⁻ β in Ioc 0 R, ENNReal.ofReal (β ^ (-κ)) = ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
  have hr : (-1 : ℝ) < -κ := by linarith
  have hint : IntegrableOn (fun β : ℝ => β ^ (-κ)) (Ioc 0 R) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1 (intervalIntegral.intervalIntegrable_rpow' hr)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] fun β : ℝ => β ^ (-κ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg hx.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl hr)]
  have h1 : -κ + 1 = 1 - κ := by ring
  rw [h1, Real.zero_rpow (by linarith), sub_zero]

lemma int_abs_rpow {R κ : ℝ} (hR : 0 < R) (hκ0 : 0 < κ) (hκ : κ < 1) :
    ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ)) ≤ 2 * ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
  have hpos : ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) =
      ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, ← int_pos_rpow hR hκ]
    exact setLIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [abs_of_pos hx.1]
  have hneg : ∫⁻ β in Icc (-R) 0, ENNReal.ofReal (|β| ^ (-κ)) =
      ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (measurableSet_Icc (a := (0 : ℝ)) (b := R))
      (f := fun β : ℝ => ENNReal.ofReal (|β| ^ (-κ))) (by fun_prop)
    have hs : Neg.neg ⁻¹' Icc (0 : ℝ) R = Icc (-R) 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
    simp only [abs_neg] at h
    rw [hs] at h
    exact h
  calc ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ))
      ≤ (∫⁻ β in Icc (-R) 0, ENNReal.ofReal (|β| ^ (-κ))) +
          ∫⁻ β in Icc 0 R, ENNReal.ofReal (|β| ^ (-κ)) := by
        rw [← Icc_union_Icc_eq_Icc (by linarith : -R ≤ 0) hR.le]
        exact lintegral_union_le _ _ _
    _ = 2 * ENNReal.ofReal (R ^ (1 - κ) / (1 - κ)) := by rw [hneg, hpos, two_mul]

lemma fac_le {A b t β β' R : ℝ} (hR : 0 < R) (hA : R ≤ A) (ht : 0 ≤ t) (hβ : |β| ≤ R)
    (hβ' : |β'| ≤ R) :
    (A ^ 2 + (β - b) ^ 2) ^ (-t / 2) ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) := by
  have hA0 : 0 < A := lt_of_lt_of_le hR hA
  have hx : 0 < A ^ 2 + (β - b) ^ 2 := by positivity
  have hy : 0 < A ^ 2 + (β' - b) ^ 2 := by positivity
  have h1 := abs_le.1 hβ
  have h2 := abs_le.1 hβ'
  have hd : (β' - β) ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have h9 : A ^ 2 + (β' - b) ^ 2 ≤ 9 * (A ^ 2 + (β - b) ^ 2) := by
    nlinarith [sq_nonneg ((β' - β) - (β - b))]
  calc (A ^ 2 + (β - b) ^ 2) ^ (-t / 2)
      = 3 ^ t * (9 * (A ^ 2 + (β - b) ^ 2)) ^ (-t / 2) := by
        rw [Real.mul_rpow (by norm_num) hx.le, show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num), ← mul_assoc, ← Real.rpow_add (by norm_num)]
        have h0 : t + 2 * (-t / 2) = 0 := by ring
        rw [h0, Real.rpow_zero, one_mul]
    _ ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hy h9 (by linarith)) (by positivity)

lemma slowWeight_le {n : ℕ} {t A b : Fin n → ℝ} {R β β' : ℝ} (hR : 0 < R) (ht : ∀ i, 0 ≤ t i)
    (hA : ∀ i, R ≤ A i) (hβ : |β| ≤ R) (hβ' : |β'| ≤ R) :
    slowly t A b β ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * slowly t A b β' := by
  unfold slowly
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun i _ => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (fac_le hR (hA i) (ht i) hβ hβ')

lemma measurable_slowWeight {n : ℕ} (t A b : Fin n → ℝ) : Measurable (slowly t A b) := by
  unfold slowly
  fun_prop

end PolynomialGrowthIntegrals

open PolynomialGrowthIntegrals in
theorem slowWeightBound' : SLOW := by
  intro n T κ hκ0 hκ1
  refine ⟨3 ^ T / (1 - κ) + 1, fun t A b R hR ht hT hA => ?_⟩
  set f := slowly t A b with hf_def
  set I := ∫⁻ β, f β with hI
  have hfm : Measurable f := measurable_slowWeight t A b
  have hw : Measurable fun β : ℝ => ENNReal.ofReal (|β| ^ (-κ)) := by fun_prop
  set c : ℝ := 3 ^ (∑ i, t i) / (2 * R) with hc
  set q : ℝ := R ^ (1 - κ) / (1 - κ) with hq

  have hcen : ∀ β ∈ Icc (-R) R, f β ≤ ENNReal.ofReal c * I := by
    intro β hβ
    have hb : |β| ≤ R := abs_le.2 ⟨hβ.1, hβ.2⟩
    have key : f β * ENNReal.ofReal (2 * R) ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I := by
      calc f β * ENNReal.ofReal (2 * R) = ∫⁻ _ in Icc (-R) R, f β := by
            rw [setLIntegral_const, Real.volume_Icc]; congr 2; ring
        _ ≤ ∫⁻ β' in Icc (-R) R, ENNReal.ofReal (3 ^ ∑ i, t i) * f β' :=
            setLIntegral_mono (measurable_const.mul hfm) fun β' hβ' =>
              slowWeight_le hR ht hA hb (abs_le.2 ⟨hβ'.1, hβ'.2⟩)
        _ = ENNReal.ofReal (3 ^ ∑ i, t i) * ∫⁻ β' in Icc (-R) R, f β' := lintegral_const_mul _ hfm
        _ ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I := by gcongr; exact setLIntegral_le_lintegral _ _
    have hinv : ENNReal.ofReal (2 * R) * ENNReal.ofReal (1 / (2 * R)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel (by positivity), ENNReal.ofReal_one]
    calc f β = f β * ENNReal.ofReal (2 * R) * ENNReal.ofReal (1 / (2 * R)) := by
          rw [mul_assoc, hinv, mul_one]
      _ ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * I * ENNReal.ofReal (1 / (2 * R)) := by gcongr
      _ = ENNReal.ofReal c * I := by
          rw [hc, div_eq_mul_one_div (3 ^ ∑ i, t i), ENNReal.ofReal_mul (by positivity)]; ring

  have hA1 : ∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ)) ≤
      ENNReal.ofReal (c * (2 * q)) * I := by
    calc ∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ))
        ≤ ∫⁻ β in Icc (-R) R, ENNReal.ofReal c * I * ENNReal.ofReal (|β| ^ (-κ)) :=
          setLIntegral_mono (measurable_const.mul hw) fun β hβ => by gcongr; exact hcen β hβ
      _ = ENNReal.ofReal c * I * ∫⁻ β in Icc (-R) R, ENNReal.ofReal (|β| ^ (-κ)) :=
          lintegral_const_mul _ hw
      _ ≤ ENNReal.ofReal c * I * (2 * ENNReal.ofReal q) :=
          by gcongr; exact int_abs_rpow hR hκ0 hκ1
      _ = ENNReal.ofReal (c * (2 * q)) * I := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          try ring

  have hA2 : ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ)) ≤ ENNReal.ofReal (R ^ (-κ)) * I := by
    calc ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ))
        ≤ ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (R ^ (-κ)) := by
          refine setLIntegral_mono (hfm.mul measurable_const) fun β hβ => ?_
          have hb : R < |β| := by
            by_contra h
            exact hβ (abs_le.1 (not_lt.1 h))
          gcongr f β * ?_
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hR hb.le (by linarith))
      _ = (∫⁻ β in (Icc (-R) R)ᶜ, f β) * ENNReal.ofReal (R ^ (-κ)) := lintegral_mul_const _ hfm
      _ ≤ I * ENNReal.ofReal (R ^ (-κ)) := by gcongr; exact setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (R ^ (-κ)) * I := mul_comm _ _

  have hRk : R ^ (1 - κ) = R * R ^ (-κ) := by
    rw [show 1 - κ = 1 + -κ by ring, Real.rpow_add hR, Real.rpow_one]
  have hcq : c * (2 * q) = 3 ^ (∑ i, t i) * R ^ (-κ) / (1 - κ) := by
    rw [hc, hq, hRk]
    have : (1 - κ) ≠ 0 := by linarith
    field_simp
    try ring
  have hsT : (3 : ℝ) ^ (∑ i, t i) ≤ 3 ^ T := Real.rpow_le_rpow_of_exponent_le (by norm_num) hT
  have hRp : 0 < R ^ (-κ) := Real.rpow_pos_of_pos hR _
  have hreal : c * (2 * q) + R ^ (-κ) ≤ (3 ^ T / (1 - κ) + 1) * R ^ (-κ) := by
    rw [hcq, add_mul, one_mul, div_mul_eq_mul_div]
    gcongr
    try linarith
  calc ∫⁻ β, slowly t A b β * ENNReal.ofReal (|β| ^ (-κ))
      = (∫⁻ β in Icc (-R) R, f β * ENNReal.ofReal (|β| ^ (-κ))) +
          ∫⁻ β in (Icc (-R) R)ᶜ, f β * ENNReal.ofReal (|β| ^ (-κ)) :=
        (lintegral_add_compl (fun β => f β * ENNReal.ofReal (|β| ^ (-κ))) measurableSet_Icc).symm
    _ ≤ ENNReal.ofReal (c * (2 * q)) * I + ENNReal.ofReal (R ^ (-κ)) * I := add_le_add hA1 hA2
    _ = ENNReal.ofReal (c * (2 * q) + R ^ (-κ)) * I := by
        rw [ENNReal.ofReal_add (by positivity) hRp.le, add_mul]
    _ ≤ ENNReal.ofReal ((3 ^ T / (1 - κ) + 1) * R ^ (-κ)) * I :=
        by gcongr
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
open MeasureTheory Set
open scoped ENNReal Real

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals

theorem lintegral_radial (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, g ‖x‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 • g ‖Complex.polarCoord.symm p‖ =
        (fun r : ℝ => ENNReal.ofReal r * g r) p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
    intro p hp
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul, mul_one]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) h1,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal r * g r) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      ((ENNReal.measurable_ofReal.mul hg).aemeasurable) aemeasurable_const]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, one_mul]
  rw [show π - -π = 2 * π by ring, mul_comm]

theorem lintegral_Ioc_rpow (a ρ : ℝ) (ha : a < 2) (hρ : 0 < ρ) :
    ∫⁻ r in Ioc (0 : ℝ) ρ, ENNReal.ofReal (r ^ (1 - a)) = ENNReal.ofReal (ρ ^ (2 - a) / (2 - a)) := by
  have hr : -1 < 1 - a := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal ((intervalIntegral.intervalIntegrable_rpow' hr).1)
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => Real.rpow_nonneg hr.1.le _)),
    ← intervalIntegral.integral_of_le hρ.le, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith)]
  congr 1
  rw [show 1 - a + 1 = 2 - a by ring, sub_zero]

theorem lintegral_Ioi_rpow (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ r in Ioi ρ, ENNReal.ofReal (r ^ (1 - b)) = ENNReal.ofReal (ρ ^ (2 - b) / (b - 2)) := by
  have hr : 1 - b < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr hρ)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => Real.rpow_nonneg (hρ.trans hr).le _)),
    integral_Ioi_rpow_of_lt hr hρ]
  congr 1
  rw [show 1 - b + 1 = 2 - b by ring, show b - 2 = -(2 - b) by ring, div_neg, neg_div]

theorem lintegral_disc (a ρ : ℝ) (ha : a < 2) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-a))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - a) / (2 - a))) := by
  have hm : Measurable ((Iic ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-a)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iic
  rw [lintegral_radial _ hm]
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Iic ρ).indicator
      (fun r => ENNReal.ofReal (r ^ (-a))) r = (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) r := by
    intro r hr
    by_cases h : r ∈ Iic ρ
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (le_of_lt hr),
        sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi, lintegral_Ioc_rpow a ρ ha hρ,
    ← ENNReal.ofReal_mul (by positivity)]

theorem lintegral_outside (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-b))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - b) / (b - 2))) := by
  have hm : Measurable ((Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-b)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ioi
  rw [lintegral_radial _ hm]
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Ioi ρ).indicator
      (fun r => ENNReal.ofReal (r ^ (-b))) r = (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (1 - b))) r := by
    intro r hr
    by_cases h : r ∈ Ioi ρ
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (le_of_lt hr),
        sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hρ.le,
    lintegral_Ioi_rpow b ρ hb hρ, ← ENNReal.ofReal_mul (by positivity)]

theorem ker_pointwise (e γ : ℝ) (he : 0 < e) (heγ : e < γ) (hγ : γ < 2) (c : ℂ) (D ρ : ℝ) (hρ : 0 < ρ)
    (hρc : ‖c‖ ≤ 2 * ρ) (hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2) (x : ℂ) (hx0 : x ≠ 0) (hxc : x ≠ c) :
    ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ)) ≤
      ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
          (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
        ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
          (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ +
        ENNReal.ofReal (ρ ^ (-γ)) *
          (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ := by
  have hE : -1 + e / 2 ≤ 0 := by linarith
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hm : 0 < ‖x - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hxc)
  have t1 : ‖c‖ - ‖x‖ ≤ ‖x - c‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le c x
  have t2 : ‖x‖ - ‖c‖ ≤ ‖x - c‖ := norm_sub_norm_le x c
  have t3 : ‖x - c‖ ≤ ‖x‖ + ‖c‖ := norm_sub_le x c
  rcases le_or_gt ‖x‖ ρ with hA | hA
  · have hle : ρ ^ 2 ≤ ‖x - c‖ ^ 2 + D ^ 2 := by
      rcases le_or_gt ‖c‖ ρ with h | h
      · nlinarith [norm_nonneg c, sq_nonneg ‖x - c‖, mul_le_mul h h (norm_nonneg c) hρ.le]
      · have h' : ‖c‖ - ρ ≤ ‖x - c‖ := by linarith
        nlinarith [mul_le_mul h' h' (by linarith) (norm_nonneg _), mul_le_mul_of_nonneg_left hρc hρ.le]
    refine le_add_right (le_add_right ?_)
    rw [indicator_of_mem (show ‖x‖ ∈ Iic ρ from hA)]
    exact mul_le_mul'
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) hle hE)) le_rfl
  rcases le_or_gt (2 * ‖c‖) ‖x‖ with hB | hB
  · refine le_add_right (le_add_left ?_)
    rw [indicator_of_mem (show ‖x‖ ∈ Ioi ρ from hA)]
    have h' : ‖x‖ / 2 ≤ ‖x - c‖ := by linarith
    have hle : ‖x‖ ^ 2 / 4 ≤ ‖x - c‖ ^ 2 + D ^ 2 := by
      nlinarith [mul_le_mul h' h' (by positivity) (norm_nonneg _), sq_nonneg D]
    have hid : (‖x‖ ^ 2 / 4) ^ (-1 + e / 2) * ‖x‖ ^ (-γ) =
        (4 : ℝ) ^ (-(-1 + e / 2)) * ‖x‖ ^ (-(2 + γ - e)) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_two, ← Real.rpow_mul hn.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      have h2 : ‖x‖ ^ (2 * (-1 + e / 2)) * ‖x‖ ^ (-γ) = ‖x‖ ^ (-(2 + γ - e)) := by
        rw [← Real.rpow_add hn]; congr 1; ring
      rw [← h2, div_eq_mul_inv]; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hid]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by positivity) hle hE) (by positivity))
  · refine le_add_left ?_
    have h6 : ‖x - c‖ ≤ 6 * ρ := by linarith
    rw [indicator_of_mem (show ‖x - c‖ ∈ Iic (6 * ρ) from h6)]
    have hid : (‖x - c‖ ^ 2) ^ (-1 + e / 2) = ‖x - c‖ ^ (-(2 - e)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hm.le]; congr 1; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hid,
      mul_comm (ρ ^ (-γ))]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul
      (Real.rpow_le_rpow_of_nonpos (pow_pos hm 2) (le_add_of_nonneg_right (sq_nonneg D)) hE)
      (Real.rpow_le_rpow_of_nonpos hρ hA.le (by linarith)) (by positivity) (by positivity)

end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open RadialKernelIntegrals

theorem planarKernelBound' : KER := by
  intro e γ he heγ hγ
  set A : ℝ := 2 * π / (2 - γ) + (4 : ℝ) ^ (-(-1 + e / 2)) * (2 * π / (γ - e)) +
    (6 : ℝ) ^ e * (2 * π / e) with hA
  refine ⟨A / (4 : ℝ) ^ (-(γ - e) / 2), fun c D hD => ?_⟩
  have hS : 0 < ‖c‖ ^ 2 + D ^ 2 := by positivity
  set ρ : ℝ := Real.sqrt (‖c‖ ^ 2 + D ^ 2) / 2 with hρdef
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.2 hS) two_pos
  have hρ2 : ρ ^ 2 = (‖c‖ ^ 2 + D ^ 2) / 4 := by
    rw [hρdef, div_pow, Real.sq_sqrt hS.le]; norm_num
  have hρc : ‖c‖ ≤ 2 * ρ := by
    have : ‖c‖ ≤ Real.sqrt (‖c‖ ^ 2 + D ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg D])
    rw [hρdef]; linarith
  have hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2 := by rw [hρ2]; ring
  have hS4 : ‖c‖ ^ 2 + D ^ 2 = 4 * ρ ^ 2 := by rw [hρ2]; ring
  have hae : ∀ᵐ x : ℂ, x ≠ 0 ∧ x ≠ c := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ)),
      compl_mem_ae_iff.2 (measure_singleton c)] with x h0 hc
    exact ⟨h0, hc⟩
  refine (lintegral_mono_ae (hae.mono fun x hx =>
    ker_pointwise e γ he heγ hγ c D ρ hρ hρc hDρ x hx.1 hx.2)).trans ?_
  have hm1 : Measurable ((Iic ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iic
  have hm2 : Measurable ((Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-(2 + γ - e))))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ioi
  have hF1 : Measurable fun x : ℂ => ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
      (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ :=
    (hm1.comp measurable_norm).const_mul _
  have hF2 : Measurable fun x : ℂ => ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ :=
    (hm2.comp measurable_norm).const_mul _
  have hF12 : Measurable fun x : ℂ => ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
      (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
      ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ := hF1.add hF2
  have h3 : ∫⁻ x : ℂ, (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ =
      ∫⁻ x : ℂ, (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x‖ :=
    lintegral_sub_right_eq_self
      (fun y : ℂ => (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖y‖) c
  have hI1 : 0 ≤ 2 * π * (ρ ^ (2 - γ) / (2 - γ)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hI2 : 0 ≤ 2 * π * (ρ ^ (2 - (2 + γ - e)) / (2 + γ - e - 2)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hI3 : 0 ≤ 2 * π * ((6 * ρ) ^ (2 - (2 - e)) / (2 - (2 - e))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  rw [lintegral_add_left hF12, lintegral_add_left hF1,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h3,
    lintegral_disc γ ρ hγ hρ, lintegral_outside (2 + γ - e) ρ (by linarith) hρ,
    lintegral_disc (2 - e) (6 * ρ) (by linarith) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) hI1) (mul_nonneg (by positivity) hI2),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by positivity) hI1)
      (mul_nonneg (by positivity) hI2)) (mul_nonneg (by positivity) hI3)]
  apply ENNReal.ofReal_le_ofReal
  have hP1 : (ρ ^ 2) ^ (-1 + e / 2) * ρ ^ (2 - γ) = ρ ^ (e - γ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]; congr 1; ring
  have hP2 : ρ ^ (2 - (2 + γ - e)) = ρ ^ (e - γ) := by congr 1; ring
  have hP3 : ρ ^ (-γ) * (6 * ρ) ^ e = (6 : ℝ) ^ e * ρ ^ (e - γ) := by
    have h : ρ ^ (-γ) * ρ ^ e = ρ ^ (e - γ) := by rw [← Real.rpow_add hρ]; congr 1; ring
    rw [Real.mul_rpow (by norm_num) hρ.le, ← h]; ring
  have hS' : (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e) / 2) = (4 : ℝ) ^ (-(γ - e) / 2) * ρ ^ (e - γ) := by
    rw [hS4, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_two,
      ← Real.rpow_mul hρ.le]
    congr 2; ring
  have hne : (4 : ℝ) ^ (-(γ - e) / 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [hS', hP2, show (2 : ℝ) + γ - e - 2 = γ - e by ring, show (2 : ℝ) - (2 - e) = e by ring]
  refine le_of_eq ?_
  calc _ = A * ρ ^ (e - γ) := by
        rw [hA]; linear_combination (2 * π / (2 - γ)) * hP1 + (2 * π / e) * hP3
    _ = _ := by field_simp

end ReciprocityTheory.ChartRestriction.DS.Xi
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem sub : SUB := quadraticSublevelDecay'

theorem ker : KER := planarKernelBound'

theorem slow : SLOW := slowWeightBound'

end ReciprocityTheory.ChartRestriction.DS.Xi
end

section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Base0

private def PhiA (k : ℕ) (A : ℝ) (g : Mt k 0) : ℝ≥0∞ := ENNReal.ofReal (gN (Matrix.of g) ^ (-A))

private lemma phiA_ne_top (k : ℕ) (A : ℝ) (g : Mt k 0) : PhiA k A g ≠ ∞ := ENNReal.ofReal_ne_top

private lemma measurable_phiA (k : ℕ) (A : ℝ) : Measurable (PhiA k A) := by
  have hc : Continuous fun g : Mt k 0 => gN (Matrix.of g) := by
    unfold gN
    apply Continuous.sqrt
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  unfold PhiA
  exact ENNReal.measurable_ofReal.comp (hc.measurable.pow_const (-A))

private def Gf (k : ℕ) (σ : ℝ) (h g h' : Mt k 0) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt 2)⁻¹ * ‖((Matrix.of h)ᴴ *ᵥ ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0)) (iW k) +
    ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)

set_option maxHeartbeats 800000 in

private lemma measurable_Gf (k : ℕ) (σ : ℝ) :
    Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => Gf k σ p.1 p.2.1 p.2.2) := by
  have hof : Continuous (fun M : Mt k 0 => (Matrix.of M : Mat k 0)) := continuous_id
  have h1 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.1 := hof.comp continuous_fst
  have h21 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.1 :=
    hof.comp (continuous_fst.comp continuous_snd)
  have h22 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.2 :=
    hof.comp (continuous_snd.comp continuous_snd)
  have hw : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0 :=
    (h21.matrix_mul h22).matrix_mulVec continuous_const
  have hv : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) :=
    h1.matrix_conjTranspose.matrix_mulVec hw
  have hc : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) +
        ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖ :=
    continuous_const.mul ((((continuous_apply (iW k)).comp hv).add ((continuous_apply (iK k)).comp hw)).norm)
  have hm : Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => ENNReal.ofReal
      ((Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) +
        ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)) :=
    (ENNReal.measurable_ofReal.comp hc.measurable).pow_const (-σ)
  unfold Gf
  exact hm

private lemma s_facts {k : ℕ} (hk : 1 ≤ k) {s : Fin (0 + 1) → ℝ} (hs : SAdm k 0 s) :
    0 ≤ s 0 ∧ s 0 < k := by
  have h := hs 0
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp [s0] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> linarith

private lemma nsq_tr_lemma {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

private lemma gN_left_lemma_2 {k r : ℕ} {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  apply Complex.ofReal_injective
  rw [nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

private lemma gN_right_lemma_3 {k r : ℕ} {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (X * κ) = gN X := by
  have hκ' : κ * κᴴ = 1 := by
    first
      | exact mul_eq_one_comm.mp hκ
      | exact (Matrix.mul_eq_one_comm).1 hκ
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hκ
  unfold gN
  congr 1
  apply Complex.ofReal_injective
  rw [nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc, hκ', Matrix.mul_one]

private lemma phiA_inv (k : ℕ) (A : ℝ) : ∀ κ ∈ Kset k 0, ∀ g,
    PhiA k A (lmulM κ g) = PhiA k A g ∧ PhiA k A (rmulF κ g) = PhiA k A g := by
  intro κ hκ g
  have hu : κᴴ * κ = 1 := by
    simp only [Kset, Set.mem_setOf_eq] at hκ
    exact hκ.2
  refine ⟨?_, ?_⟩
  · simp only [PhiA, lmulM]
    exact congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_left_lemma_2 hu (Matrix.of g))
  · simp only [PhiA, rmulF]
    exact congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_right_lemma_3 hu (Matrix.of g))

private lemma avg_one {k : ℕ} (hk : 1 ≤ k) (hT : TBoth) {s : Fin (0 + 1) → ℝ} {μG : Measure (Mt k 0)}
    (hμG : IsHaarOn (GV k 0) μG) (A : ℝ) {h h' : Mat k 0} (hh : h ∈ U0 k) (hh' : h' ∈ U0 k) :
    ∫⁻ g, PhiA k A g * FsE k 0 s (h⁻¹ * Matrix.of g * h') ∂μG = JInt μG A s := by
  rw [hT k 0 s μG (PhiA k A) hk hμG (measurable_phiA k A) (phiA_inv k A) h hh.1 h' hh'.1, sphericalFunction_fixedUnitary_eq_one hk hh,
    sphericalFunction_fixedUnitary_eq_one hk hh', mul_one, ENNReal.ofReal_one, one_mul]
  rfl

private lemma measurable_haarKernelTriple (k : ℕ) (A σ : ℝ) :
    Measurable (fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k σ q.2 q.1.2 q.1.1) := by
  have hs : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => q.1.2 := measurable_snd.comp measurable_fst
  have h1 := (measurable_phiA k A).comp hs
  have hm : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => (q.2, q.1.2, q.1.1) := by fun_prop
  have h2 := (measurable_Gf k σ).comp hm
  simp only [Function.comp_def] at h1 h2
  exact h1.mul h2

private lemma avg_key {k : ℕ} (hk : 1 ≤ k) (hT : TBoth) {s : Fin (0 + 1) → ℝ} {μG : Measure (Mt k 0)}
    (hμG : IsHaarOn (GV k 0) μG) (A : ℝ) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν)
    [IsFiniteMeasure ν] [SigmaFinite μG] :
    JInt μG A s * (ν Set.univ * ν Set.univ) =
      ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG := by
  have step1 : JInt μG A s * (ν Set.univ * ν Set.univ) = ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν := by
    rw [lintegral_const, lintegral_const, mul_assoc]
  have step2 : ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν =
      ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_fixedUnitary hν] with h hh
    rw [← avg_one hk hT hμG A hh hh']
    refine lintegral_congr (fun g => ?_)
    rw [fsE_avg hk hh]
    rfl
  have step3 : ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν =
      ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν := by
    refine lintegral_congr (fun h' => ?_)
    have hmap : Measurable (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1)) :=
      (measurable_const.prodMk measurable_snd).prodMk measurable_fst
    have hm : Measurable ((fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k (s 0) q.2 q.1.2 q.1.1) ∘
        (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1))) := Measurable.comp (measurable_haarKernelTriple k A (s 0)) hmap
    exact lintegral_lintegral_swap hm.aemeasurable
  have step4 : ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν =
      ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG :=
    lintegral_lintegral_swap (Measurable.lintegral_prod_right' (measurable_haarKernelTriple k A (s 0))).aemeasurable
  have step5 : ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG =
      ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG := by
    refine lintegral_congr (fun g => ?_)
    rw [← lintegral_const_mul' _ _ (phiA_ne_top k A g)]
    refine lintegral_congr (fun h' => ?_)
    rw [lintegral_const_mul' _ _ (phiA_ne_top k A g)]
  rw [step1, step2, step3, step4, step5]

private lemma ptw {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 ≤ σ) {ν : Measure (Mt k 0)}
    (hν : IsHaarOn (U0 k) ν) (hK1f : C0 k σ ν + ν Set.univ ≠ ∞) (g : Mt k 0)
    (hg : (Matrix.of g : Mat k 0) ∈ GV k 0) :
    ∫⁻ h', ∫⁻ h, Gf k σ h g h' ∂ν ∂ν ≤
      (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := by
  have hc2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hws := outer_ws hg
  have hgkk : 1 ≤ ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖ := by
    have h1 : 1 ≤ Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k)) := by
      nlinarith [sq_nonneg (tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))]
    rw [← Complex.sq_norm] at h1
    nlinarith [norm_nonneg ((Matrix.of g : Mat k 0) (iK k) (iK k))]
  have hbn : ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ = ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖ := by
    rw [norm_neg, norm_star]
  have hb0 : -star ((Matrix.of g : Mat k 0) (iK k) (iK k)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hbn; linarith
  have hvb : tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)) ^ 2 ≤
      Complex.normSq (-star ((Matrix.of g : Mat k 0) (iK k) (iK k))) := by
    have : Complex.normSq (star ((Matrix.of g : Mat k 0) (iK k) (iK k))) =
        Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k)) := Complex.normSq_conj _
    rw [Complex.normSq_neg, this]; linarith
  calc ∫⁻ h', ∫⁻ h, Gf k σ h g h' ∂ν ∂ν
      ≤ ∫⁻ h', ENNReal.ofReal ((Real.sqrt 2)⁻¹ *
          ‖((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖ / 2) ^ (-σ) *
            (C0 k σ ν + ν Set.univ) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
        obtain ⟨e, hne⟩ := iso_y hk hg hh'.1
        unfold Gf
        exact bnd hk hν hσ (lam := (Real.sqrt 2)⁻¹) (by positivity)
          ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) _ hne (le_of_eq e)
    _ = (∫⁻ h', ENNReal.ofReal (1 / 4 * ‖((Matrix.of h')ᴴ *ᵥ (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))
          (iW k) + -star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖) ^ (-σ) ∂ν) * (C0 k σ ν + ν Set.univ) := by
        rw [lintegral_mul_const' _ _ hK1f]
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
        rw [outer_eq hk hh' (Matrix.of g)]
        congr 2
        rw [← mul_assoc, hc2]; ring
    _ ≤ (ENNReal.ofReal (1 / 4 * ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ / 2) ^ (-σ) *
          (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) :=
        mul_le_mul' (bnd hk hν hσ (by norm_num) _ _ hb0 hvb) le_rfl
    _ ≤ (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) :=
        mul_le_mul' (mul_le_mul' (ofReal_rpow_neg_anti hσ (by rw [hbn]; linarith)) le_rfl) le_rfl
    _ = (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := mul_comm _ _

theorem aStepBase_of (hB2 : InductiveHeisenbergInputs) (hT : TBoth) : AStepBase := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, hGN, -, -, -, -, -, -, -, -, hHW, -⟩ := hB2
  intro k hk s hs μG hμG A hA
  obtain ⟨hσ0, hσk⟩ := s_facts hk hs
  obtain ⟨ν, hν⟩ := hHW k 0 (bvec (iK k)) (inWb_iK k) (Tz_iK k)
  have hν' : IsHaarOn (U0 k) ν := hν
  have hνf := haar_univ_lt_top hCW hν'
  have hν0 : ν Set.univ ≠ 0 := fun h => hν.ne_zero (Measure.measure_univ_eq_zero.mp h)
  have : IsFiniteMeasure ν := ⟨hνf⟩
  have : IsFiniteMeasureOnCompacts μG := ⟨fun K hK => hμG.finite_compact K hK⟩
  have hC0 := haarIntegralConstant_lt_top hk hν' hνf hσ0 hσk
  have hK1f : C0 k (s 0) ν + ν Set.univ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC0.ne, hνf.ne⟩
  have hKc : (C0 k (s 0) ν + ν Set.univ) *
      (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ)) ≠ ∞ := by
    refine ENNReal.mul_ne_top hK1f (ENNReal.mul_ne_top ?_ hK1f)
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]; exact ENNReal.ofReal_ne_top
  have key := avg_key hk hT (s := s) hμG A hν'
  have hfin : ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG < ∞ := by
    calc ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG
        ≤ ∫⁻ g, PhiA k A g * ((C0 k (s 0) ν + ν Set.univ) *
            (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) ∂μG := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμG.conc] with g hg
          exact mul_le_mul' le_rfl (ptw hk hσ0 hν' hK1f g (not_not.mp hg))
      _ = (∫⁻ g, PhiA k A g ∂μG) * ((C0 k (s 0) ν + ν Set.univ) *
            (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) :=
          lintegral_mul_const' _ _ hKc
      _ < ∞ := ENNReal.mul_lt_top (hGN k 0 μG A hμG hA) hKc.lt_top
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_mul (mul_ne_zero hν0 hν0)] at key
  rw [← key] at hfin
  exact lt_irrefl _ hfin

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem xiExists_of_in (h : InductiveHeisenbergInputs) : Formalism.FourierDecayAlt.B.XiExists :=
  xiExists_of_induction_steps (aStepBase_of h (tBothH iwB h))
    (aStepSucc_of h iwB (tLeftH iwB h) FormulaFAux.formulaF_all (ch_of c1))
    (bStepBase_of h)
    (bStepSucc_of h iwB FormulaFAux.formulaF_all
      (oscillatoryBound' (tailFin_of (ch_of c1)) c1 quadraticSublevelDecay' ker slow))
    (coefStep_of h (tBothH iwB h) (det_of h)) (xiIntH h)

theorem xiExists : Formalism.FourierDecayAlt.B.XiExists := xiExists_of_in heisenbergHaarFacts_hold

end ReciprocityTheory.ChartRestriction.DS.Xi
end
