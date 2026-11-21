import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightDiff
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

namespace LelongWeightDiff

variable {n d : ℕ}

theorem abs_half_log_sub_le {a ε κ : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hκ : 0 < κ) :
    |Real.log (a + ε * κ ^ 2) / 2 - Real.log (a + ε) / 2| ≤ |Real.log κ| := by
  have hb : 0 < a + ε := by linarith
  have hc : 0 < a + ε * κ ^ 2 := by positivity
  have hk2 : Real.log (κ ^ 2) = 2 * Real.log κ := by rw [Real.log_pow]; norm_num
  rcases le_total 1 κ with h1 | h1
  · have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ h1
    have l1 : Real.log (a + ε) ≤ Real.log (a + ε * κ ^ 2) := Real.log_le_log hb (by nlinarith)
    have l2 : Real.log (a + ε * κ ^ 2) ≤ Real.log (κ ^ 2) + Real.log (a + ε) := by
      rw [← Real.log_mul (by positivity) hb.ne']; exact Real.log_le_log hc (by nlinarith)
    rw [abs_of_nonneg (Real.log_nonneg h1), abs_le]; constructor <;> linarith
  · have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ hκ.le h1
    have l1 : Real.log (a + ε * κ ^ 2) ≤ Real.log (a + ε) := Real.log_le_log hc (by nlinarith)
    have l2 : Real.log (κ ^ 2) + Real.log (a + ε) ≤ Real.log (a + ε * κ ^ 2) := by
      rw [← Real.log_mul (by positivity) hb.ne']; exact Real.log_le_log (by positivity) (by nlinarith)
    rw [abs_of_nonpos (Real.log_nonpos hκ.le h1), abs_le]; constructor <;> linarith

theorem exists_poly_of_linEval_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (u : Fin n → ℂ) (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ x ∈ zeroSet J, linEval u x = 0 → eval (A *ᵥ x) P = 0 := by
  classical
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  have hs0 : Ideal.Quotient.mk J (linForm u) ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hex : ∃ m, ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g.Monic ∧ g.natDegree = m ∧
      Polynomial.aeval (Ideal.Quotient.mk J (linForm u)) g = 0 := by
    obtain ⟨g, hgm, -, hg⟩ := FibreBound.exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (linForm u))
    exact ⟨_, g, hgm, rfl, hg⟩
  obtain ⟨g, hgm, hgd, hg⟩ := Nat.find_spec hex
  have hc : g.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hgm
    rw [map_mul, Polynomial.aeval_X] at hg
    refine Nat.find_min hex (m := q.natDegree) ?_ ⟨q, hqm, rfl, (mul_eq_zero.mp hg).resolve_left hs0⟩
    rw [← hgd, Polynomial.natDegree_mul Polynomial.X_ne_zero hqm.ne_zero, Polynomial.natDegree_X]
    omega
  refine ⟨g.coeff 0, hc, fun x hx hux => ?_⟩
  have hmem : Polynomial.eval₂ (pullback A).toRingHom (linForm u) g ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
    rw [Polynomial.aeval_def] at hg
    exact hg
  have h0 := hx _ hmem
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A *ᵥ x) :=
    RingHom.ext fun P => FibreBound.eval_pullback A x P
  have hl : eval x (linForm u) = linEval u x := by simp [linForm, linEval]
  rwa [Polynomial.hom_eval₂, hcomp, hl, hux, Polynomial.eval₂_at_zero] at h0

theorem measurable_chartDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hf : ContinuousOn f (zeroSet J)) (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i)) :
    Measurable (chartDens J A f ψ) := by
  classical
  rw [CutOffDominated.chartDens_congr_zeroSet (g := (zeroSet J).piecewise f 0)
    (fun x hx => (Set.piecewise_eq_of_mem _ _ _ hx).symm)]
  exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA
    (hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet) hψ).1

theorem abs_chartDens_le {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |chartDens J A f ψ y| ≤ chartAbsDens J A f ψ y := by
  classical
  unfold chartDens chartAbsDens
  simp only [CutOffDominated.sheetSum_eq_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs <;> simp

theorem chartDens_sub {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (f f' : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    chartDens J A f ψ y - chartDens J A f' ψ y = chartDens J A (fun x => f x - f' x) ψ y := by
  classical
  unfold chartDens
  simp only [CutOffDominated.sheetSum_eq_sum _ hfin, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem tendsto_finset_sum_zero {ι α : Type*} {l : Filter α} (s : Finset ι) (f : ι → α → ℝ)
    (h : ∀ i ∈ s, Tendsto (f i) l (𝓝 0)) : Tendsto (fun a => ∑ i ∈ s, f i a) l (𝓝 0) := by
  simpa using tendsto_finsetSum s h

end LelongWeightDiff

end GroundTheory.Heights₂.Heights.Targets
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongWeightDiff.proof (hM : ChartMassCompact.Statement) : LelongWeightDiff.Statement := by
  classical
  intro n d J u g k φ hJ hdim hu hg hgc hφ hk hkpos
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons g φ i) := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (⟨Set.univ, isOpen_univ, Set.subset_univ _, hg.contDiffOn⟩ : SmoothNear (zeroSet J) g)
    · simpa using hφ j
  have hcs : ∃ i, HasCompactSupport (vecCons g φ i) := ⟨0, by simpa using hgc⟩
  by_cases hA : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · simp only [varInt, dif_neg hA, sub_self]; exact tendsto_const_nhds
  simp only [varInt, dif_pos hA]
  set A := hA.choose
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
  have hkc : ContinuousOn k (zeroSet J) := by
    obtain ⟨U, -, hU, hkU⟩ := hk; exact hkU.continuousOn.mono hU
  have hlc : Continuous fun x => ‖linEval u x‖ ^ 2 := ((contDiff_linEval u).continuous.norm).pow 2
  set D : ℝ → (Fin n → ℂ) → ℝ := fun ε x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2 - logReg u ε x
  have hWc : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (zeroSet J) := fun ε hε =>
    ((hlc.continuousOn.add (continuousOn_const.mul (hkc.pow 2))).log fun x hx => by
      exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hε (pow_pos (hkpos x hx) 2))).ne').div_const 2
  have hLc : ∀ ε : ℝ, 0 < ε → ContinuousOn (logReg u ε) (zeroSet J) := fun ε hε =>
    (contDiff_logReg u hε).continuous.continuousOn
  have hint : ∀ f, ContinuousOn f (zeroSet J) → Integrable (chartDens J A f (vecCons g φ)) := fun f hf =>
    (hM n (d + 1) J A f _ hJ hdim hAf hf hψ (Or.inr hcs)).mono'
      (LelongWeightDiff.measurable_chartDens hJ hdim hAf hf hψ).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact LelongWeightDiff.abs_chartDens_le _ _ (hfin y))
  have heq : (fun ε : ℝ => ∫ y, chartDens J A (D ε) (vecCons g φ) y) =ᶠ[𝓝[>] 0]
      fun ε => chartInt J A (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (vecCons g φ) -
        chartInt J A (logReg u ε) (vecCons g φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [chartInt, chartInt, ← integral_sub (hint _ (hWc ε hε)) (hint _ (hLc ε hε))]
    exact integral_congr_ae (Eventually.of_forall fun y =>
      (LelongWeightDiff.chartDens_sub _ _ _ (hfin y)).symm)
  refine Tendsto.congr' heq ?_
  obtain ⟨P, hP0, hPu⟩ := LelongWeightDiff.exists_poly_of_linEval_eq_zero J A hAf u hu
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε => chartDens J A (D ε) (vecCons g φ)) (f := fun _ => (0 : ℝ))
    (chartAbsDens J A (fun x => Real.log (k x)) (vecCons g φ)) ?_ ?_
    (hM n (d + 1) J A _ _ hJ hdim hAf (hkc.log fun x hx => (hkpos x hx).ne') hψ (Or.inr hcs)) ?_
  · rwa [integral_zero] at h
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (LelongWeightDiff.measurable_chartDens hJ hdim hAf ((hWc ε hε).sub (hLc ε hε)) hψ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs
    · rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (LelongWeightDiff.abs_half_log_sub_le (sq_nonneg _) hε (hkpos x hx.1)) (abs_nonneg _)
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP0] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine LelongWeightDiff.tendsto_finset_sum_zero _ _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    swap
    · simp only [dif_neg hs]; exact tendsto_const_nhds
    simp only [dif_pos hs]
    have hux : linEval u x ≠ 0 := fun h0 => hy (by rw [← hx.2]; exact hPu x hx.1 h0)
    have ha : 0 < ‖linEval u x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hux) 2
    have hc : ContinuousAt (fun ε : ℝ => D ε x) 0 := by
      simp only [D, logReg]
      refine ((ContinuousAt.log (by fun_prop) ?_).div_const 2).sub
        ((ContinuousAt.log (by fun_prop) ?_).div_const 2) <;> simp [hux]
    have h0 : D 0 x = 0 := by simp [D, logReg]
    simpa [h0] using ((hc.tendsto.mono_left nhdsWithin_le_nhds).mul_const
      (ReciprocityTheory.AnForm.maDens (fun i => vecCons g φ i ∘ hs.choose) y))

end GroundTheory.Heights₂.Heights.Targets
end
end
