import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramPositiveVolumeContinuous
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MaximalCompactSubgroupProperties
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import BuildAid.ForwardExisting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryOfGramEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevMulVecOutside
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.KsetTransitive

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B GlobalTheory.HCXi

noncomputable section

namespace GlobalTheory.HCXi

theorem blockEmb_conjTranspose (k i r' : ℕ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    (ιLev k i r' g)ᴴ = ιLev k i r' gᴴ := by
  rw [PI.QnLevBasicsW.ιLev_eq, PI.QnLevBasicsW.ιLev_eq, conjTranspose_submatrix, fromBlocks_conjTranspose]
  simp

theorem blockEmb_mem_Kset : ∀ k r' : ℕ, ∀ y ∈ Kset k r', ιLev k 1 r' y ∈ Kset k (1 + r') := by
  intro k r' y hy
  refine ⟨PI.QnLevBasicsW.level_group_unitary_hermitian k 1 r' y hy.1, ?_⟩
  rw [blockEmb_conjTranspose, ← (PI.QnLevBasicsW.level_group_homomorphism k 1 r').2, hy.2]
  exact (PI.QnLevBasicsW.level_group_homomorphism k 1 r').1

end GlobalTheory.HCXi
end
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_compact_subgroup_properties : ∀ k r : ℕ, IsClosedSubgroup (Kset k r) ∧ IsCompact (Kset k r) ∧ Hpk k r ∈ Kset k r ∧ (∀ κ ∈ Kset k r, κᴴ ∈ Kset k r ∧ κ * Hpk k r = Hpk k r * κ) ∧ ∀ κ ∈ Kset k r, ∀ κ' ∈ Kset k r, ∀ g : Mat k r, gN (κ * g * κ') = gN g := by
  first | exact @GlobalTheory.HCXi.KGroup.kset_facts | exact GlobalTheory.HCXi.KGroup.kset_facts | (intros; apply GlobalTheory.HCXi.KGroup.kset_facts <;> assumption)
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

theorem exists_isKMeas : ∀ k r : ℕ, ∃ μK : Measure (Mt k r), IsKMeas k r μK := by
  intro k r
  obtain ⟨hcl, hco, -⟩ := GlobalTheory.T.maximal_compact_subgroup_properties k r
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.compact_group_haar_exists k r (Kset k r) hcl hco
  have hfin : μ Set.univ < ∞ := by
    have h1 : μ Set.univ ≤ μ (Kset k r) + μ (Kset k r)ᶜ := measure_univ_le_add_compl _
    have h2 : μ (Kset k r) < ∞ := hμ.finite_compact _ hco
    rw [hμ.conc, add_zero] at h1
    exact h1.trans_lt h2
  have hne : μ Set.univ ≠ 0 := by
    intro h
    exact hμ.ne_zero (Measure.measure_univ_eq_zero.1 h)
  have hone : ((μ Set.univ)⁻¹ • μ) Set.univ = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hfin.ne]
  refine ⟨(μ Set.univ)⁻¹ • μ, ⟨?_, ?_, ?_, ?_, ?_⟩, hone⟩
  · rw [Measure.smul_apply, hμ.conc, smul_zero]
  · intro a ha
    rw [Measure.map_smul, hμ.left a ha]
  · intro a ha
    rw [Measure.map_smul, hμ.right a ha]
  · intro K _
    calc _ ≤ ((μ Set.univ)⁻¹ • μ) Set.univ := measure_mono (Set.subset_univ _)
      _ < ∞ := by rw [hone]; exact ENNReal.one_lt_top
  · intro h
    rw [h] at hone
    simp at hone

end GlobalTheory.HCXi
end

section
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.ConePolar

theorem angle_shift (h : ℝ → ℝ≥0∞) (hp : Function.Periodic h (2 * Real.pi)) :
    ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, h θ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), h θ := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hp.lift
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0 hp.lift
  simp only [Function.Periodic.lift_coe] at h1 h2
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, h1, h2]

theorem radial (a : ℝ) (ha : 0 ≤ a) (F H : ℝ → ℝ≥0∞) :
    ∫⁻ ρ in Set.Ioi (Real.sqrt a), ENNReal.ofReal ρ * (F (ρ ^ 2 - a) * H ρ)
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * H (Real.sqrt (a + τ)) := by
  have himg : (fun ρ : ℝ => ρ ^ 2 - a) '' Set.Ioi (Real.sqrt a) = Set.Ioi 0 := by
    ext τ
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have h0 := Real.sqrt_nonneg a
      have h1 := Real.sq_sqrt ha
      nlinarith
    · intro hτ
      refine ⟨Real.sqrt (a + τ), Real.sqrt_lt_sqrt ha (by linarith), ?_⟩
      rw [Real.sq_sqrt (by linarith)]; ring
  have hinj : Set.InjOn (fun ρ : ℝ => ρ ^ 2 - a) (Set.Ioi (Real.sqrt a)) := by
    intro x hx y hy hxy
    have h0 := Real.sqrt_nonneg a
    simp only [Set.mem_Ioi] at hx hy
    have : x ^ 2 = y ^ 2 := by simpa using hxy
    exact (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 this
  have hder : ∀ x ∈ Set.Ioi (Real.sqrt a), HasDerivWithinAt (fun ρ : ℝ => ρ ^ 2 - a) (2 * x)
      (Set.Ioi (Real.sqrt a)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).sub_const a).hasDerivWithinAt (s := Set.Ioi (Real.sqrt a))
    simpa using this
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj,
    ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 ≤ x := (Real.sqrt_nonneg a).trans (le_of_lt hx)
  rw [show a + (x ^ 2 - a) = x ^ 2 by ring, Real.sqrt_sq hx0, abs_of_nonneg (by positivity),
    ENNReal.ofReal_mul (by norm_num), ← mul_assoc (1 / 2 : ℝ≥0∞), ← mul_assoc (1 / 2 : ℝ≥0∞)]
  have : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal 2 = 1 := by
    rw [ENNReal.ofReal_ofNat, one_div, ENNReal.inv_mul_cancel (by simp) (by simp)]
  rw [this, one_mul]

theorem plane (a : ℝ) (ha : 0 ≤ a) (F : ℝ → ℝ≥0∞) (g : ℂ → ℝ≥0∞) (hF : Measurable F) (hg : Measurable g) :
    ∫⁻ z : ℂ, Set.indicator {z : ℂ | a < Complex.normSq z} (fun z => F (Complex.normSq z - a) * g z) z
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((Real.sqrt (a + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ))) := by
  rw [← radial a ha F (fun ρ => ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
          g (((ρ : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))),
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (Complex.I * p.2) := by
    intro p
    rw [Complex.polarCoord_symm_apply, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  have hn : ∀ ρ θ : ℝ, Complex.normSq ((ρ : ℂ) * Complex.exp (Complex.I * θ)) = ρ ^ 2 := by
    intro ρ θ
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hm : Measurable (Set.indicator {z : ℂ | a < Complex.normSq z}
      (fun z => F (Complex.normSq z - a) * g z)) := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.continuous_normSq.measurable)
    exact (hF.comp (Complex.continuous_normSq.measurable.sub_const a)).mul hg
  simp only [hsymm, smul_eq_mul]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  swap
  · refine Measurable.aemeasurable ?_
    refine (measurable_fst.ennreal_ofReal).mul (hm.comp ?_)
    fun_prop
  have hsub : Set.Ioi (Real.sqrt a) = Set.Ioi (Real.sqrt a) ∩ Set.Ioi (0 : ℝ) := by
    rw [Set.Ioi_inter_Ioi, max_eq_left (Real.sqrt_nonneg a)]
  rw [hsub, ← Measure.restrict_restrict measurableSet_Ioi,
    ← lintegral_indicator (s := Set.Ioi (Real.sqrt a)) measurableSet_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : 0 < ρ := hρ
  simp only [Set.indicator, Set.mem_setOf_eq, hn, Set.mem_Ioi, Real.sqrt_lt' hρ0]
  split_ifs with h
  · have hmg : Measurable fun θ : ℝ => g ((ρ : ℂ) * Complex.exp (Complex.I * θ)) :=
      hg.comp (by fun_prop)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul _ hmg, angle_shift]
    intro θ
    simp only
    congr 2
    push_cast
    rw [mul_add, Complex.exp_add, mul_comm Complex.I (2 * _), Complex.exp_two_pi_mul_I, mul_one]
  · simp

theorem measurable_snoc (k : ℕ) :
    Measurable fun q : (Fin k → ℂ) × ℂ => (Fin.snoc (α := fun _ => ℂ) q.1 q.2 : Fin (k + 1) → ℂ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]; fun_prop

theorem measurable_sqLen (k : ℕ) : Measurable (sqLen : (Fin k → ℂ) → ℝ) := by
  unfold sqLen
  exact Finset.measurable_sum _ fun i _ => Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)

theorem lintegral_snoc (k : ℕ) (f : (Fin (k + 1) → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v = ∫⁻ w : Fin k → ℂ, ∫⁻ z : ℂ, f (Fin.snoc (α := fun _ => ℂ) w z) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) (Fin.last k)).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod,
    lintegral_prod_symm' _ (by exact hf.comp (MeasurableEquiv.measurable _))]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

end GlobalTheory.HCXi.ConePolar

namespace GlobalTheory.HCXi
open ConePolar

theorem lintegral_cone_polar : ∀ (k : ℕ) (ψ : (Fin (k + 1) → ℂ) → ℝ≥0∞) (F : ℝ → ℝ≥0∞), Measurable ψ → Measurable F → (∫⁻ v : Fin (k + 1) → ℂ in {v | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}, F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ : ℝ in Set.Ioi 0, F τ * ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))) := by
  intro k ψ F hψ hF
  have hinit : Measurable fun v : Fin (k + 1) → ℂ => sqLen (Fin.init v : Fin k → ℂ) :=
    (measurable_sqLen k).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  have hlast : Measurable fun v : Fin (k + 1) → ℂ => Complex.normSq (v (Fin.last k)) :=
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)
  have hS := measurableSet_lt hinit hlast
  rw [← lintegral_indicator hS, lintegral_snoc k _
    (by exact Measurable.indicator ((hF.comp (hlast.sub hinit)).mul hψ) hS)]
  have h1 : ∀ w : Fin k → ℂ, (∫⁻ z : ℂ, Set.indicator
      {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}
      (fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v)
      (Fin.snoc (α := fun _ => ℂ) w z)) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ),
        F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) w
          (((Real.sqrt (sqLen w + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))) := by
    intro w
    rw [← plane (sqLen w) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) F
      (fun z => ψ (Fin.snoc (α := fun _ => ℂ) w z)) hF
      (hψ.comp ((measurable_snoc k).comp measurable_prodMk_left))]
    refine lintegral_congr fun z => ?_
    simp [Set.indicator]
  simp only [h1]
  have hG : Measurable fun q : ((Fin k → ℂ) × ℝ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1.1
      (((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : ((Fin k → ℂ) × ℝ) × ℝ =>
      (q.1.1, ((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH := hG.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  rw [lintegral_const_mul' _ _ (by simp), lintegral_lintegral_swap
    (by exact ((hF.comp measurable_snd).mul hH).aemeasurable)]
  congr 1
  refine lintegral_congr fun τ => ?_
  have hG' : Measurable fun q : (Fin k → ℂ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1
      (((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : (Fin k → ℂ) × ℝ =>
      (q.1, ((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH' := hG'.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  simp only at hH'
  rw [lintegral_const_mul _ hH', Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hG'.aemeasurable]

end GlobalTheory.HCXi
end

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_hyperboloid_fibration : ∀ (k : ℕ) (ψ : (Fin (k + 1) → ℂ) → ℝ≥0∞) (F : ℝ → ℝ≥0∞), Measurable ψ → Measurable F → (∫⁻ v : Fin (k + 1) → ℂ in {v | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}, F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ : ℝ in Set.Ioi 0, F τ * ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))) := by
  atlas_forward_decl GlobalTheory.HCXi.lintegral_cone_polar
end

section
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.ConeSlice

noncomputable abbrev sgnMat (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1)

noncomputable abbrev pt {k : ℕ} (τ : ℝ) (p : (Fin k → ℂ) × ℝ) : Fin (k + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))

theorem continuous_sqLen {n : ℕ} : Continuous (sqLen : (Fin n → ℂ) → ℝ) := by
  unfold sqLen
  exact continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

theorem form_eq {k : ℕ} (v : Fin (k + 1) → ℂ) :
    star v ⬝ᵥ (sgnMat k *ᵥ v) =
      ((sqLen (Fin.init v : Fin k → ℂ) - Complex.normSq (v (Fin.last k)) : ℝ) : ℂ) := by
  simp only [dotProduct, sgnMat, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, sqLen, Fin.init,
    Pi.star_apply, Fin.castSucc_ne_last, if_false, if_true, one_mul]
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

theorem form_inv {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) (v : Fin (k + 1) → ℂ) :
    Complex.normSq ((g *ᵥ v) (Fin.last k)) - sqLen (Fin.init (g *ᵥ v) : Fin k → ℂ) =
      Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ) := by
  have h : star (g *ᵥ v) ⬝ᵥ (sgnMat k *ᵥ (g *ᵥ v)) = star v ⬝ᵥ (sgnMat k *ᵥ v) := by
    conv_rhs => rw [← hg]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [form_eq, form_eq, Complex.ofReal_inj] at h
  linarith

theorem normSq_det {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) : Complex.normSq g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hD : (sgnMat k).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs <;> simp
  have h2 : (Complex.normSq g.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    apply mul_left_cancel₀ hD
    rw [mul_one]
    rw [Complex.star_def] at h
    linear_combination h
  exact_mod_cast h2

theorem continuous_mulVec {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun v : Fin n → ℂ => g *ᵥ v) :=
  (Matrix.toLin' g).continuous_of_finiteDimensional

theorem measurePreserving_mulVec {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Complex.normSq g.det = 1) :
    MeasurePreserving (fun v : Fin n → ℂ => g *ᵥ v) volume volume := by
  have hdet : LinearMap.det ((Matrix.toLin' g).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hg]
  refine ⟨(continuous_mulVec g).measurable, ?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ))
    (f := (Matrix.toLin' g).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

theorem exists_lower {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g.det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * sqLen v ≤ sqLen (g *ᵥ v) := by
  set L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' g⁻¹)
  refine ⟨((n * ‖L‖ ^ 2) + 1)⁻¹, by positivity, fun v => ?_⟩
  have h0 : ∀ u : Fin n → ℂ, 0 ≤ sqLen u := fun u =>
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h1 : ∀ u : Fin n → ℂ, sqLen u ≤ n * ‖u‖ ^ 2 := fun u => by
    calc sqLen u ≤ ∑ _i : Fin n, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [Complex.normSq_eq_norm_sq]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 2
      _ = _ := by simp
  have h2 : ∀ u : Fin n → ℂ, ‖u‖ ^ 2 ≤ sqLen u := fun u => by
    have : ‖u‖ ≤ Real.sqrt (sqLen u) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      apply Real.le_sqrt_of_sq_le
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (f := fun i => Complex.normSq (u i))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    calc ‖u‖ ^ 2 ≤ Real.sqrt (sqLen u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt (h0 u)
  have h3 : L (g *ᵥ v) = v := by
    simp [L, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g (Ne.isUnit hg)]
  have h4 : ‖v‖ ≤ ‖L‖ * ‖g *ᵥ v‖ := by
    conv_lhs => rw [← h3]
    exact L.le_opNorm _
  have h5 : ‖v‖ ^ 2 ≤ ‖L‖ ^ 2 * sqLen (g *ᵥ v) := by
    calc ‖v‖ ^ 2 ≤ (‖L‖ * ‖g *ᵥ v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
      _ = ‖L‖ ^ 2 * ‖g *ᵥ v‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h2 _) (by positivity)
  rw [inv_mul_le_iff₀ (by positivity)]
  have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (α := ℝ) n)
  have := h1 v
  have := h0 (g *ᵥ v)
  nlinarith

theorem integrable_gauss {k : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun w : Fin k → ℂ => Real.exp (-(c * sqLen w))) := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-(c * Complex.normSq z))) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ))
      (by simpa using hc) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.norm_exp, Complex.normSq_eq_norm_sq]
    congr 1
    simp [← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin k) (f := fun _ (z : ℂ) => Real.exp (-(c * Complex.normSq z)))
    (μ := fun _ => volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [sqLen, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]

theorem continuous_pt {k : ℕ} :
    Continuous (fun q : ℝ × ((Fin k → ℂ) × ℝ) => pt q.1 q.2) := by
  refine Continuous.finSnoc (by fun_prop) ?_
  have := @continuous_sqLen k
  fun_prop

theorem sqLen_le_pt {k : ℕ} (τ : ℝ) (p : (Fin k → ℂ) × ℝ) : sqLen p.1 ≤ sqLen (pt τ p) := by
  unfold sqLen
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc]
  linarith [Complex.normSq_nonneg (pt τ p (Fin.last k))]

noncomputable def slice {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi),
    ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ pt τ p)))

theorem continuous_slice {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hg : g.det ≠ 0) :
    Continuous (slice g) := by
  obtain ⟨c, hc, hle⟩ := exists_lower hg
  have hcont : Continuous (fun q : ℝ × ((Fin k → ℂ) × ℝ) =>
      ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ pt q.1 q.2)))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_sqLen.comp ((continuous_mulVec g).comp continuous_pt)).neg)
  have hint : Integrable (fun p : (Fin k → ℂ) × ℝ => Real.exp (-(c * sqLen p.1)))
      (volume.restrict (Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    exact (integrable_gauss hc).comp_fst _
  rw [continuous_iff_continuousAt]
  intro τ
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun p : (Fin k → ℂ) × ℝ => ENNReal.ofReal (Real.exp (-(c * sqLen p.1))))
    (Filter.Eventually.of_forall fun t => (hcont.comp (Continuous.prodMk_right t)).measurable)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun p => ?_)
    hint.lintegral_lt_top.ne
    (Filter.Eventually.of_forall fun p => (hcont.comp (Continuous.prodMk_left p)).continuousAt)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact (mul_le_mul_of_nonneg_left (sqLen_le_pt t p) hc.le).trans (hle _)

theorem lintegral_slice {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ τ in Set.Ioi 0, F τ * slice g τ = ∫⁻ τ in Set.Ioi 0, F τ * slice (k := k) 1 τ := by
  have hψ : Continuous (fun v : Fin (k + 1) → ℂ => ENNReal.ofReal (Real.exp (-sqLen v))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp continuous_sqLen.neg)
  have hQ : Continuous (fun v : Fin (k + 1) → ℂ =>
      Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) :=
    (Complex.continuous_normSq.comp (continuous_apply _)).sub
      (continuous_sqLen.comp (continuous_pi fun i => continuous_apply _))
  have h1 := GlobalTheory.T.lintegral_hyperboloid_fibration k _ F (hψ.comp (continuous_mulVec g)).measurable hF
  have h2 := GlobalTheory.T.lintegral_hyperboloid_fibration k _ F hψ.measurable hF
  have hset : {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}
      = {v | 0 < Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)} := by
    ext v; simp
  have hS : MeasurableSet {v : Fin (k + 1) → ℂ |
      0 < Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)} :=
    (isOpen_lt continuous_const hQ).measurableSet
  have h3 := (measurePreserving_mulVec (normSq_det hg)).setLIntegral_comp_preimage hS
    (f := fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) *
      ENNReal.ofReal (Real.exp (-sqLen v))) ((hF.comp hQ.measurable).mul hψ.measurable)
  simp only [Set.preimage_setOf_eq, form_inv hg] at h3
  rw [hset] at h1 h2
  simp only [Function.comp_apply] at h1
  rw [h3, h2] at h1
  have h4 := (ENNReal.mul_right_inj (by simp) (by simp)).1 h1
  simp only [slice, Matrix.one_mulVec]
  exact h4.symm

theorem slice_eq {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) {τ : ℝ} (hτ : 0 ≤ τ) : slice g τ = slice (k := k) 1 τ := by
  have hd : g.det ≠ 0 := fun h => by simpa [h] using normSq_det hg
  have c1 := continuous_slice hd
  have c2 := continuous_slice (k := k) (g := 1) (by simp)
  have hae : slice g =ᵐ[volume.restrict (Set.Ioi 0)] slice (k := k) 1 := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite c1.measurable c2.measurable
      fun s hs _ => ?_
    have h := lintegral_slice hg (s.indicator 1) (measurable_one.indicator hs)
    rw [← lintegral_indicator hs, ← lintegral_indicator hs]
    convert h using 2 <;> ext t <;> by_cases ht : t ∈ s <;> simp [ht]
  have h := (Measure.eqOn_open_of_ae_eq hae isOpen_Ioi c1.continuousOn c2.continuousOn).closure c1 c2
  rw [closure_Ioi] at h
  exact h hτ

theorem gaussian_slice_invariant : ∀ (k : ℕ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), gᴴ * Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) * g = Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) → ∀ τ : ℝ, 0 ≤ τ → (∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))))))) = ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2)) : Fin (k + 1) → ℂ))) := by
  intro k g hg τ hτ
  have h := slice_eq hg hτ
  simpa only [slice, Matrix.one_mulVec] using h

end GlobalTheory.HCXi.ConeSlice
end

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_gaussian_hyperboloid_fiber : ∀ (k : ℕ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), gᴴ * Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) * g = Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) → ∀ τ : ℝ, 0 ≤ τ → (∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))))))) = ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2)) : Fin (k + 1) → ℂ))) := by
  atlas_forward_decl GlobalTheory.HCXi.ConeSlice.gaussian_slice_invariant
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.ConeZero

def param (n : ℕ) (p : (Fin n → ℂ) × ℝ) : Fin (n + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) p.1
    (((Real.sqrt (sqLen p.1 + 0) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))

def coneMeasure (n : ℕ) : Measure (Fin (n + 1) → ℂ) :=
  Measure.map (param n) (volume.restrict (Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi)))

theorem continuous_sqLen (n : ℕ) : Continuous (sqLen : (Fin n → ℂ) → ℝ) := by
  unfold sqLen
  exact continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

theorem sqLen_nonneg {n : ℕ} (w : Fin n → ℂ) : 0 ≤ sqLen w :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem continuous_param (n : ℕ) : Continuous (param n) := by
  have h := continuous_sqLen n
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [param, Fin.snoc_last]
    fun_prop
  · simp only [param, Fin.snoc_castSucc]
    fun_prop

theorem normSq_param_last (n : ℕ) (p : (Fin n → ℂ) × ℝ) :
    Complex.normSq (param n p (Fin.last n)) = sqLen p.1 := by
  simp only [param, Fin.snoc_last, map_mul, add_zero, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (sqLen_nonneg _), Complex.normSq_eq_norm_sq, mul_comm Complex.I,
    Complex.norm_exp_ofReal_mul_I]
  ring

theorem sqLen_param (n : ℕ) (p : (Fin n → ℂ) × ℝ) : sqLen (param n p) = 2 * sqLen p.1 := by
  rw [sqLen, Fin.sum_univ_castSucc, normSq_param_last]
  simp only [param, Fin.snoc_castSucc]
  rw [sqLen]; ring

theorem herm_param (n : ℕ) (p : (Fin n → ℂ) × ℝ) :
    herm (Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (-1 : ℂ) else 1))
      (param n p) (param n p) = 0 := by
  have h := normSq_param_last n p
  rw [herm, dotProduct, Fin.sum_univ_castSucc]
  simp only [mulVec_diagonal, Fin.castSucc_ne_last, if_false, if_true, one_mul, Pi.star_apply,
    RCLike.star_def, neg_mul, mul_neg, ← Complex.normSq_eq_conj_mul_self, h]
  simp only [param, Fin.snoc_castSucc, sqLen]
  push_cast
  ring

theorem lintegral_cone (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ v, F (sqLen v) ∂coneMeasure n
      = (∫⁻ w : Fin n → ℂ, F (2 * sqLen w)) * ENNReal.ofReal (2 * Real.pi) := by
  have hm : Measurable fun w : Fin n → ℂ => F (2 * sqLen w) :=
    hF.comp ((continuous_sqLen n).measurable.const_mul 2)
  rw [coneMeasure, lintegral_map (f := fun v => F (sqLen v)) (hF.comp (continuous_sqLen _).measurable)
    (continuous_param n).measurable]
  simp only [sqLen_param]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun p : (Fin n → ℂ) × ℝ => F (2 * sqLen p.1)) (hm.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
    Real.volume_Ioc, sub_zero]
  rw [lintegral_mul_const _ hm]

theorem lintegral_scale (n : ℕ) (s : ℝ) (hs : 0 < s) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w : Fin n → ℂ, F (s * sqLen w)
      = ENNReal.ofReal (s ^ (-(n : ℝ))) * ∫⁻ w : Fin n → ℂ, F (sqLen w) := by
  have hm : Measurable fun w : Fin n → ℂ => F (sqLen w) := hF.comp (continuous_sqLen n).measurable
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have h1 : ∀ w : Fin n → ℂ, s * sqLen w = sqLen (Real.sqrt s • w) := by
    intro w
    simp only [sqLen, Finset.mul_sum, Pi.smul_apply, Complex.real_smul, map_mul,
      Complex.normSq_ofReal, Real.mul_self_sqrt hs.le]
  simp only [h1]
  rw [← lintegral_map hm (measurable_const_smul (Real.sqrt s)),
    Measure.map_addHaar_smul volume hr, lintegral_smul_measure, smul_eq_mul]
  congr 2
  have hd : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  rw [hd, pow_mul, Real.sq_sqrt hs.le, Real.rpow_neg hs.le, Real.rpow_natCast,
    abs_of_nonneg (by positivity)]

theorem gauss_ne_top (n : ℕ) :
    ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (Real.exp (-(2 * sqLen w))) ≠ ∞ := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-(2 * Complex.normSq z))) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 2)
      (by norm_num) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [zero_mul, add_zero, Complex.norm_exp, Complex.normSq_eq_norm_sq]
    congr 1
    rw [← Complex.ofReal_pow]
    simp [-Complex.ofReal_pow]
  have h2 : Integrable (fun w : Fin n → ℂ => ∏ i, Real.exp (-(2 * Complex.normSq (w i)))) :=
    Integrable.fintype_prod (f := fun _ z => Real.exp (-(2 * Complex.normSq z))) fun _ => h1
  have h3 : Integrable (fun w : Fin n → ℂ => Real.exp (-(2 * sqLen w))) := by
    refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [sqLen, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  exact h3.lintegral_lt_top.ne

theorem gauss_ne_zero (n : ℕ) :
    ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (Real.exp (-(2 * sqLen w))) ≠ 0 := by
  have hm : Measurable fun w : Fin n → ℂ => ENNReal.ofReal (Real.exp (-(2 * sqLen w))) := by
    have := (continuous_sqLen n).measurable
    fun_prop
  refine ((lintegral_pos_iff_support hm).2 ?_).ne'
  have : (Function.support fun w : Fin n → ℂ => ENNReal.ofReal (Real.exp (-(2 * sqLen w))))
      = Set.univ := by
    ext w
    simp [Real.exp_pos]
  rw [this]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

theorem ae_cone (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ v ∂coneMeasure n, v ≠ 0 ∧
      herm (Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (-1 : ℂ) else 1)) v v = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [coneMeasure, ae_map_iff (continuous_param n).measurable.aemeasurable]
  · refine ae_restrict_of_ae ?_
    have h0 : ∀ᵐ p : (Fin n → ℂ) × ℝ, p.1 ≠ 0 := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0 : Fin n → ℂ))
    filter_upwards [h0] with p hp
    refine ⟨fun h => hp ?_, herm_param n p⟩
    funext j
    have := congrFun h j.castSucc
    simpa [param] using this
  · refine MeasurableSet.inter (measurableSet_singleton (0 : Fin (n + 1) → ℂ)).compl ?_
    refine (isClosed_eq ?_ continuous_const).measurableSet
    unfold herm
    fun_prop

theorem Hpk_zero (k : ℕ) : Hpk k 0 = Matrix.diagonal
    (fun i : Fin (2 * 0 + k + 1) => if i = Fin.last (2 * 0 + k) then (-1 : ℂ) else 1) := by
  ext i j
  have hi := i.isLt
  by_cases h : i = j
  · subst h
    simp only [Hpk, diagonal_apply_eq, Fin.ext_iff, Fin.val_last]
    have : i.val ≤ 0 + k := by omega
    simp [show i.val ≤ k by omega]
  · simp [Hpk, h]

theorem exists_coneMeasure : ∀ k : ℕ, 1 ≤ k → ∃ m : Measure (Fin (2 * 0 + k + 1) → ℂ), SFinite m ∧ (∀ᵐ v ∂m, v ≠ 0 ∧ herm (Hpk k 0) v v = 0) ∧ (∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f → (∫⁻ v, f (s * sqLen v) ∂m) = ENNReal.ofReal (s ^ (-((2 * 0 + k : ℕ) : ℝ))) * ∫⁻ v, f (sqLen v) ∂m) ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ 0 ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ ∞ ∧ ∀ g ∈ GV k 0, (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v))) ∂m) = ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m := by
  intro k hk
  have hG : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t)) := by fun_prop
  have hpi : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    simpa using Real.pi_pos
  refine ⟨coneMeasure (2 * 0 + k), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold coneMeasure; infer_instance
  · rw [Hpk_zero]; exact ae_cone _ (by omega)
  · intro s hs f hf
    rw [lintegral_cone _ (fun t => f (s * t)) (hf.comp (measurable_const_mul s)),
      lintegral_cone _ f hf, ← mul_assoc,
      ← lintegral_scale _ s hs (fun t => f (2 * t)) (hf.comp (measurable_const_mul 2))]
    simp only [mul_left_comm s 2]
  · rw [lintegral_cone _ _ hG]
    exact mul_ne_zero (gauss_ne_zero _) hpi
  · rw [lintegral_cone _ _ hG]
    exact ENNReal.mul_ne_top (gauss_ne_top _) ENNReal.ofReal_ne_top
  · intro g hg
    have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
    rw [Hpk_zero] at hg'
    have h := GlobalTheory.T.lintegral_gaussian_hyperboloid_fiber (2 * 0 + k) g hg' 0 le_rfl
    have hs := (continuous_sqLen (2 * 0 + k + 1)).measurable
    have hm : Measurable fun v : Fin (2 * 0 + k + 1) → ℂ => g *ᵥ v :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    rw [coneMeasure, lintegral_map (f := fun v => ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v)))) (hG.comp (hs.comp hm)) (continuous_param _).measurable,
      lintegral_map (f := fun v => ENNReal.ofReal (Real.exp (-sqLen v))) (hG.comp hs) (continuous_param _).measurable]
    exact h

end GlobalTheory.HCXi.ConeZero
end
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate

noncomputable section

namespace GlobalTheory.HCXi.ConeOne

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8

def radMeas (N : ℕ) : Measure ℂ := (volume : Measure ℂ).withDensity fun c => ENNReal.ofReal (‖c‖ ^ (2 * N))

instance (N : ℕ) : SFinite (radMeas N) := by unfold radMeas; infer_instance

lemma radMeas_map (N : ℕ) (t : ℝ) (ht : 0 < t) :
    (radMeas N).map (fun c => (t : ℂ) * c) = ENNReal.ofReal ((t ^ (2 * N + 2))⁻¹) • radMeas N := by
  have hm : Measurable (fun c : ℂ => (t : ℂ) * c) := measurable_const_mul _
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hw : Measurable fun c : ℂ => ENNReal.ofReal (‖c‖ ^ (2 * N)) := by fun_prop
  rw [lintegral_map hg hm, lintegral_smul_measure]
  unfold radMeas
  have hgl : Measurable fun a : ℂ => g ((t : ℂ) * a) := hg.comp hm
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hg, lintegral_withDensity_eq_lintegral_mul _ hw hgl]
  have hmap : (volume : Measure ℂ).map (fun c => (t : ℂ) * c) = ENNReal.ofReal ((t ^ 2)⁻¹) • volume := by
    have h := Measure.map_addHaar_smul (volume : Measure ℂ) ht.ne'
    rw [Complex.finrank_real_complex, abs_of_pos (by positivity)] at h
    exact h
  have h1 := lintegral_map (μ := (volume : Measure ℂ)) (hw.mul hg) hm
  rw [hmap, lintegral_smul_measure] at h1
  have h2 : ∀ c : ℂ, ((fun c : ℂ => ENNReal.ofReal (‖c‖ ^ (2 * N))) * fun a => g ((t : ℂ) * a)) c =
      ENNReal.ofReal ((t ^ (2 * N))⁻¹) * (ENNReal.ofReal (‖(t : ℂ) * c‖ ^ (2 * N)) * g ((t : ℂ) * c)) := by
    intro c
    rw [Pi.mul_apply, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.le, mul_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  rw [lintegral_congr h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [Pi.mul_apply] at h1 ⊢
  rw [← h1, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← mul_inv, ← pow_add]

def par (k r' : ℕ) (p : ℂ × HPar k r') : Fin (2 * (1 + r') + k + 1) → ℂ :=
  p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')

lemma par_meas (k r' : ℕ) : Measurable (par k r') := by
  have : par k r' = Ψt k r' ∘ cm1Θ k r' := funext fun p => parametrisation_eq_scaled_sum p
  rw [this]
  exact Ψt_meas.comp parametrisation_map_measurable

lemma cone_def (k r' : ℕ) :
    coneMeas k r' = ((radMeas (2 * r' + k + 1)).prod (volume : Measure (HPar k r'))).map (par k r') := rfl

instance hparSFinite (k r' : ℕ) : SFinite (volume : Measure (HPar k r')) := by
  rw [Measure.volume_eq_prod]; infer_instance

lemma cone_sfinite (k r' : ℕ) : SFinite (coneMeas k r') := by
  rw [cone_def]; infer_instance

lemma cone_map (k r' : ℕ) (t : ℝ) (ht : 0 < t) :
    (coneMeas k r').map (fun v => (t : ℂ) • v) =
      ENNReal.ofReal ((t ^ (2 * (2 * r' + k + 1) + 2))⁻¹) • coneMeas k r' := by
  have hm : Measurable (fun c : ℂ => (t : ℂ) * c) := measurable_const_mul _
  have hs : Measurable (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => (t : ℂ) • v) := measurable_const_smul _
  rw [cone_def, Measure.map_map hs (par_meas k r')]
  have e : (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => (t : ℂ) • v) ∘ par k r' =
      par k r' ∘ Prod.map (fun c : ℂ => (t : ℂ) * c) id := by
    funext p
    simp only [Function.comp, par, Prod.map, id, smul_smul]
  rw [e, ← Measure.map_map (par_meas k r') (hm.prodMap measurable_id), ← Measure.map_prod_map _ _ hm measurable_id,
    radMeas_map _ t ht, Measure.map_id, Measure.prod_smul_left, Measure.map_smul]

lemma sqLen_cont {n : ℕ} : Continuous (sqLen : (Fin n → ℂ) → ℝ) := by
  unfold sqLen
  fun_prop

lemma sqLen_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ sqLen v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma sqLen_smul {n : ℕ} (t : ℝ) (v : Fin n → ℂ) : sqLen ((t : ℂ) • v) = t ^ 2 * sqLen v := by
  unfold sqLen
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, Complex.normSq_ofReal, sq]

lemma cone_homog (k r' : ℕ) (s : ℝ) (hs : 0 < s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, f (s * sqLen v) ∂(coneMeas k r')) =
      ENNReal.ofReal (s ^ (-((2 * (1 + r') + k : ℕ) : ℝ))) * ∫⁻ v, f (sqLen v) ∂(coneMeas k r') := by
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsm : Measurable (fun v : Fin (2 * (1 + r') + k + 1) → ℂ => ((Real.sqrt s : ℝ) : ℂ) • v) :=
    measurable_const_smul _
  have h1 := lintegral_map (μ := coneMeas k r') (hf.comp sqLen_cont.measurable) hsm
  rw [cone_map k r' _ ht, lintegral_smul_measure] at h1
  simp only [Function.comp, sqLen_smul, Real.sq_sqrt hs.le] at h1
  rw [← h1, smul_eq_mul]
  congr 2
  rw [Real.rpow_neg hs.le, Real.rpow_natCast,
    show 2 * (2 * r' + k + 1) + 2 = 2 * (2 * (1 + r') + k) by ring, pow_mul, Real.sq_sqrt hs.le]

lemma par_eq (k r' : ℕ) (p : ℂ × HPar k r') :
    par k r' p = p.1 • mk3 k r' (hb k r' p.2.1 p.2.2) p.2.1 1 := by
  unfold par mk3
  congr 1
  rw [one_smul]
  abel

lemma cone_ae (k r' : ℕ) : ∀ᵐ v ∂(coneMeas k r'), v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0 := by
  rw [cone_def]
  have hc : Continuous fun v : Fin (2 * (1 + r') + k + 1) → ℂ => herm (Hpk k (1 + r')) v v :=
    hermitian_quadratic_continuous (k := k) (r' := 1 + r')
  have hS : MeasurableSet {v : Fin (2 * (1 + r') + k + 1) → ℂ | v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0} :=
    (MeasurableSet.singleton 0).compl.inter (isClosed_eq hc continuous_const).measurableSet
  rw [ae_map_iff (par_meas k r').aemeasurable hS]
  have h0 : ∀ᵐ p : ℂ × HPar k r' ∂((radMeas (2 * r' + k + 1)).prod (volume : Measure (HPar k r'))), p.1 ≠ 0 := by
    rw [ae_iff]
    have : {p : ℂ × HPar k r' | ¬ p.1 ≠ 0} = {(0 : ℂ)} ×ˢ Set.univ := by
      ext p; simp
    rw [this, Measure.prod_prod]
    have h0 : radMeas (2 * r' + k + 1) {(0 : ℂ)} = 0 := by
      unfold radMeas
      exact withDensity_absolutelyContinuous _ _ (by simp)
    rw [h0, zero_mul]
  filter_upwards [h0] with p hp
  rw [par_eq]
  constructor
  · intro h
    apply hp
    have := congrArg cL h
    rw [three_block_smul, three_block_last, mul_one] at this
    exact this
  · rw [herm_smul_left, herm_smul_right, hermitian_three_block]
    have := hb_add_conj (k := k) (r' := r') p.2.1 p.2.2
    simp only [map_one, mul_one, one_mul]
    rw [this]
    simp

lemma cone_ne_zero (k r' : ℕ) : coneMeas k r' ≠ 0 := by
  intro h
  have h1 : coneMeas k r' Set.univ = 0 := by rw [h]; rfl
  rw [cone_def, Measure.map_apply (par_meas k r') MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · unfold radMeas at h1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_eq_zero_iff (by fun_prop)] at h1
    have h2 : ∀ᵐ c : ℂ, c ≠ 0 := by rw [ae_iff]; simp
    have h3 : ∀ᵐ _c : ℂ, False := by
      filter_upwards [h1, h2] with c hc hc0
      have : 0 < ‖c‖ ^ (2 * (2 * r' + k + 1)) := pow_pos (norm_pos_iff.2 hc0) _
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hc
      linarith
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h3
    exact NeZero.ne _ h3
  · rw [Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact (isOpen_univ.measure_pos (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) Set.univ_nonempty).ne' h1
    · simp at h1

lemma ball_compact {n : ℕ} : IsCompact {v : Fin n → ℂ | sqLen v ≤ 1} := by
  refine (isCompact_closedBall (0 : Fin n → ℂ) 1).of_isClosed_subset (isClosed_le sqLen_cont continuous_const) ?_
  intro v hv
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : Complex.normSq (v i) ≤ sqLen v :=
    Finset.single_le_sum (f := fun i => Complex.normSq (v i)) (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h2 : sqLen v ≤ 1 := hv
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (v i)]

lemma gauss_finite {X : Type*} [MeasurableSpace X] (m : Measure X) (q : X → ℝ) (hq : Measurable q) (h0 : ∀ v, 0 ≤ q v)
    (d : ℕ) (hh : ∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ v, f (s * q v) ∂m) = ENNReal.ofReal (s ^ (-(d : ℝ))) * ∫⁻ v, f (q v) ∂m)
    (hfin : m {v | q v ≤ 1} < ∞) : (∫⁻ v, ENNReal.ofReal (Real.exp (-q v)) ∂m) ≠ ∞ := by
  set f : ℝ → ℝ≥0∞ := (Set.Iic (1 : ℝ)).indicator 1 with hf
  have hfm : Measurable f := measurable_const.indicator measurableSet_Iic
  have hM : (∫⁻ v, f (q v) ∂m) = m {v | q v ≤ 1} := by
    rw [← lintegral_indicator_one (measurableSet_le hq measurable_const)]
    rfl
  have hle : ∀ v, ENNReal.ofReal (Real.exp (-q v)) ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v) := by
    intro v
    refine le_trans ?_ (ENNReal.le_tsum ⌊q v⌋₊)
    have h1 : ((⌊q v⌋₊ : ℝ) + 1)⁻¹ * q v ≤ 1 := by
      rw [inv_mul_le_iff₀ (by positivity), mul_one]
      exact (Nat.lt_floor_add_one _).le
    rw [hf, Set.indicator_of_mem (show _ ∈ Set.Iic (1 : ℝ) from h1), Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg (Nat.floor_le (h0 v))))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun v => ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v)) m :=
    fun n => ((hfm.comp (hq.const_mul _)).const_mul _).aemeasurable
  rw [lintegral_tsum hmeas]
  have hterm : ∀ n : ℕ, (∫⁻ v, ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v) ∂m) =
      ENNReal.ofReal (Real.exp (-(n : ℝ)) * ((n : ℝ) + 1) ^ d) * m {v | q v ≤ 1} := by
    intro n
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hh _ (by positivity) f hfm, hM, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow, inv_inv]
  simp only [hterm]
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_ne_top ?_ hfin.ne
  have hsum : Summable fun n : ℕ => Real.exp (-(n : ℝ)) * ((n : ℝ) + 1) ^ d := by
    have h1 := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul d (r := 1) one_pos)
    refine (h1.mul_left (Real.exp 1)).congr fun n => ?_
    push_cast
    rw [mul_left_comm, ← Real.exp_add, mul_comm]
    congr 2
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

end GlobalTheory.HCXi.ConeOne

namespace GlobalTheory.HCXi

open ConeOne Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8

theorem exists_cone_measure_pos_rank : ∀ k r' : ℕ, ∃ m : Measure (Fin (2 * (1 + r') + k + 1) → ℂ), SFinite m ∧ (∀ᵐ v ∂m, v ≠ 0 ∧ herm (Hpk k (1 + r')) v v = 0) ∧ (∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f → (∫⁻ v, f (s * sqLen v) ∂m) = ENNReal.ofReal (s ^ (-((2 * (1 + r') + k : ℕ) : ℝ))) * ∫⁻ v, f (sqLen v) ∂m) ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ 0 ∧ (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ ∞ ∧ ∀ g ∈ GV k (1 + r'), (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v))) ∂m) = ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m := by
  intro k r'
  have hG : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => ENNReal.ofReal (Real.exp (-sqLen v)) :=
    (Real.measurable_exp.comp sqLen_cont.measurable.neg).ennreal_ofReal
  refine ⟨coneMeas k r', cone_sfinite k r', cone_ae k r', cone_homog k r', ?_, ?_, ?_⟩
  · intro h
    rw [lintegral_eq_zero_iff hG] at h
    apply cone_ne_zero k r'
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with v hv
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hv
    exact absurd hv (not_le.2 (Real.exp_pos _))
  · exact gauss_finite _ _ sqLen_cont.measurable sqLen_nonneg _ (cone_homog k r')
      (isotropic_cone_finite_measure k r' _ ball_compact)
  · intro g hg
    have h1 := lintegral_map (μ := coneMeas k r') hG (cf_mulVec_meas g)
    rw [isotropic_cone_invariance k r' g hg] at h1
    exact h1.symm

end GlobalTheory.HCXi
end
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.Poisson

theorem unitary_comm_of_gram {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  set P : Matrix (Fin n) (Fin n) ℂ := (2⁻¹ : ℂ) • (1 + H) with hP
  have hPh : Pᴴ = P := by
    simp [hP, conjTranspose_smul, conjTranspose_add, hH]
  have hPP : P * P = P := by
    simp only [hP, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, hHH]
    module
  have hHP : H = (2 : ℂ) • P - 1 := by
    simp only [hP]
    module
  have hG : Aᴴ * P * A = Bᴴ * P * B := by
    simp only [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, h2]
  clear_value P
  have hQh : (1 - P)ᴴ = 1 - P := by simp [hPh]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, hPP, sub_self, sub_zero]
  have hG' : Aᴴ * (1 - P) * A = Bᴴ * (1 - P) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, hG]
  have key : ∀ E : Matrix (Fin n) (Fin n) ℂ, Eᴴ = E → E * E = E → Aᴴ * E * A = Bᴴ * E * B →
      ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * (E * A) = E * B := by
    intro E hE hEE hg
    have e : ∀ C : Matrix (Fin n) (Fin m) ℂ, (E * C)ᴴ * (E * C) = Cᴴ * E * C := by
      intro C
      rw [conjTranspose_mul, hE, Matrix.mul_assoc, ← Matrix.mul_assoc E E, hEE, Matrix.mul_assoc]
    refine GlobalTheory.UnitaryExtension.exists_unitary_of_gram_eq n m E (E * A) (E * B) hE hEE ?_ ?_ ?_
    · rw [← Matrix.mul_assoc, hEE]
    · rw [← Matrix.mul_assoc, hEE]
    · rw [e, e, hg]
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := key P hPh hPP hG
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := key (1 - P) hQh hQQ hG'
  rw [sub_sub_cancel] at hV3
  have hV5 : V * P = P * V := by
    have := hV2
    simp only [mul_sub, sub_mul, one_mul, mul_one] at this
    exact sub_right_injective this
  refine ⟨U * V, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hV1]
  · have : U * V * P = P * (U * V) := by
      rw [mul_assoc, hV5, ← mul_assoc, hU2, mul_assoc]
    rw [hHP]
    simp only [mul_sub, sub_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, this]
  · have hA : A = P * A + (1 - P) * A := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    have hB : B = P * B + (1 - P) * B := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    calc U * V * A = U * (V * (P * A + (1 - P) * A)) := by rw [← hA, Matrix.mul_assoc]
      _ = U * (P * A + (1 - P) * B) := by
        rw [Matrix.mul_add, hV4, ← Matrix.mul_assoc V P, hV3]
      _ = P * B + (1 - P) * B := by
        rw [Matrix.mul_add, hU4, ← Matrix.mul_assoc U (1 - P), hU3]
      _ = B := hB.symm

theorem kset_transitive_of_gram : ∀ (k r m : ℕ) (A B : Matrix (Fin (2 * r + k + 1)) (Fin m) ℂ),
    Aᴴ * A = Bᴴ * B → Aᴴ * Hpk k r * A = Bᴴ * Hpk k r * B → ∃ κ ∈ Kset k r, κ * A = B := by
  intro k r m A B h1 h2
  have hF := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  obtain ⟨U, hU1, hU2, hU3⟩ := unitary_comm_of_gram (Hpk k r) hF.1 hF.2.1 A B h1 h2
  refine ⟨U, ⟨?_, hU1⟩, hU3⟩
  show Uᴴ * Hpk k r * U = Hpk k r
  rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, hU1, Matrix.one_mul]

lemma sqLen_nonneg' {n : ℕ} (v : Fin n → ℂ) : 0 ≤ sqLen v :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

lemma sqLen_pos' {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) : 0 < sqLen v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

lemma sqLen_smul' {n : ℕ} (c : ℂ) (v : Fin n → ℂ) : sqLen (c • v) = Complex.normSq c * sqLen v := by
  simp [sqLen, Finset.mul_sum]

lemma star_dot_self {n : ℕ} (v : Fin n → ℂ) : star v ⬝ᵥ v = (sqLen v : ℂ) := by
  simp [sqLen, dotProduct, Complex.normSq_eq_conj_mul_self]

lemma continuous_sqLen' {n : ℕ} : Continuous (sqLen : (Fin n → ℂ) → ℝ) := by
  unfold sqLen
  exact continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

lemma mul_mem_GV {k r : ℕ} {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma mulVec_ne_zero {k r : ℕ} {a : Mat k r} (ha : a ∈ GV k r) {y : Fin (2 * r + k + 1) → ℂ}
    (hy : y ≠ 0) : a *ᵥ y ≠ 0 := by
  intro h
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hH : (Hpk k r)ᴴ * Hpk k r = 1 := (GlobalTheory.HCXi.KGroup.kset_facts k r).2.2.1.2
  apply hy
  calc y = ((Hpk k r)ᴴ * (aᴴ * Hpk k r * a)) *ᵥ y := by rw [ha', hH, Matrix.one_mulVec]
    _ = ((Hpk k r)ᴴ * (aᴴ * Hpk k r)) *ᵥ (a *ᵥ y) := by
        rw [Matrix.mulVec_mulVec]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

lemma exists_translate {k r : ℕ} {x v : Fin (2 * r + k + 1) → ℂ} (hx0 : herm (Hpk k r) x x = 0)
    (hx1 : sqLen x = 1) (hv0 : herm (Hpk k r) v v = 0) :
    ∃ κ ∈ Kset k r, ∃ c : ℂ, Complex.normSq c = sqLen v ∧ v = c • (κ *ᵥ x) := by
  set c : ℂ := ((Real.sqrt (sqLen v) : ℝ) : ℂ) with hc
  have hcn : Complex.normSq c = sqLen v := by
    rw [hc, Complex.normSq_ofReal, Real.mul_self_sqrt (sqLen_nonneg' v)]
  have key : ∀ (M : Mat k r) (y : Fin (2 * r + k + 1) → ℂ),
      (replicateCol (Fin 1) y)ᴴ * M * replicateCol (Fin 1) y = Matrix.of fun _ _ => star y ⬝ᵥ (M *ᵥ y) := by
    intro M y
    rw [Matrix.mul_assoc, ← replicateCol_mulVec, conjTranspose_replicateCol]
    ext i j
    simp [replicateRow_mul_replicateCol_apply]
  obtain ⟨κ, hκ, h⟩ := kset_transitive_of_gram k r 1 (replicateCol (Fin 1) (c • x)) (replicateCol (Fin 1) v)
    (by
      have h1 := key 1 (c • x)
      have h2 := key 1 v
      rw [Matrix.mul_one, Matrix.one_mulVec, star_dot_self] at h1 h2
      rw [h1, h2, sqLen_smul', hx1, hcn, mul_one])
    (by
      rw [key, key]
      have h1 : star v ⬝ᵥ (Hpk k r *ᵥ v) = 0 := hv0
      have h2 : star x ⬝ᵥ (Hpk k r *ᵥ x) = 0 := hx0
      rw [h1, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, h2, smul_zero, smul_zero])
  refine ⟨κ, hκ, c, hcn, ?_⟩
  rw [← replicateCol_mulVec] at h
  have := replicateCol_injective h
  rw [← this, Matrix.mulVec_smul]

lemma core (k r : ℕ) (μK : Measure (Mt k r)) (x : Fin (2 * r + k + 1) → ℂ) (hK : IsKMeas k r μK)
    (hx0 : herm (Hpk k r) x x = 0) (hx1 : sqLen x = 1) (g : Mat k r) (hg : g ∈ GV k r)
    (m : Measure (Fin (2 * r + k + 1) → ℂ)) [SFinite m] (d : ℝ)
    (hae : ∀ᵐ v ∂m, v ≠ 0 ∧ herm (Hpk k r) v v = 0)
    (hhom : ∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ v, f (s * sqLen v) ∂m) = ENNReal.ofReal (s ^ d) * ∫⁻ v, f (sqLen v) ∂m)
    (h0 : (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ 0)
    (htop : (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ ∞)
    (hinv : ∀ g ∈ GV k r, (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v))) ∂m) =
      ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) :
    (∫⁻ κ : Mt k r, ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ d) ∂μK) = 1 := by
  haveI : IsProbabilityMeasure μK := ⟨hK.2⟩
  set Γ := ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m with hΓ
  have hmem : ∀ᵐ κ : Mt k r ∂μK, Matrix.of κ ∈ Kset k r := hK.1.conc
  have hx : x ≠ 0 := by
    rintro rfl
    simp [sqLen] at hx1
  have hcg : Continuous fun κ : Mt k r => g * Matrix.of κ :=
    continuous_const.matrix_mul (continuous_id (X := Mat k r))
  have hcs : Continuous fun p : Mt k r × (Fin (2 * r + k + 1) → ℂ) =>
      sqLen ((g * Matrix.of p.1) *ᵥ p.2) :=
    continuous_sqLen'.comp ((hcg.comp continuous_fst).matrix_mulVec continuous_snd)
  have hcx : Continuous fun κ : Mt k r => sqLen ((g * Matrix.of κ) *ᵥ x) :=
    continuous_sqLen'.comp (hcg.matrix_mulVec continuous_const)
  have hm1 : Measurable fun p : Mt k r × (Fin (2 * r + k + 1) → ℂ) =>
      ENNReal.ofReal (Real.exp (-sqLen ((g * Matrix.of p.1) *ᵥ p.2))) :=
    (Real.continuous_exp.comp hcs.neg).measurable.ennreal_ofReal
  have hm2 : Measurable fun p : Mt k r × (Fin (2 * r + k + 1) → ℂ) =>
      ENNReal.ofReal (Real.exp (-(sqLen ((g * Matrix.of p.1) *ᵥ x) * sqLen p.2))) :=
    (Real.continuous_exp.comp ((hcx.comp continuous_fst).mul
      (continuous_sqLen'.comp continuous_snd)).neg).measurable.ennreal_ofReal
  have e1 : Γ = ∫⁻ κ : Mt k r, ∫⁻ v,
      ENNReal.ofReal (Real.exp (-sqLen ((g * Matrix.of κ) *ᵥ v))) ∂m ∂μK := by
    rw [lintegral_congr_ae (g := fun _ => Γ)]
    · simp
    · filter_upwards [hmem] with κ hκ using hinv _ (mul_mem_GV hg hκ.1)
  have e2 : ∀ᵐ v ∂m, (∫⁻ κ : Mt k r,
      ENNReal.ofReal (Real.exp (-sqLen ((g * Matrix.of κ) *ᵥ v))) ∂μK) =
      ∫⁻ κ : Mt k r, ENNReal.ofReal (Real.exp (-(sqLen ((g * Matrix.of κ) *ᵥ x) * sqLen v))) ∂μK := by
    filter_upwards [hae] with v hv
    obtain ⟨a, ha, c, hc, hv'⟩ := exists_translate hx0 hx1 hv.2
    have hr : Measurable (rmulF a) := by
      have : Continuous (rmulF a) := (continuous_id (X := Mat k r)).matrix_mul continuous_const
      exact this.measurable
    have hf : Measurable fun κ : Mt k r =>
        ENNReal.ofReal (Real.exp (-(sqLen ((g * Matrix.of κ) *ᵥ x) * sqLen v))) :=
      (Real.continuous_exp.comp (hcx.mul continuous_const).neg).measurable.ennreal_ofReal
    conv_rhs => rw [← hK.1.right a ha]
    rw [lintegral_map hf hr]
    refine lintegral_congr fun κ => ?_
    have : Matrix.of (rmulF a κ) = Matrix.of κ * a := rfl
    rw [this, ← hc, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec x _ a, mul_comm _ (Complex.normSq c), ← sqLen_smul',
      ← Matrix.mulVec_smul, ← hv']
  have e3 : ∀ᵐ κ : Mt k r ∂μK,
      (∫⁻ v, ENNReal.ofReal (Real.exp (-(sqLen ((g * Matrix.of κ) *ᵥ x) * sqLen v))) ∂m) =
      ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ d) * Γ := by
    filter_upwards [hmem] with κ hκ
    exact hhom _ (sqLen_pos' (mulVec_ne_zero (mul_mem_GV hg hκ.1) hx))
      (fun t => ENNReal.ofReal (Real.exp (-t)))
      (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal
  have e4 : Γ = (∫⁻ κ : Mt k r, ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ d) ∂μK) * Γ := by
    calc Γ = _ := e1
      _ = _ := lintegral_lintegral_swap hm1.aemeasurable
      _ = _ := lintegral_congr_ae e2
      _ = _ := (lintegral_lintegral_swap hm2.aemeasurable).symm
      _ = _ := lintegral_congr_ae e3
      _ = _ := lintegral_mul_const' _ _ htop
  have e5 : (∫⁻ κ : Mt k r, ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ d) ∂μK) * Γ = 1 * Γ := by
    rw [one_mul, ← e4]
  exact (ENNReal.mul_left_inj h0 htop).mp e5

theorem poisson_integral : ∀ (k r : ℕ) (μK : Measure (Mt k r)) (x : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → IsKMeas k r μK → herm (Hpk k r) x x = 0 → sqLen x = 1 → ∀ g ∈ GV k r, (∫⁻ κ : Mt k r, ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ (-((2 * r + k : ℕ) : ℝ))) ∂μK) = 1 := by
  intro k r μK x hk hK hx0 hx1 g hg
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨m, hs, hae, hhom, h0, htop, hinv⟩ := GlobalTheory.HCXi.ConeZero.exists_coneMeasure k hk
    exact core k 0 μK x hK hx0 hx1 g hg m _ hae hhom h0 htop hinv
  · obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨m, hs, hae, hhom, h0, htop, hinv⟩ := GlobalTheory.HCXi.exists_cone_measure_pos_rank k r'
    exact core k _ μK x hK hx0 hx1 g hg m _ hae hhom h0 htop hinv

end GlobalTheory.HCXi.Poisson
end

section
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.LineStabiliser

open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser

variable (k r' : ℕ)

def fst : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

def lst : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

theorem e0_eq : e0 k r' = Pi.single (fst k r') 1 := rfl

theorem gram_mulVec_e0 : Hpk k (1 + r') *ᵥ e0 k r' = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  rw [e0_eq, mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem star_e0_vecMul_hpk_eq_single_lst : star (e0 k r') ᵥ* Hpk k (1 + r') = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  have h : star (e0 k r') = Pi.single (fst k r') 1 := by
    rw [e0_eq, ← Pi.single_star, star_one]
  rw [h, single_one_vecMul, Matrix.row_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem pair_e0_left (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    star (e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ v) = v (lst k r') := by
  rw [dotProduct_mulVec, star_e0_vecMul_hpk_eq_single_lst, single_one_dotProduct]

theorem lift_lst (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (lst k r') = 0 := by
  unfold liftVec
  rw [dif_neg]
  simp only [lst]
  omega

theorem e0_lst_eq_zero : e0 k r' (lst k r') = 0 := by
  rw [e0_eq, Pi.single_apply, if_neg]
  simp only [lst, fst, Fin.ext_iff]
  omega

theorem decomp (u : Fin (2 * (1 + r') + k + 1) → ℂ) (hu : u (lst k r') = 0) :
    u = liftVec k 1 r' ((incl k 1 r')ᴴ *ᵥ u) + u (fst k r') • e0 k r' := by
  have hc : ∀ j, ((incl k 1 r')ᴴ *ᵥ u) j = u (levPos k 1 r' j) := fun j =>
    inclH_mul k 1 r' (Matrix.of fun a _ => u a) j j
  ext i
  have hi := i.isLt
  rw [Pi.add_apply, Pi.smul_apply, e0_eq, Pi.single_apply, smul_eq_mul]
  unfold liftVec
  by_cases h : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos h, hc, if_neg (by simp only [fst, Fin.ext_iff]; omega), mul_zero, add_zero]
    congr 1
    simp only [levPos, Fin.ext_iff]
    omega
  · rw [dif_neg h, zero_add]
    by_cases h0 : i = fst k r'
    · rw [if_pos h0, mul_one, h0]
    · rw [if_neg h0, mul_zero, ← hu]
      congr 1
      simp only [fst, lst, Fin.ext_iff] at h0 ⊢
      omega

theorem pair_unitary {n : ℕ} (H p : Matrix (Fin n) (Fin n) ℂ) (hp : pᴴ * H * p = H) (v w : Fin n → ℂ) :
    star (p *ᵥ w) ⬝ᵥ (H *ᵥ (p *ᵥ v)) = star w ⬝ᵥ (H *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hp]

theorem pair_lift (v w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' w) ⬝ᵥ (Hpk k (1 + r') *ᵥ liftVec k 1 r' v) = star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [liftVec_eq, liftVec_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, gram_inner]

theorem pair_shift (v w : Fin (2 * r' + k + 1) → ℂ) (c d : ℂ) :
    star (liftVec k 1 r' w + d • e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ (liftVec k 1 r' v + c • e0 k r')) =
      star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [star_add, add_dotProduct, star_smul, smul_dotProduct, pair_e0_left, mulVec_add, dotProduct_add,
    pair_lift, mulVec_smul, gram_mulVec_e0, dotProduct_smul, dotProduct_single_one]
  simp [lift_lst, e0_lst_eq_zero]

theorem acts_through_level_one : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  intro k r' a p hp he
  have hp' : pᴴ * Hpk k (1 + r') * p = Hpk k (1 + r') := hp
  have ha : a ≠ 0 := by
    rintro rfl
    have h := pair_unitary _ p hp' (Pi.single (lst k r') 1) (e0 k r')
    rw [he, zero_smul, star_zero, zero_dotProduct, pair_e0_left] at h
    simp at h
  have hl : ∀ w, (p *ᵥ liftVec k 1 r' w) (lst k r') = 0 := by
    intro w
    have h := pair_unitary _ p hp' (liftVec k 1 r' w) (e0 k r')
    rw [he, star_smul, smul_dotProduct, pair_e0_left, pair_e0_left, lift_lst, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (star_ne_zero.2 ha)
  have hd : ∀ w, p *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (((incl k 1 r')ᴴ * p * incl k 1 r') *ᵥ w) +
        (p *ᵥ liftVec k 1 r' w) (fst k r') • e0 k r' := by
    intro w
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← liftVec_eq k 1 r' w]
    exact decomp k r' _ (hl w)
  refine ⟨ha, (incl k 1 r')ᴴ * p * incl k 1 r', ?_, fun w => ⟨_, hd w⟩⟩
  generalize (incl k 1 r')ᴴ * p * incl k 1 r' = g at hd
  show gᴴ * Hpk k r' * g = Hpk k r'
  ext i j
  have h := pair_unitary _ p hp' (liftVec k 1 r' (Pi.single j 1)) (liftVec k 1 r' (Pi.single i 1))
  rw [hd (Pi.single j 1), hd (Pi.single i 1), pair_shift, pair_lift, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec, ← Pi.single_star, star_one, single_one_dotProduct,
    single_one_dotProduct, mulVec_single_one, mulVec_single_one] at h
  exact h

end GlobalTheory.HCXi.LineStabiliser
end
end

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_line_stabilizer_levi : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  atlas_forward_decl GlobalTheory.HCXi.LineStabiliser.acts_through_level_one
end

section
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.VLev

theorem det_gram_cons {n m : ℕ} (e : Fin n → ℂ) (he : star e ⬝ᵥ e = 1) (w : Fin m → Fin n → ℂ)
    (hw : ∀ b, star e ⬝ᵥ w b = 0) (a : ℂ) (c : Fin m → ℂ) (v : Fin (m + 1) → Fin n → ℂ)
    (h0 : v 0 = a • e) (hs : ∀ b, v b.succ = w b + c b • e) :
    (Matrix.of fun i j => star (v i) ⬝ᵥ v j).det =
      (Complex.normSq a : ℂ) * (Matrix.of fun i j => star (w i) ⬝ᵥ w j).det := by
  have hw' : ∀ b, star (w b) ⬝ᵥ e = 0 := fun b => by
    rw [star_dotProduct, hw, star_zero]
  let u : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Matrix.of fun i j => (Fin.cons (α := fun _ => ℂ) (Fin.cons (α := fun _ => ℂ) a c j) (fun i' => if i'.succ = j then 1 else 0) i)
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Matrix.of fun i j => star (Fin.cons (α := fun _ => Fin n → ℂ) e w i) ⬝ᵥ (Fin.cons (α := fun _ => Fin n → ℂ) e w j)
  have hu : u.det = a := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero]
    · have : u.submatrix (Fin.succAbove 0) Fin.succ = 1 := by
        ext i j
        simp [u, Matrix.one_apply]
      rw [this]; simp [u]
    · intro i _
      simp [u]
  have hD : D.det = (Matrix.of fun i j => star (w i) ⬝ᵥ w j).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Finset.sum_eq_zero]
    · have : D.submatrix Fin.succ (Fin.succAbove 0) = Matrix.of fun i j => star (w i) ⬝ᵥ w j := by
        ext i j
        simp [D]
      rw [this]; simp [D, he]
    · intro i _
      simp [D, hw]
  have hG : (Matrix.of fun i j => star (v i) ⬝ᵥ v j) = uᴴ * D * u := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [u, D, h0, hs, Matrix.mul_apply, Fin.sum_univ_succ, he, hw, hw', Matrix.conjTranspose_apply, mul_add, add_mul, Finset.sum_add_distrib,
        apply_ite (starRingEnd ℂ)] <;> ring
  rw [hG, det_mul, det_mul, det_conjTranspose, hu, hD, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]; ring

theorem gram_eq (k r : ℕ) (g : Mat k r) (j : Fin (r + 1)) :
    gram k r g j = (Matrix.of fun i i' : Fin (j.val + 1) =>
      star (g *ᵥ fvec k r (isoVec k r) (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)) ⬝ᵥ
        (g *ᵥ fvec k r (isoVec k r) (Fin.castLE (Nat.succ_le_of_lt j.isLt) i'))).det.re := by
  unfold gram
  congr 2

theorem gram_nonneg (k r : ℕ) (g : Mat k r) (j : Fin (r + 1)) : 0 ≤ gram k r g j := by
  unfold gram
  have := ((Matrix.posSemidef_conjTranspose_mul_self (g * frame k r)).submatrix
    (Fin.castLE (Nat.succ_le_of_lt j.isLt))).det_nonneg
  exact (Complex.nonneg_iff.1 this).1

theorem gram_K (k r : ℕ) (κ g : Mat k r) (hκ : κᴴ * κ = 1) (j : Fin (r + 1)) :
    gram k r (κ * g) j = gram k r g j := by
  unfold gram
  have : (κ * g * frame k r)ᴴ * (κ * g * frame k r) = (g * frame k r)ᴴ * (g * frame k r) := by
    rw [Matrix.mul_assoc κ, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]
  rw [this]

theorem fvec_zero (k r' : ℕ) (j : Fin (1 + r' + 1)) (hj : j.val = 0) :
    fvec k (1 + r') (isoVec k (1 + r')) j = e0 k r' := by
  unfold fvec e0
  rw [dif_pos (by omega)]
  congr 1
  ext; simp [eI, a0, hj]

theorem liftVec_add' (k i r' : ℕ) (v w : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' (v + w) = liftVec k i r' v + liftVec k i r' w := by
  ext p; simp only [liftVec, Pi.add_apply]; split_ifs <;> simp

theorem liftVec_smul' (k i r' : ℕ) (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' (c • v) = c • liftVec k i r' v := by
  ext p; simp only [liftVec, Pi.smul_apply]; split_ifs <;> simp

theorem fvec_succ (k r' : ℕ) (j : Fin (1 + r' + 1)) (b : Fin (r' + 1)) (hj : j.val = b.val + 1) :
    fvec k (1 + r') (isoVec k (1 + r')) j = liftVec k 1 r' (fvec k r' (isoVec k r') b) := by
  unfold fvec
  by_cases hb : b.val < r'
  · rw [dif_pos (by omega), dif_pos hb]
    exact (PI.QnLevBasicsW.bvec_lift _ _ (by simp only [eI]; omega)).symm
  · rw [dif_neg (by omega), dif_neg hb]
    unfold isoVec
    rw [liftVec_smul', liftVec_add', PI.QnLevBasicsW.bvec_lift _ (wI k (1 + r') 0) (by simp only [wI]; omega),
      PI.QnLevBasicsW.bvec_lift _ (wI k (1 + r') (Fin.last k)) (by simp only [wI]; omega)]

theorem star_e0_dotProduct (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    star (e0 k r') ⬝ᵥ v = v (eI k (1 + r') (a0 r')) := by
  simp [e0, bvec]

theorem star_e0_dotProduct_self (k r' : ℕ) : star (e0 k r') ⬝ᵥ e0 k r' = 1 := by
  rw [star_e0_dotProduct]; simp [e0, bvec]

theorem star_e0_dotProduct_lift (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (e0 k r') ⬝ᵥ liftVec k 1 r' w = 0 := by
  rw [star_e0_dotProduct]; exact PI.QnLevBasicsW.liftVec_apply_out _ _ (by simp [eI, a0])

section
variable {k r' : ℕ} (M : Mat k (1 + r')) (h : Mat k r') (a : ℂ) (hM0 : M *ᵥ e0 k r' = a • e0 k r')
  (hM : ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, M *ᵥ liftVec k 1 r' w = liftVec k 1 r' (h *ᵥ w) + c • e0 k r')
include hM0

theorem gram_zero (j : Fin (1 + r' + 1)) (hj : j.val = 0) : gram k (1 + r') M j = Complex.normSq a := by
  obtain ⟨j, hj'⟩ := j
  simp only at hj
  subst hj
  rw [gram_eq]
  rw [det_gram_cons (m := 0) (e0 k r') (star_e0_dotProduct_self k r') Fin.elim0 (fun b => b.elim0) a Fin.elim0 _
    (by rw [fvec_zero _ _ _ rfl, hM0]) (fun b => b.elim0)]
  simp

include hM
theorem gram_succ (j : Fin (1 + r' + 1)) (b : Fin (r' + 1)) (hj : j.val = b.val + 1) :
    gram k (1 + r') M j = Complex.normSq a * gram k r' h b := by
  obtain ⟨j, hj'⟩ := j
  simp only at hj
  subst hj
  choose c hc using hM
  rw [gram_eq, gram_eq]
  rw [det_gram_cons (m := b.val + 1) (e0 k r') (star_e0_dotProduct_self k r')
    (fun i => liftVec k 1 r' (h *ᵥ fvec k r' (isoVec k r') (Fin.castLE (Nat.succ_le_of_lt b.isLt) i)))
    (fun _ => star_e0_dotProduct_lift _ _ _) a
    (fun i => c (fvec k r' (isoVec k r') (Fin.castLE (Nat.succ_le_of_lt b.isLt) i))) _
    (by rw [fvec_zero _ _ _ rfl, hM0])
    (fun i => by rw [fvec_succ _ _ _ (Fin.castLE (Nat.succ_le_of_lt b.isLt) i) rfl, hc])]
  simp only [PI.QnLevBasicsW.dot_lift, Complex.re_ofReal_mul]

theorem vHalf_block (ha : a ≠ 0) : vHalf k (1 + r') M =
    Complex.normSq a ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' h := by
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
  unfold vHalf
  rw [Fin.prod_univ_add, Fin.prod_univ_one, gram_zero M a hM0 _ rfl,
    gram_succ M h a hM0 hM (Fin.last _) (Fin.last _) (by simp; omega),
    Finset.prod_congr rfl (fun (b : Fin r') _ => by
      rw [gram_succ M h a hM0 hM _ b.castSucc (by simp; omega), mul_inv]),
    Finset.prod_mul_distrib, Real.mul_rpow hN.le (gram_nonneg _ _ _ _)]
  have : Complex.normSq a ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) =
      (Complex.normSq a)⁻¹ * (Complex.normSq a)⁻¹ ^ r' * Complex.normSq a ^ (-((k : ℝ) / 2)) := by
    rw [← pow_succ', inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hN.le, ← Real.rpow_add hN]
    congr 1; push_cast; ring
  rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring
end

theorem sqLen_eq {n : ℕ} (v : Fin n → ℂ) : sqLen v = (star v ⬝ᵥ v).re := by
  simp only [sqLen, dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem levi_embedding_mulVec_e0 (k r' : ℕ) (y : Mat k r') : ιLev k 1 r' y *ᵥ e0 k r' = e0 k r' :=
  PI.QnLevBasicsW.col_fix y _ (fun b hb => by simp [eI, a0] at hb)

theorem parabolic_mulVec_e0_smul {k r' : ℕ} {p : Mat k (1 + r')} (hp : p ∈ Pset k (1 + r')) :
    ∃ a : ℂ, p *ᵥ e0 k r' = a • e0 k r' := by
  obtain ⟨-, u, hu, hpu⟩ := hp
  refine ⟨u 0 0, ?_⟩
  ext i
  have h1 := congrFun (congrFun hpu i) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ (n := 1 + r'), Finset.sum_eq_zero (s := Finset.univ)
    (f := fun b : Fin (1 + r') => frame k (1 + r') i b.succ * u b.succ 0)
    (fun b _ => by rw [hu (show id (0 : Fin (1 + r' + 1)) < id b.succ from Fin.succ_pos b), mul_zero])] at h1
  simp only [frame, Matrix.of_apply, fvec_zero k r' 0 rfl, add_zero] at h1
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [h1, mul_comm]

theorem vHalf_level : ∀ k r' : ℕ, 1 ≤ k → ∀ x ∈ GV k (1 + r'), ∃ g₁ ∈ GV k r', ∀ y ∈ GV k r', vHalf k (1 + r') (x * ιLev k 1 r' y) = sqLen (x *ᵥ e0 k r') ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' (g₁ * y) := by
  intro k r' hk x hx
  obtain ⟨κ, hκ, p, hp, rfl⟩ := GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq k (1 + r') hk x hx
  obtain ⟨a, ha⟩ := parabolic_mulVec_e0_smul hp
  obtain ⟨ha0, g₁, hg₁, hw⟩ := GlobalTheory.T.parabolic_line_stabilizer_levi k r' a p hp.1 ha
  refine ⟨g₁, hg₁, fun y _ => ?_⟩
  have h1 : vHalf k (1 + r') (κ * p * ιLev k 1 r' y) = vHalf k (1 + r') (p * ιLev k 1 r' y) := by
    simp only [vHalf, Matrix.mul_assoc κ, gram_K _ _ _ _ hκ.2]
  have h2 : sqLen ((κ * p) *ᵥ e0 k r') = Complex.normSq a := by
    rw [sqLen_eq, ← Matrix.mulVec_mulVec, ha, star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hκ.2,
      Matrix.one_mulVec, star_smul, smul_dotProduct, dotProduct_smul, star_e0_dotProduct_self]
    simp [Complex.normSq_apply]
  rw [h1, h2]
  refine vHalf_block _ _ a ?_ (fun w => ?_) ha0
  · rw [← Matrix.mulVec_mulVec, levi_embedding_mulVec_e0, ha]
  · rw [← Matrix.mulVec_mulVec, PI.QnLevBasicsW.mulVec_lift, ← Matrix.mulVec_mulVec]
    exact hw _

end GlobalTheory.HCXi.VLev
end
end

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_volume_levi_recursion : ∀ k r' : ℕ, 1 ≤ k → ∀ x ∈ GV k (1 + r'), ∃ g₁ ∈ GV k r', ∀ y ∈ GV k r', vHalf k (1 + r') (x * ιLev k 1 r' y) = sqLen (x *ᵥ e0 k r') ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' (g₁ * y) := by
  atlas_forward_decl GlobalTheory.HCXi.VLev.vHalf_level
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.LeOne

lemma gv_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma meas_v {k r : ℕ} (hk : 1 ≤ k) {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {f : α → Mat k r} (hf : Continuous f) :
    Measurable fun t => ENNReal.ofReal (vHalf k r (f t)) ^ 2 := by
  have hm := (GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn k r hk).2.2.1
  have hf' : Continuous (Y := Mt k r) fun t => Matrix.of.symm (f t) := hf
  exact (ENNReal.measurable_ofReal.comp (hm.comp hf'.measurable)).pow_const 2

lemma cont_of {k r : ℕ} : Continuous fun κ : Mt k r => (Matrix.of κ : Mat k r) := continuous_id

lemma cont_lev (k i r' : ℕ) : Continuous (ιLev k i r') := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  unfold ιLev
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  all_goals exact continuous_const

lemma sqLen_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ sqLen v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma diag_re {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (a : Fin m) :
    ((Aᴴ * A) a a).re = sqLen fun i => A i a := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sqLen, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma col_facts (k r : ℕ) (hk : 1 ≤ k) (a : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r (isoVec k r) a) (fvec k r (isoVec k r) a) = 0 ∧
      sqLen (fvec k r (isoVec k r) a) = 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic k r hk
  constructor
  · have := congrFun (congrFun h2 a) a
    rw [Matrix.mul_assoc] at this
    exact this
  · have := diag_re (frame k r) a
    rw [h1] at this
    rw [Matrix.one_apply_eq, Complex.one_re] at this
    exact this.symm

lemma sq_rpow {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    ENNReal.ofReal (s ^ (-((m : ℝ) / 2))) ^ 2 = ENNReal.ofReal (s ^ (-(m : ℝ))) := by
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hs _), ← Real.rpow_natCast, ← Real.rpow_mul hs]
  congr 2
  push_cast
  ring

lemma vHalf_zero (k : ℕ) (x : Mat k 0) :
    vHalf k 0 x = sqLen (x *ᵥ isoVec k 0) ^ (-((k : ℝ) / 2)) := by
  have : gram k 0 x (Fin.last 0) = sqLen (x *ᵥ isoVec k 0) := by
    unfold GlobalTheory.HCXi.gram
    rw [show ∀ M : Matrix (Fin ((Fin.last 0 : ℕ) + 1)) (Fin ((Fin.last 0 : ℕ) + 1)) ℂ, M.det = M 0 0 from
      fun M => Matrix.det_fin_one M, Matrix.submatrix_apply, diag_re]
    rfl
  unfold vHalf
  rw [this]
  simp

lemma base (k : ℕ) (μK : Measure (Mt k 0)) (hk : 1 ≤ k) (hμ : IsKMeas k 0 μK) (g : Mat k 0) (hg : g ∈ GV k 0) :
    (∫⁻ κ : Mt k 0, ENNReal.ofReal (vHalf k 0 (g * Matrix.of κ)) ^ 2 ∂μK) = 1 := by
  obtain ⟨h1, h2⟩ := col_facts k 0 hk (Fin.last 0)
  have h := GlobalTheory.HCXi.Poisson.poisson_integral k 0 μK (isoVec k 0) hk hμ h1 h2 g hg
  rw [← h]
  refine lintegral_congr fun κ => ?_
  rw [vHalf_zero, sq_rpow (sqLen_nonneg _)]
  simp

lemma step (k r' : ℕ) (hk : 1 ≤ k)
    (ih : ∀ μ : Measure (Mt k r'), IsKMeas k r' μ → ∀ g ∈ GV k r',
      (∫⁻ κ : Mt k r', ENNReal.ofReal (vHalf k r' (g * Matrix.of κ)) ^ 2 ∂μ) = 1)
    (μK : Measure (Mt k (1 + r'))) (hμ : IsKMeas k (1 + r') μK) (g : Mat k (1 + r')) (hg : g ∈ GV k (1 + r')) :
    (∫⁻ κ : Mt k (1 + r'), ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ)) ^ 2 ∂μK) = 1 := by
  obtain ⟨μ₁, hμ₁⟩ := GlobalTheory.HCXi.exists_isKMeas k r'
  have : IsProbabilityMeasure μK := ⟨hμ.2⟩
  have : IsProbabilityMeasure μ₁ := ⟨hμ₁.2⟩
  have hae : ∀ᵐ κ ∂μK, (Matrix.of κ : Mat k (1 + r')) ∈ Kset k (1 + r') := hμ.1.conc
  have hae₁ : ∀ᵐ y ∂μ₁, (Matrix.of y : Mat k r') ∈ Kset k r' := hμ₁.1.conc
  have hm : Measurable fun κ : Mt k (1 + r') => ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ)) ^ 2 :=
    meas_v hk (continuous_const.matrix_mul cont_of)
  have hm2 : Measurable fun q : Mt k r' × Mt k (1 + r') =>
      ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of q.2 * ιLev k 1 r' (Matrix.of q.1))) ^ 2 :=
    meas_v hk ((continuous_const.matrix_mul (cont_of.comp continuous_snd)).matrix_mul
      ((cont_lev k 1 r').comp (cont_of.comp continuous_fst)))
  have hsw := lintegral_lintegral_swap (μ := μ₁) (ν := μK)
    (f := fun (y : Mt k r') (κ : Mt k (1 + r')) =>
      ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ * ιLev k 1 r' (Matrix.of y))) ^ 2) hm2.aemeasurable
  have he : fvec k (1 + r') (isoVec k (1 + r')) ⟨0, Nat.succ_pos _⟩ = e0 k r' := by
    unfold fvec
    rw [dif_pos (show (0 : ℕ) < 1 + r' by omega)]
    rfl
  obtain ⟨h1, h2⟩ := col_facts k (1 + r') hk ⟨0, Nat.succ_pos _⟩
  rw [he] at h1 h2
  calc (∫⁻ κ : Mt k (1 + r'), ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ)) ^ 2 ∂μK)
      = ∫⁻ _y : Mt k r', (∫⁻ κ : Mt k (1 + r'), ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ)) ^ 2 ∂μK) ∂μ₁ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ y : Mt k r', ∫⁻ κ : Mt k (1 + r'),
          ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ * ιLev k 1 r' (Matrix.of y))) ^ 2 ∂μK ∂μ₁ := by
        refine lintegral_congr_ae (hae₁.mono fun y hy => ?_)
        have hrm : Measurable (rmulF (ιLev k 1 r' (Matrix.of y)) : Mt k (1 + r') → Mt k (1 + r')) :=
          Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
        dsimp only
        conv_lhs => rw [← hμ.1.right _ (GlobalTheory.HCXi.blockEmb_mem_Kset k r' _ hy)]
        rw [lintegral_map hm hrm]
        simp only [Matrix.mul_assoc]
        rfl
    _ = ∫⁻ κ : Mt k (1 + r'), ∫⁻ y : Mt k r',
          ENNReal.ofReal (vHalf k (1 + r') (g * Matrix.of κ * ιLev k 1 r' (Matrix.of y))) ^ 2 ∂μ₁ ∂μK := hsw
    _ = ∫⁻ κ : Mt k (1 + r'), ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ e0 k r') ^
          (-((2 * (1 + r') + k : ℕ) : ℝ))) ∂μK := by
        refine lintegral_congr_ae (hae.mono fun κ hκ => ?_)
        obtain ⟨g₁, hg₁, hv⟩ := GlobalTheory.T.half_volume_levi_recursion k r' hk _ (gv_mul hg hκ.1)
        have hm3 : Measurable fun y : Mt k r' => ENNReal.ofReal (vHalf k r' (g₁ * Matrix.of y)) ^ 2 :=
          meas_v hk (continuous_const.matrix_mul cont_of)
        dsimp only
        rw [← sq_rpow (sqLen_nonneg _), ← mul_one (ENNReal.ofReal _ ^ 2), ← ih μ₁ hμ₁ g₁ hg₁,
          ← lintegral_const_mul _ hm3]
        refine lintegral_congr_ae (hae₁.mono fun y hy => ?_)
        dsimp only
        rw [hv _ hy.1, ENNReal.ofReal_mul (Real.rpow_nonneg (sqLen_nonneg _) _), mul_pow]
    _ = 1 := GlobalTheory.HCXi.Poisson.poisson_integral k (1 + r') μK (e0 k r') hk hμ h1 h2 g hg


end GlobalTheory.HCXi.LeOne

namespace GlobalTheory.HCXi




end GlobalTheory.HCXi
end
