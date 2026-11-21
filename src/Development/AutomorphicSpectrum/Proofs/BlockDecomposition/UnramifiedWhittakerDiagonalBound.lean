import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdelicNormVecMulLeMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizationPureIntegrand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitSmoothnessHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableModulusPowOnBoundedUnits
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSmoothnessHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaSpherical
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilThetaRealization
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial

section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitBound

open scoped Pointwise

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem det_diagonal_two (a : Fˣ) : ((dg2 a 1 : GL (Fin 2) F).val).det = a := by
  simp [dg2, Matrix.det_fin_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem nsg_one : nsg (F × F) (1 : F) = 1 := by
  unfold nsg
  rw [if_pos]
  exact ⟨1, by simp⟩

theorem wcS_diag (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (a : Fˣ) :
    WcS χ c₁ c₂ Ψ (dg2 a 1) = ((c₁ a : ℂˣ) : ℂ) * mp a (1 / 2) *
      ∫ u : Fˣ, Ψ (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) * (((c₂ u)⁻¹ : ℂˣ) : ℂ) ∂multHaar F := by
  have hd : GeneralLinearGroup.det (dg2 a 1 : GL (Fin 2) F) = a := Units.ext (by
    simpa using det_diagonal_two a)
  have h00 : (dg2 a 1 : GL (Fin 2) F).val 0 0 = a := by simp [dg2]
  have h01 : (dg2 a 1 : GL (Fin 2) F).val 0 1 = 0 := by simp [dg2]
  have h10 : (dg2 a 1 : GL (Fin 2) F).val 1 0 = 0 := by simp [dg2]
  have h11 : (dg2 a 1 : GL (Fin 2) F).val 1 1 = 1 := by simp [dg2]
  unfold WcS
  rw [hd, det_diagonal_two, h00, h01, h10, h11]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have ha : (a : F) / a = 1 := div_self a.ne_zero
  simp only [rW, ha, zero_div, if_true, nsg_one]
  simp [mul_comm]

end GlobalTheory.CompanionTheory.SplitBound
end
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.WthCont

theorem WthR_continuous : ∀ n : ℤ, Continuous (GL2LocalData.WthR n) := by
  intro n
  have hv : Continuous fun g : GL (Fin 2) ℝ => (g.val : Matrix (Fin 2) (Fin 2) ℝ) :=
    Units.continuous_val
  have hent : ∀ i j, Continuous fun g : GL (Fin 2) ℝ => (g.val i j : ℝ) := fun i j =>
    hv.matrix_elem i j
  have hdet : Continuous fun g : GL (Fin 2) ℝ => (g.val).det := hv.matrix_det
  have hne : ∀ g : GL (Fin 2) ℝ, (g.val).det ≠ 0 := fun g =>
    (Matrix.isUnits_det_units g).ne_zero
  have hopen : IsOpen {g : GL (Fin 2) ℝ | 0 < (g.val).det} := isOpen_lt continuous_const hdet
  have hclosed : IsClosed {g : GL (Fin 2) ℝ | 0 < (g.val).det} := by
    have e : {g : GL (Fin 2) ℝ | 0 < (g.val).det} = {g : GL (Fin 2) ℝ | 0 ≤ (g.val).det} := by
      ext g
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (hne g).symm⟩
    rw [e]
    exact isClosed_le continuous_const hdet
  have hc : ∀ i j, Continuous fun g : GL (Fin 2) ℝ => ((g.val i j : ℝ) : ℂ) := fun i j =>
    Complex.continuous_ofReal.comp (hent i j)
  have hq : Continuous fun g : GL (Fin 2) ℝ =>
      ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)) :=
    (hc 1 1).add (continuous_const.mul (hc 1 0))
  have hp : Continuous fun g : GL (Fin 2) ℝ =>
      ((g.val 0 1 : ℂ) + Complex.I * (g.val 0 0 : ℂ)) :=
    (hc 0 1).add (continuous_const.mul (hc 0 0))
  have hq0 : ∀ g : GL (Fin 2) ℝ, ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)) ≠ 0 := by
    intro g h0
    have h1 : (g.val 1 1 : ℝ) = 0 := by
      have := congrArg Complex.re h0
      simpa using this
    have h2 : (g.val 1 0 : ℝ) = 0 := by
      have := congrArg Complex.im h0
      simpa using this
    apply hne g
    rw [Matrix.det_fin_two, h1, h2]
    ring
  have hfun : GL2LocalData.WthR n = fun g : GL (Fin 2) ℝ =>
      if 0 < (g.val).det then
        (((g.val).det : ℝ) : ℂ) ^ (((n.natAbs + 1 : ℕ) : ℂ) / 2) *
          ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
          Complex.exp (2 * Real.pi * Complex.I * (((g.val 0 1 : ℂ) + Complex.I * (g.val 0 0 : ℂ)) /
            ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ))))
      else 0 := rfl
  rw [hfun]
  refine continuous_if ?_ ?_ continuousOn_const
  · intro a ha
    have hcl : IsClopen {g : GL (Fin 2) ℝ | 0 < (g.val).det} := ⟨hclosed, hopen⟩
    rw [hcl.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty a)
  · rw [hclosed.closure_eq]
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · refine ContinuousOn.cpow_const ?_ ?_
      · exact (Complex.continuous_ofReal.comp hdet).continuousOn
      · intro g hg
        exact Complex.ofReal_mem_slitPlane.mpr hg
    · exact (hq.zpow₀ _ (fun g => Or.inl (hq0 g))).continuousOn
    · exact (Complex.continuous_exp.comp
        (continuous_const.mul (hp.div hq hq0))).continuousOn

end GlobalTheory.CompanionTheory.GL2Factorization.WthCont
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_real_whittaker : ∀ n : ℤ, Continuous (GL2LocalData.WthR n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.WthCont.WthR_continuous
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.NormWth

theorem norm_core (m : ℕ) (A B p q r u d : ℝ) (hB : B ≠ 0)
    (h00 : p * p + q * q = 1) (h11 : r * r + u * u = 1) (h01 : p * r + q * u = 0)
    (hd : d = A * B * B * (p * u - q * r)) (hpos : 0 < d) :
    ‖((d : ℝ) : ℂ) ^ ((m : ℂ) / 2) *
        (((B * u : ℝ) : ℂ) + Complex.I * ((B * r : ℝ) : ℂ)) ^ (-(m : ℤ)) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((((A * B * q : ℝ) : ℂ) + Complex.I * ((A * B * p : ℝ) : ℂ)) /
            (((B * u : ℝ) : ℂ) + Complex.I * ((B * r : ℝ) : ℂ))))‖ =
      |A| ^ ((m : ℝ) / 2) * Real.exp (-(2 * Real.pi * |A|)) := by
  set D : ℝ := p * u - q * r with hD
  have hD2 : D * D = 1 := by
    rw [hD]; linear_combination (r * r + u * u) * h00 + h11 - (p * r + q * u) * h01
  have hp : p = D * u := by
    rw [hD]; linear_combination (-p) * h11 + r * h01
  have hq : q = -(D * r) := by
    rw [hD]; linear_combination u * h01 - q * h11
  have hBB : 0 < B * B := mul_self_pos.2 hB
  have hAD : 0 < A * D := by
    have h : 0 < (A * D) * (B * B) := by rw [hd] at hpos; linarith [hpos, (by ring : A * B * B * D = (A * D) * (B * B))]
    by_contra hn
    nlinarith [not_lt.1 hn, hBB]
  have ht : A * D = |A| := by
    have h1 : (D - 1) * (D + 1) = 0 := by linear_combination hD2
    rcases mul_eq_zero.1 h1 with h | h
    · have hD1 : D = 1 := by linarith
      rw [hD1, mul_one] at hAD ⊢
      exact (abs_of_pos hAD).symm
    · have hD1 : D = -1 := by linarith
      rw [hD1] at hAD ⊢
      have : A < 0 := by linarith
      rw [abs_of_neg this]; ring
  set t : ℝ := |A| with htdef
  have htpos : 0 < t := ht ▸ hAD
  have hdt : d = t * (B * B) := by rw [hd, ← ht]; ring
  set z : ℂ := (u : ℂ) + (r : ℂ) * Complex.I with hz
  have hz1 : ‖z‖ = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, hz, Complex.normSq_add_mul_I]; linarith [h11, sq u, sq r]
    have h0 := norm_nonneg z
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  have hBc : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hB
  have hx : ((B * u : ℝ) : ℂ) + Complex.I * ((B * r : ℝ) : ℂ) = (B : ℂ) * z := by
    rw [hz]; push_cast; ring
  have hy : ((A * B * q : ℝ) : ℂ) + Complex.I * ((A * B * p : ℝ) : ℂ) =
      (B : ℂ) * z * (Complex.I * (t : ℂ)) := by
    rw [hz, ← ht, hp, hq]
    push_cast
    linear_combination (-((A : ℂ) * B * D * r)) * Complex.I_sq
  have hexp : 2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (t : ℂ)) =
      ((-(2 * Real.pi * t) : ℝ) : ℂ) := by
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * t) * Complex.I_sq
  rw [hx, hy, mul_div_cancel_left₀ _ (mul_ne_zero hBc hz0), hexp, norm_mul, norm_mul,
    ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_zpow, norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hm : ((m : ℂ) / 2) = (((m : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hm, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.ofReal_re, hdt,
    Real.mul_rpow htpos.le hBB.le]
  have hab : 0 < |B| := abs_pos.2 hB
  have hB2 : (B * B) ^ ((m : ℝ) / 2) = |B| ^ m := by
    rw [← abs_mul_self B, abs_mul, ← sq, ← Real.rpow_natCast |B| 2, ← Real.rpow_mul hab.le,
      ← Real.rpow_natCast |B| m]
    congr 1
    push_cast
    ring
  rw [hB2, _root_.zpow_neg, zpow_natCast]
  have : |B| ^ m ≠ 0 := (pow_pos hab m).ne'
  field_simp

theorem norm_WthR_iwasawa_le : ∀ (n : ℤ) (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 →
    ‖GL2LocalData.WthR n (dg2 (a * b) b * k)‖ ≤
      |(a : ℝ)| ^ (((n.natAbs + 1 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * |(a : ℝ)|)) := by
  intro n a b k hk
  have h00 : k.val 0 0 * k.val 0 0 + k.val 0 1 * k.val 0 1 = 1 := by
    have := congrFun (congrFun hk 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : k.val 1 0 * k.val 1 0 + k.val 1 1 * k.val 1 1 = 1 := by
    have := congrFun (congrFun hk 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : k.val 0 0 * k.val 1 0 + k.val 0 1 * k.val 1 1 = 0 := by
    have := congrFun (congrFun hk 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e00 : (dg2 (a * b) b * k).val 0 0 = (a : ℝ) * b * k.val 0 0 := by
    simp [dg2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (dg2 (a * b) b * k).val 0 1 = (a : ℝ) * b * k.val 0 1 := by
    simp [dg2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (dg2 (a * b) b * k).val 1 0 = (b : ℝ) * k.val 1 0 := by
    simp [dg2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (dg2 (a * b) b * k).val 1 1 = (b : ℝ) * k.val 1 1 := by
    simp [dg2, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : ((dg2 (a * b) b * k).val).det =
      (a : ℝ) * b * b * (k.val 0 0 * k.val 1 1 - k.val 0 1 * k.val 1 0) := by
    rw [Matrix.det_fin_two, e00, e01, e10, e11]; ring
  by_cases hd : 0 < ((dg2 (a * b) b * k).val).det
  · have h := norm_core (n.natAbs + 1) a b (k.val 0 0) (k.val 0 1) (k.val 1 0) (k.val 1 1)
      _ b.ne_zero h00 h11 h01 hdet hd
    unfold GL2LocalData.WthR
    rw [if_pos hd, e00, e01, e10, e11]
    exact h.le
  · have h0 : GL2LocalData.WthR n (dg2 (a * b) b * k) = 0 := by
      unfold GL2LocalData.WthR
      rw [if_neg hd]
    rw [h0, norm_zero]
    positivity

end GlobalTheory.CompanionTheory.GL2Factorization.NormWth
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_real_whittaker_torus_le : ∀ (n : ℤ) (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ‖GL2LocalData.WthR n (dg2 (a * b) b * k)‖ ≤ |(a : ℝ)| ^ (((n.natAbs + 1 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * |(a : ℝ)|)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.NormWth.norm_WthR_iwasawa_le
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.IwasawaDual

theorem tinvR_mul {n : Type} [Fintype n] [DecidableEq n] (g h : GL n ℝ) :
    GL2LocalData.tinvR (g * h) = GL2LocalData.tinvR g * GL2LocalData.tinvR h := by
  apply Units.ext
  simp [GL2LocalData.tinvR, Matrix.transpose_mul]

theorem tinvR_orth (k : GL (Fin 2) ℝ) (hk : k.val * k.valᵀ = 1) : GL2LocalData.tinvR k = k := by
  have h1 : k.val * (k⁻¹ : GL (Fin 2) ℝ).val = 1 := by
    rw [← Units.val_mul]; simp
  have h2 : (k⁻¹ : GL (Fin 2) ℝ).val = k.valᵀ := by
    have h3 : (k⁻¹ : GL (Fin 2) ℝ).val * k.val = 1 := by
      rw [← Units.val_mul]; simp
    calc (k⁻¹ : GL (Fin 2) ℝ).val = (k⁻¹ : GL (Fin 2) ℝ).val * (k.val * k.valᵀ) := by rw [hk, mul_one]
      _ = k.valᵀ := by rw [← mul_assoc, h3, one_mul]
  apply Units.ext
  show (k⁻¹ : GL (Fin 2) ℝ).valᵀ = k.val
  rw [h2, Matrix.transpose_transpose]

theorem transposeInv_diagonal_real (x y : ℝˣ) : GL2LocalData.tinvR (dg2 x y) = dg2 x⁻¹ y⁻¹ := by
  have h : (dg2 x y)⁻¹ = dg2 x⁻¹ y⁻¹ := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  apply Units.ext
  show ((dg2 x y)⁻¹ : GL (Fin 2) ℝ).valᵀ = _
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem weyl_mul_diagonal_real (x y : ℝˣ) : GL2LocalData.w2R * dg2 x y = dg2 y x * GL2LocalData.w2R := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, GL2LocalData.w2R, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_real_orthogonal : GL2LocalData.w2R.val * GL2LocalData.w2R.valᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GL2LocalData.w2R, Matrix.mul_apply, Fin.sum_univ_two]

theorem iwasawa_dual : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ∃ k' : GL (Fin 2) ℝ, k'.val * k'.valᵀ = 1 ∧ GL2LocalData.w2R * GL2LocalData.tinvR (dg2 (a * b) b * k) = dg2 (a * (a * b)⁻¹) (a * b)⁻¹ * k' := by
  intro a b k hk
  refine ⟨GL2LocalData.w2R * k, ?_, ?_⟩
  · have : (GL2LocalData.w2R * k).val = GL2LocalData.w2R.val * k.val := rfl
    rw [this, Matrix.transpose_mul, mul_assoc, ← mul_assoc k.val, hk, one_mul, weyl_real_orthogonal]
  · have hab : a * (a * b)⁻¹ = b⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [tinvR_mul, tinvR_orth k hk, transposeInv_diagonal_real, hab, ← mul_assoc, weyl_mul_diagonal_real, mul_assoc]

end GlobalTheory.CompanionTheory.GL2Factorization.IwasawaDual
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_transposeInv_iwasawa_real : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ∃ k' : GL (Fin 2) ℝ, k'.val * k'.valᵀ = 1 ∧ GL2LocalData.w2R * GL2LocalData.tinvR (dg2 (a * b) b * k) = dg2 (a * (a * b)⁻¹) (a * b)⁻¹ * k' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.IwasawaDual.iwasawa_dual
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.EmC

theorem emR_coe (h : GL (Fin 2) ℝ) :
    ((GL2LocalData.emR h : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
    have h0 : h.val.det ≠ 0 := (Matrix.isUnits_det_units h).ne_zero
    rw [Matrix.det_fin_two] at h0
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.cons_val_fin_one]
    intro hh
    apply h0
    linarith
  rw [GL2LocalData.emR, dif_pos hd]
  rfl

theorem emR_iwasawa : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 →
    GL2LocalData.emR (dg2 (a * b) b * k) = dg (a * b) b 1 * GL2LocalData.emR k ∧ GL2LocalData.emR k ∈ O3 := by
  intro a b k hk
  constructor
  · apply Units.ext
    rw [Units.val_mul, emR_coe, emR_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dg, dg2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  · have e00 := congrFun (congrFun hk 0) 0
    have e01 := congrFun (congrFun hk 0) 1
    have e10 := congrFun (congrFun hk 1) 0
    have e11 := congrFun (congrFun hk 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply] at e00 e01 e10 e11
    show ((GL2LocalData.emR k : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
      ((GL2LocalData.emR k : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1
    rw [emR_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> simp_all

end GlobalTheory.CompanionTheory.GL2Factorization.EmC
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_iwasawa_real_orthogonal : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → GL2LocalData.emR (dg2 (a * b) b * k) = dg (a * b) b 1 * GL2LocalData.emR k ∧ GL2LocalData.emR k ∈ O3 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.EmC.emR_iwasawa
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section
namespace GlobalTheory.CompanionTheory.GL2Factorization.DualIw

theorem emR_coe (h : GL (Fin 2) ℝ) : (GL2LocalData.emR h).val =
    !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
    have h1 : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) ℝ).det = (h.val).det := by
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  rw [GL2LocalData.emR, dif_pos hd]
  rfl

theorem emR_mul (g h : GL (Fin 2) ℝ) : GL2LocalData.emR (g * h) = GL2LocalData.emR g * GL2LocalData.emR h := by
  apply Units.ext
  rw [Units.val_mul, emR_coe, emR_coe, emR_coe, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem tinvR_mul {n : ℕ} (g h : GL (Fin n) ℝ) : GL2LocalData.tinvR (g * h) = GL2LocalData.tinvR g * GL2LocalData.tinvR h := by
  apply Units.ext
  show ((g * h)⁻¹ : GL (Fin n) ℝ).val.transpose =
    (g⁻¹ : GL (Fin n) ℝ).val.transpose * (h⁻¹ : GL (Fin n) ℝ).val.transpose
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem tinvR_of_orthogonal {n : ℕ} (g : GL (Fin n) ℝ) (hg : g.val * g.valᵀ = 1) :
    GL2LocalData.tinvR g = g := by
  apply Units.ext
  show (g⁻¹ : GL (Fin n) ℝ).val.transpose = g.val
  have h : (g⁻¹ : GL (Fin n) ℝ).val = g.valᵀ := by
    have h1 : (g⁻¹ : GL (Fin n) ℝ).val * g.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel]; rfl
    calc (g⁻¹ : GL (Fin n) ℝ).val = (g⁻¹ : GL (Fin n) ℝ).val * (g.val * g.valᵀ) := by
          rw [hg, Matrix.mul_one]
      _ = g.valᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h, Matrix.transpose_transpose]

theorem emR_orthogonal (k : GL (Fin 2) ℝ) (hk : k.val * k.valᵀ = 1) :
    (GL2LocalData.emR k).val * (GL2LocalData.emR k).valᵀ = 1 := by
  have e : ∀ i j, (k.val * k.valᵀ) i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := fun i j => by rw [hk]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [emR_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]

theorem weyl3_mul_embedding_mem_orthogonal (k : GL (Fin 2) ℝ) (hk : k.val * k.valᵀ = 1) : GL2LocalData.w3R * GL2LocalData.emR k ∈ O3 := by
  have hw : GL2LocalData.w3R.val * GL2LocalData.w3R.valᵀ = 1 := by
    show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) *
      (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  show (GL2LocalData.w3R * GL2LocalData.emR k).val * (GL2LocalData.w3R * GL2LocalData.emR k).valᵀ = 1
  rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (GL2LocalData.emR k).val,
    emR_orthogonal k hk, Matrix.one_mul, hw]

theorem dg_mul_dg (a b c d e f : ℝˣ) :
    (dg a b c : GL (Fin 3) ℝ) * dg d e f = dg (a * d) (b * e) (c * f) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl3_transposeInv_embedding_diagonal (x y : ℝˣ) :
    GL2LocalData.w3R * GL2LocalData.tinvR (GL2LocalData.emR (dg2 x y)) = dg 1 y⁻¹ x⁻¹ * GL2LocalData.w3R := by
  have hinv : (GL2LocalData.emR (dg2 x y))⁻¹ = GL2LocalData.emR (dg2 x⁻¹ y⁻¹) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← emR_mul]
    apply Units.ext
    rw [emR_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2]
  apply Units.ext
  have h : (GL2LocalData.tinvR (GL2LocalData.emR (dg2 x y))).val = (GL2LocalData.emR (dg2 x⁻¹ y⁻¹)).val.transpose := by
    show ((GL2LocalData.emR (dg2 x y))⁻¹ : GL (Fin 3) ℝ).val.transpose = _
    rw [hinv]
  rw [Units.val_mul, Units.val_mul, h, emR_coe]
  show (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) * _ =
    (!![((1 : ℝˣ) : ℝ), 0, 0; 0, ((y⁻¹ : ℝˣ) : ℝ), 0; 0, 0, ((x⁻¹ : ℝˣ) : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ) *
      !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, dg2]

theorem dual_coords : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ∃ o ∈ O3,
    GL2LocalData.w3R * GL2LocalData.tinvR (GL2LocalData.emR (dg2 (a * b) b * k)) =
      dg (a * b)⁻¹ (a * b)⁻¹ (a * b)⁻¹ * (dg (b * a) a 1 * o) := by
  intro a b k hk
  refine ⟨GL2LocalData.w3R * GL2LocalData.emR k, weyl3_mul_embedding_mem_orthogonal k hk, ?_⟩
  have h3 : (a * b)⁻¹ * (b * a) = 1 := by rw [mul_comm b a, inv_mul_cancel]
  have h4 : (a * b)⁻¹ * a = b⁻¹ := by rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [emR_mul, tinvR_mul, tinvR_of_orthogonal _ (emR_orthogonal k hk), ← mul_assoc,
    weyl3_transposeInv_embedding_diagonal, ← mul_assoc, dg_mul_dg, h3, h4, mul_one, mul_assoc]

end GlobalTheory.CompanionTheory.GL2Factorization.DualIw
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl3_transposeInv_embedding_iwasawa : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ∃ o ∈ O3, GL2LocalData.w3R * GL2LocalData.tinvR (GL2LocalData.emR (dg2 (a * b) b * k)) = dg (a * b)⁻¹ (a * b)⁻¹ (a * b)⁻¹ * (dg (b * a) a 1 * o) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.DualIw.dual_coords
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization

theorem smoothR_continuous : ∀ W : GL (Fin 3) ℝ → ℂ, SmoothR W → Continuous W := by
  intro W hW
  have hc : ContinuousOn (ext W) {m : M3 | (Matrix.of m).det ≠ 0} := hW.continuousOn
  have hv : Continuous fun g : GL (Fin 3) ℝ => (Matrix.of.symm g.val : M3) :=
    (Units.continuous_val : Continuous fun g : GL (Fin 3) ℝ => (g.val : Matrix (Fin 3) (Fin 3) ℝ))
  have hm : ∀ g : GL (Fin 3) ℝ, (Matrix.of.symm g.val : M3) ∈ {m : M3 | (Matrix.of m).det ≠ 0} := by
    intro g
    have : (g.val).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    simpa using this
  have he : W = fun g => ext W (Matrix.of.symm g.val : M3) := by
    funext g
    have h : (Matrix.of (Matrix.of.symm g.val : M3)).det ≠ 0 := hm g
    rw [Ad3.ext, dif_pos h]
    congr 1
    apply Units.ext
    simp
  rw [he]
  exact hc.comp_continuous hv hm

end GlobalTheory.CompanionTheory.GL2Factorization
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_smooth_real_GL3 : ∀ W : GL (Fin 3) ℝ → ℂ, SmoothR W → Continuous W := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.smoothR_continuous
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.EmRCont

theorem val_emR (h : GL (Fin 2) ℝ) :
    ((GL2LocalData.emR h : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := by
  have hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
    have h0 : h.val.det ≠ 0 := (Matrix.isUnits_det_units h).ne_zero
    rw [Matrix.det_fin_two] at h0
    rw [Matrix.det_fin_three]
    simp
    intro hh
    apply h0
    linarith
  unfold GL2LocalData.emR
  rw [dif_pos hd]
  rfl

theorem emR_mul (g h : GL (Fin 2) ℝ) : GL2LocalData.emR (g * h) = GL2LocalData.emR g * GL2LocalData.emR h := by
  apply Units.ext
  rw [Units.val_mul, val_emR, val_emR, val_emR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Units.val_mul]

theorem emR_one : GL2LocalData.emR (1 : GL (Fin 2) ℝ) = 1 := by
  apply Units.ext
  rw [val_emR]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem emR_inv (g : GL (Fin 2) ℝ) : GL2LocalData.emR g⁻¹ = (GL2LocalData.emR g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← emR_mul, inv_mul_cancel, emR_one])

theorem continuous_emR_val : Continuous fun h : GL (Fin 2) ℝ => (GL2LocalData.emR h).val := by
  have c : ∀ i j, Continuous fun h : GL (Fin 2) ℝ => h.val i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have e : (fun h : GL (Fin 2) ℝ => (GL2LocalData.emR h).val) = fun h =>
      !![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] := funext val_emR
  rw [e]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> first | exact c _ _ | exact continuous_const

theorem continuous_emR : Continuous GL2LocalData.emR := by
  refine Units.continuous_iff.2 ⟨continuous_emR_val, ?_⟩
  have e : (fun h : GL (Fin 2) ℝ => (((GL2LocalData.emR h)⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) =
      (fun h : GL (Fin 2) ℝ => (GL2LocalData.emR h).val) ∘ fun h => h⁻¹ := by
    funext h
    simp only [Function.comp, emR_inv]
  rw [e]
  exact continuous_emR_val.comp continuous_inv

end GlobalTheory.CompanionTheory.GL2Factorization.EmRCont
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_real_embedding_GL3 : Continuous GL2LocalData.emR := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.EmRCont.continuous_emR
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.CtIn

theorem continuous_tinvR (m : ℕ) : Continuous (GL2LocalData.tinvR : GL (Fin m) ℝ → GL (Fin m) ℝ) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous (fun g : GL (Fin m) ℝ => ((g⁻¹ : GL (Fin m) ℝ).val)ᵀ)
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · show Continuous (fun g : GL (Fin m) ℝ => (g.val)ᵀ)
    exact Units.continuous_val.matrix_transpose

theorem tinvR_continuous : ∀ m : ℕ, Continuous (GL2LocalData.tinvR : GL (Fin m) ℝ → GL (Fin m) ℝ) :=
  continuous_tinvR

end GlobalTheory.CompanionTheory.GL2Factorization.CtIn
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_real_transposeInv : ∀ m : ℕ, Continuous (GL2LocalData.tinvR : GL (Fin m) ℝ → GL (Fin m) ℝ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.CtIn.tinvR_continuous
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord

theorem continuous_diagonal_real_torus :
    Continuous (fun q : ℝˣ × ℝˣ => (dg2 q.1 q.2 : GL (Fin 2) ℝ)) := by
  have hv1 : Continuous (fun q : ℝˣ × ℝˣ => (q.1 : ℝ)) := Units.continuous_val.comp continuous_fst
  have hv2 : Continuous (fun q : ℝˣ × ℝˣ => (q.2 : ℝ)) := Units.continuous_val.comp continuous_snd
  have hi1 : Continuous (fun q : ℝˣ × ℝˣ => ((q.1⁻¹ : ℝˣ) : ℝ)) :=
    (Units.continuous_iff.1 continuous_id).2.comp continuous_fst
  have hi2 : Continuous (fun q : ℝˣ × ℝˣ => ((q.2⁻¹ : ℝˣ) : ℝ)) :=
    (Units.continuous_iff.1 continuous_id).2.comp continuous_snd
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : ℝˣ × ℝˣ => (!![(q.1 : ℝ), 0; 0, (q.2 : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) i j
    fin_cases i <;> fin_cases j <;>
      first | (simpa using hv1) | (simpa using hv2) | (simpa using continuous_const)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : ℝˣ × ℝˣ =>
      (!![((q.1⁻¹ : ℝˣ) : ℝ), 0; 0, ((q.2⁻¹ : ℝˣ) : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) i j
    fin_cases i <;> fin_cases j <;>
      first | (simpa using hi1) | (simpa using hi2) | (simpa using continuous_const)

theorem continuous_iwasawa_coord :
    Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => dg2 (p.1 * p.2.1) p.2.1 * p.2.2) := by
  have h : Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => ((p.1 * p.2.1, p.2.1) : ℝˣ × ℝˣ)) :=
    (continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.comp continuous_snd)
  exact (continuous_diagonal_real_torus.comp h).mul (continuous_snd.comp continuous_snd)

end GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_iwasawa_real_parametrization : Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => dg2 (p.1 * p.2.1) p.2.1 * p.2.2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.IwasawaCoord.continuous_iwasawa_coord
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.OrthParam

theorem rot_det_ne (θ : ℝ) : !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ].det ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith

theorem rot_val (θ : ℝ) :
    (GL2LocalData.rotR θ : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  simp only [GL2LocalData.rotR, dif_pos (rot_det_ne θ)]
  rfl

theorem rot_inv_val (θ : ℝ) :
    (((GL2LocalData.rotR θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [rot_val]
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

theorem continuous_rot : Continuous GL2LocalData.rotR := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ GL2LocalData.rotR : ℝ → Matrix (Fin 2) (Fin 2) ℝ) =
        fun θ => !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := funext rot_val
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have hc : Continuous fun θ : ℝ =>
        (!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ) := by
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    exact hc.congr fun θ => (rot_inv_val θ).symm

theorem rot_orth (θ : ℝ) : (GL2LocalData.rotR θ).val * (GL2LocalData.rotR θ).valᵀ = 1 := by
  rw [rot_val]
  have h := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> nlinarith

theorem kR_continuous_orthogonal :
    ∀ ε : Bool, Continuous (fun θ : ℝ => GL2LocalData.kR θ ε) ∧
      ∀ θ : ℝ, (GL2LocalData.kR θ ε).val * (GL2LocalData.kR θ ε).valᵀ = 1 := by
  intro ε
  refine ⟨?_, fun θ => ?_⟩
  · unfold GL2LocalData.kR
    exact continuous_rot.mul continuous_const
  · have hr := rot_orth θ
    cases ε
    · simpa [GL2LocalData.kR] using hr
    · have hd : ((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
          ((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      simp only [GL2LocalData.kR, if_true, Units.val_mul, Matrix.transpose_mul]
      calc _ = (GL2LocalData.rotR θ).val * (((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
              ((dg2 (1 : ℝˣ) (-1) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) * (GL2LocalData.rotR θ).valᵀ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hd, Matrix.mul_one, hr]

end GlobalTheory.CompanionTheory.GL2Factorization.OrthParam
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_real_rotation_orthogonal : ∀ ε : Bool, Continuous (fun θ : ℝ => GL2LocalData.kR θ ε) ∧ ∀ θ : ℝ, (GL2LocalData.kR θ ε).val * (GL2LocalData.kR θ ε).valᵀ = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.OrthParam.kR_continuous_orthogonal
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization

theorem integrable_mIwR_of_product_bound :
    ∀ (F : ℝˣ × ℝˣ × ℝ → ℂ) (C p q N : ℝ), AEStronglyMeasurable F GL2LocalData.mIwR → 0 < p → 0 < q → p < N → q < N → (∀ (a b : ℝˣ) (θ : ℝ), ‖F (a, b, θ)‖ ≤ C * (|(a : ℝ)| ^ p * (1 + |(a : ℝ)|) ^ (-N)) * (|(b : ℝ)| ^ q * (1 + |(b : ℝ)|) ^ (-N))) → Integrable F GL2LocalData.mIwR := by
  intro F C p q N hF hp hq hpN hqN hb
  have h1 := GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_abs_rpow_mul_one_add_rpow_neg p N hp hpN
  have h2 := GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_abs_rpow_mul_one_add_rpow_neg q N hq hqN
  have h3 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    integrable_const _
  have h4 := h2.mul_prod h3
  have h5 := h1.mul_prod h4
  have h6 := h5.const_mul C
  refine Integrable.mono' (g := _) h6 hF ?_
  refine Filter.Eventually.of_forall ?_
  rintro ⟨a, b, θ⟩
  refine (hb a b θ).trans (le_of_eq ?_)
  simp only [mul_one]
  ring

end GlobalTheory.CompanionTheory.GL2Factorization
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_iwasawa_real_of_decay : ∀ (F : ℝˣ × ℝˣ × ℝ → ℂ) (C p q N : ℝ), AEStronglyMeasurable F GL2LocalData.mIwR → 0 < p → 0 < q → p < N → q < N → (∀ (a b : ℝˣ) (θ : ℝ), ‖F (a, b, θ)‖ ≤ C * (|(a : ℝ)| ^ p * (1 + |(a : ℝ)|) ^ (-N)) * (|(b : ℝ)| ^ q * (1 + |(b : ℝ)|) ^ (-N))) → Integrable F GL2LocalData.mIwR := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.integrable_mIwR_of_product_bound
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization

theorem real_integrand_norm_le_ptw : ∀ (x₃ x₂ s : ℂ) (A B C m : ℝ) (T N : ℕ), 0 < A → 0 < B → ‖x₃‖ ≤ C / (A * B) ^ T / ((1 + A) * (1 + B)) ^ N → ‖x₂‖ ≤ A ^ m → ‖x₃ * x₂ * ((A : ℂ) ^ (s - 3 / 2)) * ((B : ℂ) ^ (2 * s - 1))‖ ≤ C * (A ^ (s.re - 3 / 2 + m - T) * (1 + A) ^ (-(N : ℝ))) * (B ^ (2 * s.re - 1 - T) * (1 + B) ^ (-(N : ℝ))) := by
  intro x₃ x₂ s A B C m T N hA hB h3 h2
  have hA1 : 0 < 1 + A := by linarith
  have hB1 : 0 < 1 + B := by linarith
  have e1 : ‖(A : ℂ) ^ (s - 3 / 2)‖ = A ^ (s.re - 3 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    simp
  have e2 : ‖(B : ℂ) ^ (2 * s - 1)‖ = B ^ (2 * s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hB]
    simp
  have key : ‖x₃‖ * ‖x₂‖ ≤ (C / (A * B) ^ T / ((1 + A) * (1 + B)) ^ N) * A ^ m :=
    mul_le_mul h3 h2 (norm_nonneg _) ((norm_nonneg _).trans h3)
  have hP : 0 ≤ A ^ (s.re - 3 / 2) * B ^ (2 * s.re - 1) :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
  have hR : C * (A ^ (s.re - 3 / 2 + m - T) * (1 + A) ^ (-(N : ℝ))) *
      (B ^ (2 * s.re - 1 - T) * (1 + B) ^ (-(N : ℝ))) =
      (C / (A * B) ^ T / ((1 + A) * (1 + B)) ^ N) * A ^ m *
        (A ^ (s.re - 3 / 2) * B ^ (2 * s.re - 1)) := by
    rw [Real.rpow_sub hA, Real.rpow_add hA, Real.rpow_sub hB, Real.rpow_neg hA1.le,
      Real.rpow_neg hB1.le, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast,
      Real.rpow_natCast, mul_pow, mul_pow]
    field_simp
  rw [norm_mul, norm_mul, norm_mul, e1, e2, hR, mul_assoc (‖x₃‖ * ‖x₂‖)]
  exact mul_le_mul_of_nonneg_right key hP

end GlobalTheory.CompanionTheory.GL2Factorization
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_zeta_integrand_decay_bound : ∀ (x₃ x₂ s : ℂ) (A B C m : ℝ) (T N : ℕ), 0 < A → 0 < B → ‖x₃‖ ≤ C / (A * B) ^ T / ((1 + A) * (1 + B)) ^ N → ‖x₂‖ ≤ A ^ m → ‖x₃ * x₂ * ((A : ℂ) ^ (s - 3 / 2)) * ((B : ℂ) ^ (2 * s - 1))‖ ≤ C * (A ^ (s.re - 3 / 2 + m - T) * (1 + A) ^ (-(N : ℝ))) * (B ^ (2 * s.re - 1 - T) * (1 + B) ^ (-(N : ℝ))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GL2Factorization.real_integrand_norm_le_ptw
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.RealPlace

abbrev mE (n : ℤ) : ℝ := ((n.natAbs + 1 : ℕ) : ℝ) / 2

theorem cont_chR (s : ℂ) : Continuous (chR false s) := by
  have h : Continuous (fun a : ℝˣ => (((|(a : ℝ)| : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp (Units.continuous_val.abs)
  have h2 : Continuous (fun a : ℝˣ => (((|(a : ℝ)| : ℝ)) : ℂ) ^ s) := by
    refine h.cpow continuous_const fun a => Or.inl ?_
    simpa using a.ne_zero
  have e : chR false s = fun a : ℝˣ => (((|(a : ℝ)| : ℝ)) : ℂ) ^ s := by
    funext a
    simp [chR]
  rw [e]
  exact h2

theorem cont_rI {W₃ : GL (Fin 3) ℝ → ℂ} {W₂ : GL (Fin 2) ℝ → ℂ} (c3 : Continuous W₃) (c2 : Continuous W₂) (s : ℂ) :
    Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => rI W₃ W₂ s p.1 p.2.1 p.2.2) := by
  unfold rI
  have h := GlobalTheory.T.continuous_iwasawa_real_parametrization
  have h1 : Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => p.1) := continuous_fst
  have h2 : Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => p.2.1) := continuous_snd.fst
  exact (((c3.comp (GlobalTheory.T.continuous_real_embedding_GL3.comp h)).mul (c2.comp h)).mul ((cont_chR _).comp h1)).mul ((cont_chR _).comp h2)

theorem cont_iwR {W₃ : GL (Fin 3) ℝ → ℂ} {W₂ : GL (Fin 2) ℝ → ℂ} (c3 : Continuous W₃) (c2 : Continuous W₂)
    (s : ℂ) (ε : Bool) : Continuous (GL2LocalData.iwR W₃ W₂ s ε) := by
  have h : Continuous (fun p : ℝˣ × ℝˣ × ℝ => ((p.1, p.2.1, GL2LocalData.kR p.2.2 ε) : ℝˣ × ℝˣ × GL (Fin 2) ℝ)) :=
    continuous_fst.prodMk (continuous_snd.fst.prodMk ((GlobalTheory.T.continuous_real_rotation_orthogonal ε).1.comp continuous_snd.snd))
  have h2 := (cont_rI c3 c2 s).comp h
  have e : GL2LocalData.iwR W₃ W₂ s ε = (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => rI W₃ W₂ s p.1 p.2.1 p.2.2) ∘
      (fun p : ℝˣ × ℝˣ × ℝ => ((p.1, p.2.1, GL2LocalData.kR p.2.2 ε) : ℝˣ × ℝˣ × GL (Fin 2) ℝ)) := by
    funext p
    simp only [GL2LocalData.iwR, rI, Function.comp]
  rw [e]
  exact h2

theorem int_core (W₃ : GL (Fin 3) ℝ → ℂ) (W₂ : GL (Fin 2) ℝ → ℂ) (c3 : Continuous W₃) (c2 : Continuous W₂)
    (T : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (h3 : ∀ N : ℕ, ∃ C : ℝ, ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 →
      ‖W₃ (GL2LocalData.emR (dg2 (a * b) b * k))‖ ≤
        C / (|(a : ℝ)| * |(b : ℝ)|) ^ T / ((1 + |(a : ℝ)|) * (1 + |(b : ℝ)|)) ^ N)
    (h2 : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ‖W₂ (dg2 (a * b) b * k)‖ ≤ |(a : ℝ)| ^ m)
    (s : ℂ) (hs : (T : ℝ) + 3 < s.re) (ε : Bool) : Integrable (GL2LocalData.iwR W₃ W₂ s ε) GL2LocalData.mIwR := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (s.re - 3 / 2 + m - T) (2 * s.re - 1 - T))
  have hN1 : s.re - 3 / 2 + m - T < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 2 * s.re - 1 - T < N := lt_of_le_of_lt (le_max_right _ _) hN
  obtain ⟨C, hC⟩ := h3 N
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  refine GlobalTheory.T.integrable_iwasawa_real_of_decay _ C (s.re - 3 / 2 + m - T) (2 * s.re - 1 - T) N (cont_iwR c3 c2 s ε).aestronglyMeasurable
    (by linarith) (by linarith) hN1 hN2 ?_
  intro a b θ
  have ha : 0 < |(a : ℝ)| := abs_pos.2 a.ne_zero
  have hb : 0 < |(b : ℝ)| := abs_pos.2 b.ne_zero
  have ho := (GlobalTheory.T.continuous_real_rotation_orthogonal ε).2 θ
  have := GlobalTheory.T.norm_zeta_integrand_decay_bound (W₃ (GL2LocalData.emR (dg2 (a * b) b * GL2LocalData.kR θ ε))) (W₂ (dg2 (a * b) b * GL2LocalData.kR θ ε)) s
    |(a : ℝ)| |(b : ℝ)| C m T N ha hb (hC a b _ ho) (h2 a b _ ho)
  simpa [GL2LocalData.iwR, chR] using this

theorem cont_thR (n : ℤ) (t : ℝ) : Continuous (thR n t) := by
  have hd : Continuous (fun g : GL (Fin 2) ℝ => |(g.val).det|) :=
    (Continuous.matrix_det Units.continuous_val).abs
  have hd' : Continuous (fun g : GL (Fin 2) ℝ => (((|(g.val).det| : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp hd
  unfold thR
  refine (GlobalTheory.T.continuous_real_whittaker n).mul (hd'.cpow continuous_const ?_)
  intro g
  refine Or.inl ?_
  simpa using (g.det.ne_zero)

theorem norm_thR_le (n : ℤ) (t : ℝ) (a b : ℝˣ) (k : GL (Fin 2) ℝ) (hk : k.val * k.valᵀ = 1) :
    ‖thR n t (dg2 (a * b) b * k)‖ ≤ |(a : ℝ)| ^ mE n := by
  have hdet : 0 < |((dg2 (a * b) b * k).val).det| := abs_pos.2 ((dg2 (a * b) b * k).det.ne_zero)
  unfold thR
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hdet]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, Real.rpow_zero, mul_one]
  refine (GlobalTheory.T.norm_real_whittaker_torus_le n a b k hk).trans ?_
  have h1 : Real.exp (-(2 * Real.pi * |(a : ℝ)|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h0 := abs_nonneg (a : ℝ)
    have hp := Real.pi_pos
    nlinarith [mul_nonneg hp.le h0]
  exact mul_le_of_le_one_right (by positivity) h1

theorem main : ∀ (k : ℕ) (V : Submodule ℂ (GL (Fin 3) ℝ → ℂ)) (E : Fin 3 → Fin 3 → Module.End ℂ V), WhR k V E → ∀ W ∈ V, ∀ (n : ℤ) (t : ℝ),
  (∀ s : ℂ, Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => rI W (thR n t) s p.1 p.2.1 p.2.2) ∧
    Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => rI (GL2LocalData.dW3R W) (GL2LocalData.dW2R (thR n t)) s p.1 p.2.1 p.2.2)) ∧
  ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ ε : Bool, Integrable (GL2LocalData.iwR W (thR n t) s ε) GL2LocalData.mIwR ∧
    Integrable (GL2LocalData.iwR (GL2LocalData.dW3R W) (GL2LocalData.dW2R (thR n t)) s ε) GL2LocalData.mIwR := by
  intro k V E h W hW n t
  have cW : Continuous W := GlobalTheory.T.continuous_of_smooth_real_GL3 W (h.smooth W hW)
  have cT : Continuous (thR n t) := cont_thR n t
  have cW' : Continuous (GL2LocalData.dW3R W) := by
    unfold GL2LocalData.dW3R
    exact cW.comp (continuous_const.mul (GlobalTheory.T.continuous_real_transposeInv 3))
  have cT' : Continuous (GL2LocalData.dW2R (thR n t)) := by
    unfold GL2LocalData.dW2R
    exact cT.comp (continuous_const.mul (GlobalTheory.T.continuous_real_transposeInv 2))
  refine ⟨fun s => ⟨cont_rI cW cT s, cont_rI cW' cT' s⟩, ?_⟩
  obtain ⟨T, hT⟩ := h.gauge W hW
  have hm : 0 ≤ mE n := by unfold mE; positivity
  refine ⟨(T : ℝ) + 3, fun s hs ε => ⟨?_, ?_⟩⟩
  · refine int_core W (thR n t) cW cT T (mE n) hm ?_ (fun a b k hk => norm_thR_le n t a b k hk) s hs ε
    intro N
    obtain ⟨C, hC⟩ := hT N
    refine ⟨C, fun a b k hk => ?_⟩
    obtain ⟨e1, e2⟩ := GlobalTheory.T.embedding_iwasawa_real_orthogonal a b k hk
    rw [e1]
    exact hC a b _ e2
  · refine int_core _ _ cW' cT' T (mE n) hm ?_ ?_ s hs ε
    · intro N
      obtain ⟨C, hC⟩ := hT N
      refine ⟨C, fun a b k hk => ?_⟩
      obtain ⟨o, ho, e⟩ := GlobalTheory.T.weyl3_transposeInv_embedding_iwasawa a b k hk
      have e' : GL2LocalData.dW3R W (GL2LocalData.emR (dg2 (a * b) b * k)) = W (dg (b * a) a 1 * o) := by
        unfold GL2LocalData.dW3R
        rw [e, h.cen W hW]
      rw [e']
      have := hC b a o ho
      rw [mul_comm |(b : ℝ)| |(a : ℝ)|, mul_comm (1 + |(b : ℝ)|) (1 + |(a : ℝ)|)] at this
      exact this
    · intro a b k hk
      obtain ⟨k', hk', e⟩ := GlobalTheory.T.weyl_transposeInv_iwasawa_real a b k hk
      unfold GL2LocalData.dW2R
      rw [e]
      exact norm_thR_le n t a _ k' hk'

end GlobalTheory.CompanionTheory.GL2Factorization.RealPlace
end
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.WCont

variable {K : Type} [Field K] [NumberField K]

theorem isUnit1_localChar (c : HeckeCharacter K) (w : PlK K) : IsUnit1 (localChar c w) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩

theorem isUnit1_cAt (c : HeckeCharacter K) (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] :
    IsUnit1 (cAt c v w) :=
  ⟨(isUnit1_localChar c w).1.comp (Continuous.units_map _ (_root_.continuous_algebraMap (Qv v) (Kv K w))),
    fun x => (isUnit1_localChar c w).2 _⟩

end GlobalTheory.CompanionTheory.WCont
end
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.UnrTorus

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mem_integers_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  have hset : ({x : F | x ∈ 𝒪[F]} : Set F) = (valBall F 0 : Set F) := by
    rw [coe_valBall_zero]; rfl
  have h0 := mem_valBall_iff_le_ord (K := F) (n := 0) hx
  rw [← h0]
  exact Set.ext_iff.1 hset x

theorem modulus_eq_zpow {x : F} (hx : x ≠ 0) :
    (modulus x : ℝ) = (residueCard F : ℝ) ^ (-ord x) := by
  rw [modulus_of_ne_zero hx]
  push_cast
  rfl

theorem succ_le_modulus_inv {x : F} (hx : x ≠ 0) {n : ℕ} (hn : ord x = n) :
    (n : ℝ) + 1 ≤ (modulus x : ℝ)⁻¹ := by
  have hq : (2 : ℝ) ≤ (residueCard F : ℝ) := by
    exact_mod_cast (one_lt_residueCard (K := F))
  rw [modulus_eq_zpow hx, hn, zpow_neg, inv_inv, zpow_natCast]
  calc (n : ℝ) + 1 ≤ 2 ^ n := by
        exact_mod_cast Nat.lt_two_pow_self (n := n)
    _ ≤ (residueCard F : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) hq n

variable [MeasurableSpace F] [BorelSpace F]

theorem split_bound (χ : AddChar F Circle) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (a : Fˣ) :
    ‖GL2LocalData.WcS χ c₁ c₂ (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1) (dg2 a 1)‖ ≤
                 (modulus (a : F) : ℝ)⁻¹ ∧
      (GL2LocalData.WcS χ c₁ c₂ (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1) (dg2 a 1) ≠ 0 →
        (modulus (a : F) : ℝ) ≤ 1) := by
  set Ψ : F × F → ℂ := Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1 with hΨ
  set f : Fˣ → ℂ := fun u => Ψ (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) *
    (((c₂ u)⁻¹ : ℂˣ) : ℂ) with hf
  have hpos : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have hmp : ‖mp a (1 / 2)‖ = (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) := by
    simp only [mp]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    norm_num
  have hW : GL2LocalData.WcS χ c₁ c₂ Ψ (dg2 a 1) = ((c₁ a : ℂˣ) : ℂ) * mp a (1 / 2) * ∫ u, f u ∂multHaar F :=
    GlobalTheory.CompanionTheory.SplitBound.wcS_diag χ c₁ c₂ Ψ a
  have hsupp : ∀ u : Fˣ, f u ≠ 0 → ord (u : F) ≤ 0 ∧ 0 ≤ ord (u : F) + ord (a : F) := by
    intro u hu
    have h0 : Ψ (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) ≠ 0 := fun h0 => hu (by simp only [hf]; rw [h0]; simp)
    have hm : (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} := by
      by_contra hn
      exact h0 (Set.indicator_of_notMem hn _)
    obtain ⟨m1, m2⟩ := hm
    have e1 := (mem_integers_iff_ord (u * a).ne_zero).1 m1
    have e2 := (mem_integers_iff_ord (u⁻¹).ne_zero).1 m2
    rw [ord_units_mul] at e1
    rw [ord_units_inv] at e2
    exact ⟨by omega, e1⟩
  have hnf : ∀ u, ‖f u‖ ≤ 1 := fun u => by
    have e2 : ‖(((c₂ u)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, h₂.2 u, inv_one]
    simp only [hf, norm_mul, h₁.2 u, e2, mul_one]
    by_cases hm : (((u * a : Fˣ) : F), ((u⁻¹ : Fˣ) : F)) ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]}
    · simp only [hΨ]
      rw [Set.indicator_of_mem hm]
      simp
    · simp only [hΨ]
      rw [Set.indicator_of_notMem hm]
      simp
  by_cases hm : 0 ≤ ord (a : F)
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm
    have hle : (modulus (a : F) : ℝ) ≤ 1 := by
      have : (a : F) ∈ 𝒪[F] := (mem_integers_iff_ord a.ne_zero).2 hm
      exact_mod_cast modulus_le_one_iff.2 this
    refine ⟨?_, fun _ => hle⟩
    set S : Set Fˣ := ⋃ i ∈ Finset.range (n + 1), ordShell F (-(i : ℤ)) with hS
    have hμ : multHaar F S ≤ ((n + 1 : ℕ) : ENNReal) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      simp [multHaar_ordShell]
    have hμ' : multHaar F S < ⊤ := hμ.trans_lt (ENNReal.natCast_lt_top _)
    have hreal : (multHaar F).real S ≤ (n : ℝ) + 1 := by
      have h := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hμ
      rw [ENNReal.toReal_natCast] at h
      rw [measureReal_def]
      push_cast at h
      exact h
    have hz : ∀ u ∉ S, f u = 0 := by
      intro u hu
      by_contra hne
      obtain ⟨b1, b2⟩ := hsupp u hne
      refine hu ?_
      simp only [hS, Set.mem_iUnion]
      refine ⟨(-ord (u : F)).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · simp only [mem_ordShell]
        omega
    have hI : ‖∫ u, f u ∂multHaar F‖ ≤ (n : ℝ) + 1 := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
      refine (norm_setIntegral_le_of_norm_le_const hμ' (fun u _ => hnf u)).trans ?_
      simpa using hreal
    rw [hW, norm_mul, norm_mul, h₁.2 a, one_mul, hmp]
    have hr : (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one hpos.le hle (by norm_num)
    calc (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) * ‖∫ u, f u ∂multHaar F‖
        ≤ 1 * ((n : ℝ) + 1) := mul_le_mul hr hI (norm_nonneg _) zero_le_one
      _ = (n : ℝ) + 1 := one_mul _
      _ ≤ _ := succ_le_modulus_inv a.ne_zero hn
  · have hzero : ∀ u, f u = 0 := by
      intro u
      by_contra hne
      obtain ⟨b1, b2⟩ := hsupp u hne
      omega
    have hW0 : GL2LocalData.WcS χ c₁ c₂ Ψ (dg2 a 1) = 0 := by
      rw [hW]
      simp [funext hzero]
    rw [hW0]
    exact ⟨by simpa using (inv_pos.2 hpos).le, fun h => absurd rfl h⟩

end Local

section Field

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [Algebra F E]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] in
theorem nsg_one_field : GL2LocalData.nsg E (1 : F) = 1 := by
  unfold GL2LocalData.nsg
  rw [if_pos]
  exact ⟨1, by simp⟩

theorem field_bound (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) {c : Eˣ →* ℂˣ}
    (hc : IsUnit1 c) (hmod : ∀ x : E, (modulus x : ℝ) = modulus (Algebra.norm F x)) (a : Fˣ) :
    ‖GL2LocalData.Wc χ σ μE lam c (Set.indicator {x : E | x ∈ 𝒪[E]} 1) (dg2 a 1)‖ ≤ (modulus (a : F) : ℝ)⁻¹ ∧
      (GL2LocalData.Wc χ σ μE lam c (Set.indicator {x : E | x ∈ 𝒪[E]} 1) (dg2 a 1) ≠ 0 →
        (modulus (a : F) : ℝ) ≤ 1) := by
  classical
  set Φ : E → ℂ := Set.indicator {x : E | x ∈ 𝒪[E]} 1 with hΦ
  have hpos : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have hdet : ((dg2 a 1 : GL (Fin 2) F).val).det = a := by
    simp [dg2, Matrix.det_fin_two]
  have h00 : (dg2 a 1 : GL (Fin 2) F).val 0 0 = a := by simp [dg2]
  have h01 : (dg2 a 1 : GL (Fin 2) F).val 0 1 = 0 := by simp [dg2]
  have h10 : (dg2 a 1 : GL (Fin 2) F).val 1 0 = 0 := by simp [dg2]
  have h11 : (dg2 a 1 : GL (Fin 2) F).val 1 1 = 1 := by simp [dg2]
  have key : ∀ w : ℂ, w = GL2LocalData.Wc χ σ μE lam c Φ (dg2 a 1) → w = 0 ∨
      ((modulus (a : F) : ℝ) ≤ 1 ∧ ‖w‖ ≤ 1) := by
    rintro w rfl
    unfold GL2LocalData.Wc
    rw [hdet, h00, h01, h10, h11]
    by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)
    · rw [dif_pos h]
      set t : Eˣ := h.choose with ht
      have htN : Algebra.norm F (t : E) = (a : F) := h.choose_spec
      have ha : (a : F) / a = 1 := div_self a.ne_zero
      simp only [GL2LocalData.rW, ha, zero_div, if_true, nsg_one_field]
      by_cases hm : (t : E) ∈ 𝒪[E]
      · right
        have hle : (modulus (a : F) : ℝ) ≤ 1 := by
          rw [← htN, ← hmod]
          exact_mod_cast modulus_le_one_iff.2 hm
        refine ⟨hle, ?_⟩
        have hv : Φ (algebraMap F E 1 * 1 * (t : E)) = 1 := by
          simp only [map_one, mul_one, one_mul, hΦ]
          exact Set.indicator_of_mem (s := {x : E | x ∈ 𝒪[E]}) hm _
        rw [hv]
        simp only [norm_mul, hc.2 t, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        simpa using Real.rpow_le_one hpos.le hle (by norm_num : (0:ℝ) ≤ 1 / 2)
      · left
        have hv : Φ (algebraMap F E 1 * 1 * (t : E)) = 0 := by
          simp only [map_one, mul_one, one_mul, hΦ]
          exact Set.indicator_of_notMem (s := {x : E | x ∈ 𝒪[E]}) hm _
        rw [hv]
        simp
    · rw [dif_neg h]
      exact Or.inl rfl
  rcases key _ rfl with h0 | ⟨hle, hn⟩
  · rw [h0]
    exact ⟨by simpa using (inv_pos.2 hpos).le, fun h => absurd rfl h⟩
  · exact ⟨hn.trans ((one_le_inv₀ hpos).2 hle), fun _ => hle⟩

end Field

theorem main : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → m.std → Unr c v →
  ∀ y : (Qv v)ˣ, ‖m.W (dg2 y 1)‖ ≤ ‖(y : Qv v)‖⁻¹ ∧ (m.W (dg2 y 1) ≠ 0 → ‖(y : Qv v)‖ ≤ 1) := by
  intro K _ _ h2 c v m hok hstd hU y
  have hn : (modulus (y : Qv v) : ℝ) = ‖(y : Qv v)‖ :=
    GroundTheory.Automorphic.GodementSection.modulus_adicCompletion v (y : Qv v)
  rw [← hn]
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    haveI := i₁
    haveI := i₂
    obtain rfl : Φ = _ := hstd
    exact split_bound (GP.psiF v)⁻¹ (GlobalTheory.CompanionTheory.WCont.isUnit1_cAt c v w₁) (GlobalTheory.CompanionTheory.WCont.isUnit1_cAt c v w₂) y
  | @ns w i σ η Φ =>
    haveI := i
    obtain rfl : Φ = _ := hstd
    obtain ⟨hu, hσ, hη, -⟩ := hok
    have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
    obtain ⟨hχc, hχ1, -⟩ :=
      (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
    have hf : Module.finrank (Qv v) (Kv K w) = 2 :=
      GlobalTheory.CompanionTheory.StdThetaExists.finrank_eq_two_of_unique h2 v w hu
    have hcont : Continuous (algebraMap (Qv v) (Kv K w)) := continuous_adicCompletionMap v w
    have hWm := GlobalTheory.CompanionTheory.NormModulus.wMod (Qv v) _ hχc hχ1 (Kv K w) hf hcont σ hσ η hη
    exact field_bound (GP.psiF v)⁻¹ σ _ _ (GlobalTheory.CompanionTheory.WCont.isUnit1_localChar c w) hWm y

end GlobalTheory.CompanionTheory.UnrTorus
end
end
