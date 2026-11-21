import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartBounds
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartGradient
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshMean
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagMean
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartLowerHeightsound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartPotentialPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspCoordinateBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspCovolume
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspLeadingMinima
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspShortVectors
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspTimeDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramEntryDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramPivotProduct
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramContinuous
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramSubmean
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PMatrixDetDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPeriodGramPosDef
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPeriodLatticeCovolume
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotBounds
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotProductBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PSchurDetBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PUnimodularLast

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace MCChartFrameDeriv

theorem le_one_add_sum {g r : ℕ} (A : Fin g → Fin r → ℝ) (hA : ∀ j l, 0 < A j l) (j : Fin g)
    (l : Fin r) : A j l ≤ 1 + ∑ j', ∑ l', A j' l' := by
  have h1 : A j l ≤ ∑ l', A j l' :=
    Finset.single_le_sum (f := fun l' => A j l') (fun l' _ => (hA j l').le) (Finset.mem_univ l)
  have h2 : ∑ l', A j l' ≤ ∑ j', ∑ l', A j' l' :=
    Finset.single_le_sum (f := fun j' => ∑ l', A j' l')
      (fun j' _ => Finset.sum_nonneg fun l' _ => (hA j' l').le) (Finset.mem_univ j)
  linarith

end MCChartFrameDeriv

open MCChartFrameDeriv in

theorem ChartFrameDeriv.proof (h₁ : AnalyticDerivBound.Statement) : ChartFrameDeriv.Statement := by
  intro D
  have hU : IsOpen (D.U ×ˢ D.V) := D.isOpen_U.prod D.isOpen_V
  have hex : ∀ j l, ∃ A : ℝ, 0 < A ∧ ∀ x ∈ D.K,
      DifferentiableAt ℝ (fun q => D.f q j l) x ∧ ‖D.f x j l‖ ≤ A ∧
        ‖fderiv ℝ (fun q => D.f q j l) x‖ ≤ A := fun j l =>
    h₁ (fun q => D.f q j l) (D.U ×ˢ D.V) D.K hU (D.f_analytic j l) D.isCompact_K D.K_subset
  choose A hApos hA using hex
  have hsum : 0 ≤ ∑ j, ∑ l, A j l :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hApos j l).le
  refine ⟨1 + ∑ j, ∑ l, A j l, by linarith, fun p hp j l => ?_⟩
  obtain ⟨hd, hb, hb'⟩ := hA j l p hp
  have hle := le_one_add_sum A hApos j l
  exact ⟨hd, hb.trans hle, hb'.trans hle⟩

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem cuspTime_continuousOn {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) (j : Fin a) :
    ContinuousOn (fun z => cuspTime h z j) (puncturedChart h U) := by
  have hc : Continuous (fun z : Fin n → ℂ => cuspCoord h z j) := continuous_apply _
  have hne : ∀ z ∈ puncturedChart h U, ‖cuspCoord h z j‖ ≠ 0 := fun z hz =>
    norm_ne_zero_iff.mpr (hz.2 j)
  have hinv : ContinuousOn (fun z => ‖cuspCoord h z j‖⁻¹) (puncturedChart h U) :=
    hc.norm.continuousOn.inv₀ hne
  exact continuousOn_const.mul (hinv.log fun z hz => inv_ne_zero (hne z hz))

theorem ChartImagContinuous.proof : ChartImagContinuous.Statement := by
  intro D
  have hsub : D.Ustar ⊆ D.U := fun z hz => hz.1
  have hτ : ∀ k l, ContinuousOn (fun z => (D.τ0 z k l).im) D.Ustar := fun k l =>
    Complex.continuous_im.comp_continuousOn ((D.τ0_analytic k l).continuousOn.mono hsub)
  have ht : ∀ j, ContinuousOn (fun z => cuspTime D.a_le z j) D.Ustar := fun j =>
    cuspTime_continuousOn D.a_le D.U j
  show ContinuousOn (fun z => chartImag D.a_le D.τ0 D.B z) D.Ustar
  refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => ?_
  simp only [chartImag, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact (hτ k l).add (continuousOn_finsetSum _ fun j _ => (ht j).mul continuousOn_const)

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem ChartPeriodImPos.proof : ChartPeriodImPos.Statement := by
  intro D z hz ℓ hℓ
  rw [MCPeriod.period_im D z ℓ hℓ]
  have hY : (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef := D.Y_ge z hz
  refine ⟨?_, ?_⟩
  · have e : D.Y z = (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)) +
        D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) := by abel
    rw [e]
    exact Matrix.PosDef.posSemidef_add hY (PosDef.one.smul D.c_pos)
  · intro x
    have h := hY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at h
    have hx : x ⬝ᵥ x = ∑ k, x k ^ 2 := by
      simp only [dotProduct, sq]
    rw [hx] at h
    rw [MCSchur.qf]
    linarith

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem CuspLattice.proof (h1 : CuspShortVectors.Statement) (h2 : CuspLeadingMinima.Statement)
    (h3 : CuspCovolume.Statement) : CuspLattice.Statement := by
  intro D T
  obtain ⟨c₁, hc₁, H1⟩ := h1 D T
  obtain ⟨c₂, hc₂, H3⟩ := h3 D T
  exact ⟨c₁, c₂, hc₁, hc₂, fun p hp hu ℓ hℓ =>
    ⟨H1 p hp hu ℓ hℓ, h2 D T p hp hu ℓ hℓ, fun k v hv hli => H3 p hp hu ℓ hℓ k v hv hli⟩⟩

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramDropLast.proof : IntGramDropLast.Statement := by
  intro d k S N hN
  ext i j
  simp only [intGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.submatrix_apply, id, Fin.sum_univ_castSucc, hN, Int.cast_zero, zero_mul, mul_zero,
    add_zero]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramQf.proof : IntGramQf.Statement := by
  intro d k S N z
  simp only [MCSchur.qf, intGram, ← mulVec_mulVec]
  rw [dotProduct_mulVec, vecMul_transpose]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramSubLast.proof : IntGramSubLast.Statement := by
  intro d k S M hM
  ext i j
  simp only [intGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.submatrix_apply, Fin.sum_univ_castSucc, hM, Int.cast_zero, zero_mul, mul_zero,
    add_zero]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramUnimodular.proof : IntGramUnimodular.Statement := by
  intro d k S N U hU
  have hmap : (N * U).map (Int.cast : ℤ → ℝ) =
      N.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have hdet : (U.map (Int.cast : ℤ → ℝ)).det = ((U.det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det U).symm
  have hsq : ((U.det : ℤ) : ℝ) * (U.det : ℝ) = 1 := by
    rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num
  unfold intGram
  rw [hmap, transpose_mul]
  have e : (U.map (Int.cast : ℤ → ℝ))ᵀ * (N.map (Int.cast : ℤ → ℝ))ᵀ * S *
      (N.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ)) =
      (U.map (Int.cast : ℤ → ℝ))ᵀ * ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)) *
        U.map (Int.cast : ℤ → ℝ) := by
    simp only [Matrix.mul_assoc]
  rw [e, det_mul, det_mul, det_transpose, hdet]
  calc (U.det : ℝ) * ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)).det * (U.det : ℝ)
      = ((U.det : ℤ) : ℝ) * (U.det : ℝ) *
          ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)).det := by ring
    _ = _ := by rw [hsq, one_mul]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace LeadingCovolume

theorem periodBasis_of_lt {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (i : ℕ) (hi : i < g)
    (hi' : i < g + g) : periodBasis τ ⟨i, hi'⟩ = Pi.single (⟨i, hi⟩ : Fin g) 1 := by
  have e : (⟨i, hi'⟩ : Fin (g + g)) = Fin.castAdd g ⟨i, hi⟩ := rfl
  rw [e, periodBasis, Fin.append_left]

end LeadingCovolume

theorem LeadingCovolume.proof : LeadingCovolume.Statement := by
  intro g τ r h
  unfold covolume leadMinor
  congr 2
  ext a b
  have ha : (a : ℕ) < g + g := by omega
  have hb : (b : ℕ) < g + g := by omega
  rw [Matrix.of_apply, Matrix.of_apply, dif_pos ⟨ha, hb⟩, periodGram, Matrix.of_apply,
    LeadingCovolume.periodBasis_of_lt τ a (by omega) ha,
    LeadingCovolume.periodBasis_of_lt τ b (by omega) hb]
  rfl

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem LeadMinorBasic.proof : LeadMinorBasic.Statement := by
  intro d S
  refine ⟨?_, ?_, ?_⟩
  · simp [leadMinor]
  · unfold leadMinor
    congr 1
    ext a b
    simp only [Matrix.of_apply]
    rw [dif_pos ⟨a.2, b.2⟩]
  · intro hS i hi
    have e : (Matrix.of fun a b : Fin i =>
        if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0) =
        S.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      rw [dif_pos ⟨a.2.trans_le hi, b.2.trans_le hi⟩]
      rfl
    unfold leadMinor
    rw [e]
    exact (hS.submatrix (Fin.castLE_injective hi)).det_pos

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem LeadMinorLeading.proof : LeadMinorLeading.Statement := by
  intro d S m h j hj
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.submatrix_apply]
  have ha : (a : ℕ) < m := lt_of_lt_of_le a.2 hj
  have hb : (b : ℕ) < m := lt_of_lt_of_le b.2 hj
  rw [dif_pos ⟨ha, hb⟩, dif_pos ⟨ha.trans_le h, hb.trans_le h⟩]
  rfl

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric Real MCPsh

noncomputable section

theorem LogDetGramPsh.proof (hcont : LogDetGramContinuous.Statement)
    (hsub : LogDetGramSubmean.Statement) : LogDetGramPsh.Statement := by
  intro N g rk S
  have hYc : ContinuousOn (fun x => (S.τ x).map Complex.im) S.W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      Complex.continuous_im.comp_continuousOn (S.τ_analytic j k).continuousOn
  have hFc : ContinuousOn S.f S.W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => (S.f_analytic j k).continuousOn
  have hc := hcont (Fin N → ℂ) S.W g rk (fun x => (S.τ x).map Complex.im) S.f hYc hFc
    S.im_posDef S.f_rank
  refine ⟨hc.upperSemicontinuousOn, ?_⟩
  intro z w hdisc
  have hline : ∀ ζ ∈ closedBall (0:ℂ) 1, z + ζ • w ∈ S.W := fun ζ hζ =>
    hdisc ζ (by simpa using hζ)
  have haff : ∀ ζ : ℂ, AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ := fun ζ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hτ : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.τ (z + ζ • w) j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.τ x j k) (f := fun ζ : ℂ => z + ζ • w)
      (S.τ_analytic j k _ (hline ζ hζ)) (haff ζ)
  have hf : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.f (z + ζ • w) j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.f x j k) (f := fun ζ : ℂ => z + ζ • w)
      (S.f_analytic j k _ (hline ζ hζ)) (haff ζ)
  have hYd : ContinuousOn (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im) (closedBall 0 1) :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      Complex.continuous_im.comp_continuousOn (hτ j k).continuousOn
  have hmean : ∀ j k, circleAverage (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im j k) 0 1 =
      (S.τ (z + (0:ℂ) • w)).map Complex.im j k := fun j k => by
    simpa only [map_apply] using circleAverage_im_of_analytic (hτ j k)
  obtain ⟨hint, hle⟩ := hsub g rk (fun ζ => (S.τ (z + ζ • w)).map Complex.im)
    (fun ζ => S.f (z + ζ • w)) (fun ζ hζ => S.im_posDef _ (hline ζ hζ)) hYd hmean hf
    (fun ζ hζ => S.f_rank _ (hline ζ hζ))
  refine ⟨hint, ?_⟩
  have e : z + (0:ℂ) • w = z := by simp
  simpa only [e] using hle

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PeriodHermValue

theorem re_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (α β : Fin g → ℝ) :
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).re) =
      α + τ.map Complex.re *ᵥ β := by
  ext k
  simp [mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

theorem im_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (α β : Fin g → ℝ) :
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).im) =
      τ.map Complex.im *ᵥ β := by
  ext k
  simp [mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

theorem qf_inv_mulVec {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : IsUnit Y.det)
    (β : Fin g → ℝ) : MCSchur.qf Y⁻¹ (Y *ᵥ β) = MCSchur.qf Y β := by
  unfold MCSchur.qf
  rw [mulVec_mulVec, nonsing_inv_mul Y hY, one_mulVec, dotProduct_comm]

end PeriodHermValue

theorem PeriodHermValue.proof : PeriodHermValue.Statement := by
  intro g τ hY α β
  rw [MCSchur.hermValue_eq_qf, PeriodHermValue.re_eq, PeriodHermValue.im_eq,
    PeriodHermValue.qf_inv_mulVec _ hY]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PivotInvDiag

theorem leadMinor_last_eq (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (d : ℕ) (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    leadMinor S d = (S.submatrix Fin.castSucc Fin.castSucc).det := by
  have h := hLL (d + 1) S d (Nat.le_succ d) d le_rfl
  have hc : (Fin.castLE (Nat.le_succ d) : Fin d → Fin (d + 1)) = Fin.castSucc := by
    funext i; ext; rfl
  rw [hc] at h
  rw [← h]
  exact (hLB d (S.submatrix Fin.castSucc Fin.castSucc)).2.1

theorem adjugate_last_last {d : ℕ} (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    S.adjugate (Fin.last d) (Fin.last d) = (S.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have : ((-1 : ℝ)) ^ ((Fin.last d : ℕ) + (Fin.last d : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]; norm_num
  rw [this, one_mul]

end PivotInvDiag

theorem PivotInvDiag.proof (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement) :
    PivotInvDiag.Statement := by
  intro d S hS
  obtain ⟨-, hdet, hpos⟩ := hLB (d + 1) S
  have hm : 0 < leadMinor S d := hpos hS d (Nat.le_succ d)
  have hD : 0 < leadMinor S (d + 1) := hpos hS (d + 1) le_rfl
  rw [hdet] at hD
  have hmin := PivotInvDiag.leadMinor_last_eq hLL hLB d S
  unfold pivot
  rw [hdet, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
    PivotInvDiag.adjugate_last_last, ← hmin, smul_eq_mul]
  field_simp
end
end Heights
end Heights₂
end GroundTheory
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem PivotLast.proof (hPI : PivotInvDiag.Statement) : PivotLast.Statement := by
  intro d S hS x
  have h1 := MCCusp.sq_le_inv_diag_mul_qf hS x (Fin.last d)
  have h2 := hPI d S hS
  have hpos : 0 < S⁻¹ (Fin.last d) (Fin.last d) := hS.inv.diag_pos
  have hp : 0 < pivot S d := by
    by_contra hc
    push_neg at hc
    have := mul_nonpos_of_nonneg_of_nonpos hpos.le hc
    linarith
  calc x (Fin.last d) ^ 2 * pivot S d
      ≤ (S⁻¹ (Fin.last d) (Fin.last d) * MCSchur.qf S x) * pivot S d :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ = MCSchur.qf S x * (S⁻¹ (Fin.last d) (Fin.last d) * pivot S d) := by ring
    _ = MCSchur.qf S x := by rw [h2, mul_one]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LogDetGramContinuous.full : LogDetGramContinuous.Statement := LogDetGramContinuous.proof

theorem LogDetGramSubmean.full : LogDetGramSubmean.Statement :=
  LogDetGramSubmean.proof LogDetGramContinuous.full

theorem InvEntryBound.full : InvEntryBound.Statement := InvEntryBound.proof

theorem InvEntryDeriv.full : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.full

theorem LogDetGramDeriv.full : LogDetGramDeriv.Statement :=
  LogDetGramDeriv.proof InvEntryBound.full InvEntryDeriv.full MatrixDetDeriv.proof
    GramEntryDeriv.proof

theorem AnalyticDerivBound.full : AnalyticDerivBound.Statement := AnalyticDerivBound.proof

theorem ChartFrameDeriv.full : ChartFrameDeriv.Statement :=
  ChartFrameDeriv.proof AnalyticDerivBound.full

theorem ChartImagDeriv.full : ChartImagDeriv.Statement :=
  ChartImagDeriv.proof AnalyticDerivBound.full CuspTimeDeriv.proof

theorem PeriodHermValue.full : PeriodHermValue.Statement := PeriodHermValue.proof

theorem PeriodGramPosDef.full : PeriodGramPosDef.Statement :=
  PeriodGramPosDef.proof PeriodHermValue.full

theorem PivotInvDiag.full : PivotInvDiag.Statement :=
  PivotInvDiag.proof LeadMinorLeading.proof LeadMinorBasic.proof

theorem PivotLast.full : PivotLast.Statement := PivotLast.proof PivotInvDiag.full

theorem PivotBounds.full : PivotBounds.Statement :=
  PivotBounds.proof LeadMinorLeading.proof LeadMinorBasic.proof PivotInvDiag.full PivotLast.full

theorem PivotProductBound.full : PivotProductBound.Statement :=
  PivotProductBound.proof LeadMinorBasic.proof

theorem GramPivotProduct.full : GramPivotProduct.Statement :=
  GramPivotProduct.proof LeadMinorLeading.proof LeadMinorBasic.proof PivotLast.full
    UnimodularLast.proof SchurDetBound.proof IntGramQf.proof IntGramUnimodular.proof
    IntGramDropLast.proof IntGramSubLast.proof

theorem CuspCoordinateBound.full : CuspCoordinateBound.Statement :=
  CuspCoordinateBound.proof ChartPeriodImPos.proof ChartLowerBlockBound.proof PeriodGramPosDef.full

theorem ChartBounds.full : ChartBounds.Statement := ChartBounds.proof

theorem ChartGradient.full : ChartGradient.Statement :=
  ChartGradient.proof LogDetGramDeriv.full ChartFrameDeriv.full ChartImagDeriv.full
    ChartBounds.full

theorem LogDetGramPsh.full : LogDetGramPsh.Statement :=
  LogDetGramPsh.proof LogDetGramContinuous.full LogDetGramSubmean.full

theorem ChartPotentialPsh.full : ChartPotentialPsh.Statement :=
  ChartPotentialPsh.proof LogDetGramContinuous.full LogDetGramSubmean.full
    ChartImagContinuous.proof ChartImagMean.proof

theorem SchurQuotient.full : SchurQuotient.Statement := MCSchur.schurQuotient

theorem SchurQuotientPeriod.full : SchurQuotientPeriod.Statement := MCPeriod.schurQuotientPeriod

theorem CuspLattice.full : CuspLattice.Statement :=
  CuspLattice.proof
    (CuspShortVectors.proof ChartPeriodImPos.proof ChartLowerBlockBound.proof PeriodHermValue.full)
    (CuspLeadingMinima.proof ChartPeriodImPos.proof)
    (CuspCovolume.proof ChartPeriodImPos.proof PeriodGramPosDef.full CuspCoordinateBound.full
      PivotBounds.full GramPivotProduct.full PivotProductBound.full
      PeriodLatticeCovolume.proof LeadingCovolume.proof)

end GroundTheory.Heights₂.Heights
end
