import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.InGBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CayleyInverseConjTransposeMulApply
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TsContinuousNU
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolParam

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

theorem inv_of_inG {x : M2 n} (hx : InG x) : x⁻¹ = -(JJ n * xᴴ * JJ n) := by
  refine Matrix.inv_eq_left_inv ?_
  have h : xᴴ * JJ n * x = JJ n := hx
  calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
    _ = 1 := by rw [h, JJ_sq]; simp

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x := by
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have h : xᴴ * JJ n * x = JJ n := hx
    calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
      _ = 1 := by rw [h, JJ_sq]; simp
  exact (Matrix.isUnit_iff_isUnit_det x).mpr (Matrix.isUnit_det_of_left_inverse h)

theorem isUnit_det_of_inG {x : M2 n} (hx : InG x) : IsUnit x.det :=
  (Matrix.isUnit_iff_isUnit_det x).mp (isUnit_of_inG hx)

theorem inverse_first_block_eq_conjTranspose {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ := by
  rw [ub1, inv_of_inG hx, u1]
  conv_lhs => rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁]
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, sub_eq_add_neg]
  abel

theorem det_first_block_ne_zero_group {x : M2 n} (hx : InG x) : (u1 x).det ≠ 0 := by
  have := PositivityTheory.Rg.Sw.AbsSt.IwaPf.det_ne x hx Complex.I (by simp [Complex.ext_iff]; norm_num)
  simpa [u1] using this

def Nq (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks 0 Q 0 0 * Cmi n

theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.mp cm_mul_cmi

theorem Nq_sq (Q : Matrix (Fin n) (Fin n) ℂ) : Nq Q * Nq Q = 0 := by
  have : fromBlocks 0 Q 0 0 * fromBlocks 0 Q 0 0 = (0 : M2 n) := by
    rw [fromBlocks_multiply]; simp [fromBlocks_zero]
  calc Nq Q * Nq Q = Cm n * fromBlocks 0 Q 0 0 * (Cmi n * Cm n) * fromBlocks 0 Q 0 0 * Cmi n := by
        simp only [Nq, Matrix.mul_assoc]
    _ = 0 := by rw [cmi_mul_cm, Matrix.mul_one, Matrix.mul_assoc (Cm n), this]; simp

theorem mX_eq (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : mX (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 = 1 + s • Nq Q := by
  have e : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 : M2 n) = 1 + s • (fromBlocks 0 Q 0 0 : M2 n) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  rw [mX, cm_inv, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, Nq, Matrix.mul_smul, Matrix.smul_mul]

theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Nq Q := by
  have := mX_eq Q 1
  rw [one_smul, one_smul] at this
  rw [lowQ, this]; abel

theorem Nq_blocks (Q : Matrix (Fin n) (Fin n) ℂ) :
    Nq Q = fromBlocks (-(1 / 2 : ℂ) • Q) ((Complex.I / 2) • Q) ((Complex.I / 2) • Q) ((1 / 2 : ℂ) • Q) := by
  rw [Nq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem inv_mul_lower {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    (x * (1 + s • Nq Q))⁻¹ = (1 - s • Nq Q) * x⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  have hN := Nq_sq Q
  have e : (1 + s • Nq Q) * (1 - s • Nq Q) = (1 : M2 n) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN]
    simp
  have hx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x ((Matrix.isUnit_iff_isUnit_det x).mp hx)
  calc x * (1 + s • Nq Q) * ((1 - s • Nq Q) * x⁻¹) = x * ((1 + s • Nq Q) * (1 - s • Nq Q)) * x⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e, Matrix.mul_one, hx']

theorem upper_left_block_sub (A B : M2 n) : (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
theorem lower_left_block_sub (A B : M2 n) : (A - B).toBlocks₂₁ = A.toBlocks₂₁ - B.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
theorem upper_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
theorem lower_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₂₁ = c • A.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
theorem upper_left_block_mul_eq (A B : M2 n) : (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem inverse_first_block_lowering {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    ub1 (x * (1 + s • Nq Q)) = ub1 x - s • (Q * ub2 x) := by
  rw [ub1, inv_mul_lower hx, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, upper_left_block_sub, lower_left_block_sub, upper_left_block_smul,
    lower_left_block_smul, upper_left_block_mul_eq, toBlocks₂₁_mul, Nq_blocks, ub1, ub2]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.smul_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, smul_add, smul_sub, smul_neg, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem first_block_lowering_invariant (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : u1 (x * (1 + s • Nq Q)) = u1 x := by
  have := (uAct n x 1 (s • Q) 0 1).1
  rw [mX_eq] at this
  rw [this]; simp

theorem det_lower (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : (x * (1 + s • Nq Q)).det = x.det := by
  rw [← mX_eq, det_mul, mX, cm_inv, det_mul, det_mul, det_fromBlocks_zero₂₁]
  have : (Cm n).det * (Cmi n).det = 1 := by rw [← det_mul, cm_mul_cmi, det_one]
  simp only [det_one, mul_one]
  linear_combination x.det * this

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
end
end

section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem deriv_comp_mul_exp_smul_eq_fderiv (F : M2 n → ℂ) (x W : M2 n) (hF : DifferentiableAt ℂ F x) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) 0 = fderiv ℂ F x (x * W) := by
  have hL : HasDerivAt (fun t : ℝ => x * II.cE W t) (x * W) 0 := by
    let L : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 W)
  have h := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp [II.cE])
  have he : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) = fun t => F (x * II.cE W t) := by
    funext t
    simp only [II.cE, Complex.coe_smul]
  rw [he]
  exact h.deriv

theorem rC_eq (F : M2 n → ℂ) (x Z : M2 n) (hF : DifferentiableAt ℂ F x) : rC Z F x = fderiv ℂ F x (x * Z) := by
  unfold rC
  rw [deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, ← smul_eq_mul Complex.I, ← map_smul, ← map_add,
    ← Matrix.mul_smul, ← Matrix.mul_add, smul_smul]
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [hI, ← smul_add, add_add_sub_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem contDiffOn_inverse_first_block : ∀ i j, ContDiffOn ℂ ∞ (fun x : M2 n => ub1 x i j) {x | x.det ≠ 0} := by
  intro i j
  exact LVs.contDiffOn_inverse_first_block _ (fun x hx => isUnit_iff_ne_zero.2 hx) i j

theorem isOpen_det_ne : IsOpen {x : M2 n | x.det ≠ 0} :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
end
end

section
noncomputable section

open Matrix Filter Topology Polynomial
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem diffAt_of_cdo {f : M2 n → ℂ} {U : Set (M2 n)} (hf : ContDiffOn ℂ ∞ f U) (hU : IsOpen U) {x : M2 n}
    (hx : x ∈ U) : DifferentiableAt ℂ f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

theorem D0_eq_numSeg_mul_add {x : M2 n} (hx : InG x) :
    (u1 x).det * (ub1 x).det = ((Complex.normSq (u1 x).det : ℝ) : ℂ) := by
  rw [inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def]
  exact Complex.mul_conj _

theorem normSq_det_first_block_pos {x : M2 n} (hx : InG x) : 0 < Complex.normSq (u1 x).det :=
  Complex.normSq_pos.mpr (det_first_block_ne_zero_group hx)

theorem det_product_mem_slitPlane {x : M2 n} (hx : InG x) : (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := by
  rw [D0_eq_numSeg_mul_add hx]; exact Complex.ofReal_mem_slitPlane.mpr (normSq_det_first_block_pos hx)

theorem diff_fz {x : M2 n} (hx : InG x) (m : ℕ) (e : ℤ) (z : ℂ) : DifferentiableAt ℂ (fz m e z) x := by
  have hU : IsOpen {y : M2 n | det y ≠ 0} := isOpen_det_ne
  have hxU : x ∈ {y : M2 n | det y ≠ 0} := (isUnit_det_of_inG hx).ne_zero
  have hdet : DifferentiableAt ℂ (fun y : M2 n => det y) x :=
    diffAt_of_cdo (cdo_det (fun i j => (contDiff_apply_apply ℂ ℂ i j).contDiffOn)) hU hxU
  have hu1 : DifferentiableAt ℂ (fun y : M2 n => (u1 y).det) x :=
    diffAt_of_cdo (cdo_det (fun i j => LVs.contDiffOn_first_cayley_block_entries _ i j)) hU hxU
  have hub1 : DifferentiableAt ℂ (fun y : M2 n => (ub1 y).det) x :=
    diffAt_of_cdo (cdo_det (fun i j => PositivityTheory.Rg.Sw.HSt.LoweringDerivative.contDiffOn_inverse_first_block i j)) hU hxU
  unfold fz
  refine ((hdet.zpow (Or.inl hxU)).mul (hu1.zpow (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_
  exact (hu1.mul hub1).cpow (differentiableAt_const _) (det_product_mem_slitPlane hx)

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_det_one_add_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • A).det) A.trace 0 := by
  have h : (fun s : ℂ => (1 + s • A).det) = fun s =>
      1 + A.trace * s + (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2 := by
    funext s
    exact Matrix.det_one_add_smul s A
  rw [h]
  have h1 : HasDerivAt (fun s : ℂ => 1 + A.trace * s) A.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul A.trace).const_add 1
  have h2 : HasDerivAt (fun s : ℂ =>
      (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2) 0 0 := by
    convert (Polynomial.hasDerivAt
      (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX (0 : ℂ)).fun_mul
      (hasDerivAt_pow 2 (0 : ℂ)) using 1
    all_goals first
      | rfl
      | simp
  convert h1.fun_add h2 using 1
  all_goals first
    | rfl
    | simp

set_option backward.isDefEq.respectTransparency false in
theorem lt1 : LoweringDerivativeVacuum := by
  intro n m e z Q x hx
  have hxu : IsUnit x := isUnit_of_inG hx
  have hD : (u1 x).det * (ub1 x).det ≠ 0 := Complex.slitPlane_ne_zero (det_product_mem_slitPlane hx)
  have hB : (ub1 x).det ≠ 0 := right_ne_zero_of_mul hD
  rw [rC_eq _ _ _ (diff_fz hx m e z), lowQ_eq]
  have hline : ∀ s : ℂ, x + s • (x * Nq Q) = x * (1 + s • Nq Q) := by
    intro s
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hsub : ∀ s : ℂ, ub1 x - s • (Q * ub2 x) = ub1 x * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))) := by
    intro s
    have hBu : IsUnit (ub1 x).det := isUnit_iff_ne_zero.2 hB
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul, smul_neg, sub_eq_add_neg]
  have hcomp : ∀ s : ℂ, fz m e z (x + s • (x * Nq Q)) = det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      ((u1 x).det * ((ub1 x).det * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))).det)) ^ (-z) := by
    intro s
    rw [hline s]
    unfold fz
    rw [det_lower, first_block_lowering_invariant, inverse_first_block_lowering hxu, hsub, Matrix.det_mul]
  have htr : (-((ub1 x)⁻¹ * (Q * ub2 x))).trace = -(Om x * Q).trace := by
    unfold Om
    rw [Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm Q]
  have hL : HasDerivAt (fun s : ℂ => x + s • (x * Nq Q)) (x * Nq Q) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).smul_const (x * Nq Q)).const_add x using 1
    all_goals first
      | rfl
      | simp
  have h1 : HasDerivAt (fun s : ℂ => fz m e z (x + s • (x * Nq Q)))
      (fderiv ℂ (fz m e z) x (x * Nq Q)) 0 :=
    (diff_fz hx m e z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hdet := hasDerivAt_det_one_add_smul (-((ub1 x)⁻¹ * (Q * ub2 x)))
  have hg := (hdet.const_mul (ub1 x).det).const_mul (u1 x).det
  have hg0 : (u1 x).det * ((ub1 x).det * (1 + (0 : ℂ) • -((ub1 x)⁻¹ * (Q * ub2 x))).det)
      ∈ Complex.slitPlane := by
    simpa using det_product_mem_slitPlane hx
  have hp := (hg.cpow_const (c := -z) hg0).const_mul (det x ^ e * (u1 x).det ^ (-(m : ℤ)))
  have h2 := hp.congr_of_eventuallyEq (Filter.Eventually.of_forall hcomp)
  rw [h1.unique h2, htr]
  simp only [zero_smul, add_zero, Matrix.det_one, mul_one]
  rw [Complex.cpow_sub _ _ hD, Complex.cpow_one]
  have hr : (u1 x).det * ((ub1 x).det * -(Om x * Q).trace) =
      -((u1 x).det * (ub1 x).det * (Om x * Q).trace) := by ring
  rw [hr]
  unfold eQ fz
  generalize (u1 x).det * (ub1 x).det = D at hD ⊢
  field_simp

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative

namespace PositivityTheory.Rg.Sw.HSt

theorem lt1 : LoweringDerivativeVacuum := LoweringDerivative.lt1

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open Matrix Filter Topology MeasureTheory
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem JJ_sq_eq_neg_one : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

private theorem inG_mul_JJ_mul_conjTranspose_eq_JJ {x : M2 n} (hx : InG x) : x * JJ n * xᴴ = JJ n := by
  have hJ := (JJ_sq_eq_neg_one (n := n))
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h1 : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hx', hJ, neg_neg]
  have h2 : x * (-(JJ n * xᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc x * JJ n * xᴴ = x * (-(JJ n * xᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, neg_neg]
    _ = JJ n := by rw [h2, Matrix.one_mul]

private theorem toBlocks₂_relations_of_inG {x : M2 n} (hx : InG x) :
    toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ = toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ ∧
    toBlocks₂₁ x * (toBlocks₁₂ x)ᴴ - toBlocks₂₂ x * (toBlocks₁₁ x)ᴴ = -1 := by
  have e := inG_mul_JJ_mul_conjTranspose_eq_JJ hx
  rw [← fromBlocks_toBlocks x] at e
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_inj,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂] at e
  simp at e
  refine ⟨?_, ?_⟩
  · have h := e.2.2.2
    rw [neg_add_eq_sub, sub_eq_zero] at h
    exact h
  · have h := e.2.2.1
    rwa [neg_add_eq_sub] at h

private theorem det_smul_toBlocks₂₁_add_toBlocks₂₂_ne_zero {x : M2 n} (hx : InG x) (t : ℂ) (ht : t ≠ star t) :
    (t • toBlocks₂₁ x + toBlocks₂₂ x).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hvM⟩ := exists_vecMul_eq_zero_iff.mpr h0
  obtain ⟨hC, hA⟩ := toBlocks₂_relations_of_inG hx
  rw [Matrix.vecMul_add, Matrix.vecMul_smul] at hvM
  have hβ : v ᵥ* toBlocks₂₂ x = -t • (v ᵥ* toBlocks₂₁ x) := by
    rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hvM
  have key : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x)
      = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) := by
    have h := congrArg (fun M => (v ᵥ* M) ⬝ᵥ star v) hC
    have e1 : (v ᵥ* (toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ)) ⬝ᵥ star v
        = (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x) := by
      rw [← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]
    have e2 : (v ᵥ* (toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ)) ⬝ᵥ star v
        = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) := by
      rw [← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]
    rw [← e1, ← e2]
    exact h
  rw [hβ, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at key
  have hs : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) = 0 := by
    have h3 : (t - star t) * ((v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x)) = 0 := by
      rw [star_neg] at key
      linear_combination key
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) ht
    · exact h4
  have hα : v ᵥ* toBlocks₂₁ x = 0 := by
    open scoped ComplexOrder in exact dotProduct_self_star_eq_zero.mp hs
  have hβ0 : v ᵥ* toBlocks₂₂ x = 0 := by rw [hβ, hα, smul_zero]
  have h5 := congrArg (fun M => v ᵥ* M) hA
  simp only [Matrix.vecMul_sub, ← vecMul_vecMul, hα, hβ0, zero_vecMul, sub_self, vecMul_neg,
    vecMul_one] at h5
  exact hv (neg_eq_zero.mp h5.symm)

theorem det_second_cayley_block_ne {x : M2 n} (hx : InG x) : (u2 x).det ≠ 0 := by
  have h := det_smul_toBlocks₂₁_add_toBlocks₂₂_ne_zero hx (-Complex.I) (by
    rw [star_neg, Complex.star_def, Complex.conj_I, neg_neg]
    intro h
    have := congrArg Complex.im h
    norm_num at this)
  rw [neg_smul] at h
  exact h

theorem inG_of_inK {g : M2 n} (h : InK g) : InG g := h.1

private theorem det_ne_zero_of_inG' {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  have hJ : JJ n * JJ n = -1 := by
    rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
    simp
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h1 : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hx', hJ, neg_neg]
  exact (Matrix.isUnit_det_of_left_inverse h1).ne_zero

theorem continuous_rhoP {Kg : Type} [TopologicalSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι)
    (hK : ∀ k, InG (ι k)) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) : Continuous (rhoP ι m e Y) := by
  have hC : Continuous fun k => toBlocks₂₁ (ι k) :=
    continuous_matrix fun i j => hι.matrix_elem (Sum.inr i) (Sum.inl j)
  have hD : Continuous fun k => toBlocks₂₂ (ι k) :=
    continuous_matrix fun i j => hι.matrix_elem (Sum.inr i) (Sum.inr j)
  have hu1 : Continuous fun k => u1 (ι k) := by
    unfold u1
    fun_prop
  have hu2 : Continuous fun k => u2 (ι k) := by
    unfold u2
    fun_prop
  have hI : Complex.I ≠ star Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hd1 : ∀ k, (u1 (ι k)).det ≠ 0 := fun k => det_smul_toBlocks₂₁_add_toBlocks₂₂_ne_zero (hK k) Complex.I hI
  have hinv : Continuous fun k => (u2 (ι k))⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro k
    refine (continuousAt_matrix_inv _ ?_).comp hu2.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (det_second_cayley_block_ne (hK k))
  have hdet : Continuous fun k => (ι k).det := hι.matrix_det
  unfold rhoP fz
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  refine Continuous.star (Continuous.mul (Continuous.mul (hdet.zpow₀ e ?_) ?_)
    (Continuous.matrix_trace ((hinv.matrix_mul continuous_const).matrix_mul hu1)))
  · exact fun k => Or.inl (det_ne_zero_of_inG' (hK k))
  · exact (hu1.matrix_det).zpow₀ _ (fun k => Or.inl (hd1 k))

theorem one_upper_left_block : (1 : M2 n).toBlocks₁₁ = 1 := by ext i j; simp [toBlocks₁₁, Matrix.one_apply]
theorem one_lower_left_block : (1 : M2 n).toBlocks₂₁ = 0 := by ext i j; simp [toBlocks₂₁, Matrix.one_apply]
theorem one_lower_right_block : (1 : M2 n).toBlocks₂₂ = 1 := by ext i j; simp [toBlocks₂₂, Matrix.one_apply]

theorem fz_one (m : ℕ) (e : ℤ) (z : ℂ) : fz m e z (1 : M2 n) = 1 := by
  simp [fz, u1, ub1, one_upper_left_block, one_lower_left_block, one_lower_right_block]

theorem Om_one : Om (1 : M2 n) = -1 := by
  simp [Om, ub2, ub1, one_upper_left_block, one_lower_left_block]

theorem eQ_one (m : ℕ) (e : ℤ) (z : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) : eQ m e z Q (1 : M2 n) = -Q.trace := by
  simp [eQ, fz_one, Om_one]

theorem eQ_smul (m : ℕ) (e : ℤ) (z c : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (x : M2 n) :
    eQ m e z (c • Q) x = c * eQ m e z Q x := by
  simp only [eQ, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring

theorem asmLT : AsmLT := by
  unfold AsmLT LocTau
  intro hLT1 hLT2 hLT3 hCrux n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hιK Q
  have hK : ∀ k, InG (ι k) := fun k => inG_of_inK ((hιK (ι k)).mpr ⟨k, rfl⟩)
  obtain ⟨P, ψ, a, b, x0, hψ, ha, hb, hx0, hder⟩ := hCrux n m e hmn Kg μ ι hι hιK
  obtain ⟨c, hc, hcEq⟩ := hLT2 n m e Kg μ ι hι hιK ψ a b hψ.1 hψ.2.1 ha hb
  have h1G : InG (1 : M2 n) := by simp [InG]
  have hc0 : c 0 = 0 := by
    have h3 := hLT3 n m e hmn Kg μ ι hι hιK (rhoP ι m e 1) ψ a b 1
      (continuous_rhoP ι hι hK m e 1) hψ ha hb h1G
    rw [hcEq 1 0 1 h1G, eQ_smul, eQ_one] at h3
    simp at h3
    rcases h3 with h | h
    · exact h
    · omega
  have hd : deriv c 0 ≠ 0 := by
    intro hd0
    apply hder
    set β := (u1 x0).det * (ub1 x0).det with hβdef
    set K0 := x0.det ^ e * (u1 x0).det ^ (-(m : ℤ)) * (Om x0 * Pᴴ).trace with hK0
    have hF : (fun z => tOp μ ι (rhoP ι m e P) ψ a b (fz m e z) x0)
        = fun z => c z * (K0 * β ^ (-z)) := by
      funext z
      rw [hcEq P z x0 hx0, eQ_smul]
      simp only [eQ, fz, hK0, hβdef]
      ring
    rw [hF]
    by_cases hβ : β = 0
    · have h0 : (fun z => c z * (K0 * β ^ (-z))) = fun _ => 0 := by
        funext z
        by_cases hz : z = 0
        · subst hz
          simp [hc0]
        · simp [hβ, Complex.zero_cpow (neg_ne_zero.mpr hz)]
      rw [h0]
      simp
    · have hg : HasDerivAt (fun z : ℂ => K0 * β ^ (-z)) (K0 * (β ^ (-(0 : ℂ)) * Complex.log β * (-1))) 0 :=
        (((hasDerivAt_id' (0 : ℂ)).neg).const_cpow (Or.inl hβ)).const_mul K0
      have h := ((hc 0).hasDerivAt.mul hg).deriv
      simp only [hd0, hc0, zero_mul, mul_zero, add_zero] at h
      exact h
  refine ⟨1, fun _ => rhoP ι m e Qᴴ, fun _ => ψ, fun _ => a, fun _ => b, dslope c 0, fun _ _ => 1,
    fun _ => continuous_rhoP ι hι hK m e _, fun _ => hψ, fun _ => ⟨ha, hb⟩, ?_, ?_,
    fun _ => differentiable_const _, ?_⟩
  · have h := (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).mpr
      hc.differentiableOn
    exact differentiableOn_univ.mp h
  · rw [dslope_same]
    exact hd
  · intro z x hx
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
    rw [hLT1 n m e z Q x hx, hcEq Qᴴ z x hx, conjTranspose_conjTranspose, eQ_smul]
    have h := sub_smul_dslope c 0 z
    rw [sub_zero, hc0, sub_zero, smul_eq_mul] at h
    rw [← h]
    ring

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative

namespace PositivityTheory.Rg.Sw.HSt

theorem asmLT : AsmLT := LoweringDerivative.asmLT

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

private theorem mul_toBlocks₂₁_eq (g h : M2 n) :
    (g * h).toBlocks₂₁ = g.toBlocks₂₁ * h.toBlocks₁₁ + g.toBlocks₂₂ * h.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

private theorem mul_toBlocks₂₂_eq (g h : M2 n) :
    (g * h).toBlocks₂₂ = g.toBlocks₂₁ * h.toBlocks₁₂ + g.toBlocks₂₂ * h.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂]

private theorem mul_toBlocks₁₁' (g h : M2 n) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ + g.toBlocks₁₂ * h.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

private theorem mul_toBlocks₁₂ (g h : M2 n) :
    (g * h).toBlocks₁₂ = g.toBlocks₁₁ * h.toBlocks₁₂ + g.toBlocks₁₂ * h.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

private theorem conjTranspose_toBlocks (g : M2 n) :
    (gᴴ).toBlocks₁₁ = (g.toBlocks₁₁)ᴴ ∧ (gᴴ).toBlocks₁₂ = (g.toBlocks₂₁)ᴴ ∧
      (gᴴ).toBlocks₂₁ = (g.toBlocks₁₂)ᴴ ∧ (gᴴ).toBlocks₂₂ = (g.toBlocks₂₂)ᴴ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.conjTranspose_apply]

private theorem JJ_toBlocks :
    (JJ n).toBlocks₁₁ = 0 ∧ (JJ n).toBlocks₁₂ = 1 ∧ (JJ n).toBlocks₂₁ = -1 ∧ (JJ n).toBlocks₂₂ = 0 := by
  simp [JJ]

private theorem inK_toBlocks₂_eq {k : M2 n} (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have h2 : k * kᴴ = 1 := mul_eq_one_comm.mp hk.2
  have h3 : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [h2, Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hG]
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  have e1 := congrArg Matrix.toBlocks₁₁ h3
  have e2 := congrArg Matrix.toBlocks₁₂ h3
  rw [mul_toBlocks₁₁', mul_toBlocks₁₁', j11, j12, j21] at e1
  rw [mul_toBlocks₁₂, mul_toBlocks₁₂, j11, j12, j22] at e2
  simp at e1 e2
  exact ⟨e1, e2⟩

private theorem neg_toBlocks₁₁_toBlocks₂₁ (g : M2 n) :
    (-g).toBlocks₁₁ = -g.toBlocks₁₁ ∧ (-g).toBlocks₂₁ = -g.toBlocks₂₁ := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

private theorem one_toBlocks₁₁_toBlocks₁₂ :
    (1 : M2 n).toBlocks₁₁ = 1 ∧ (1 : M2 n).toBlocks₁₂ = 0 := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.one_apply]

private theorem inK_toBlocks₁_unitary_relations {k : M2 n} (hk : InK k) :
    (k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂ = 1 ∧
      (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂ = (k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  have hU : kᴴ * k = 1 := hk.2
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks k
  obtain ⟨o11, o12⟩ := (one_toBlocks₁₁_toBlocks₁₂ (n := n))
  have e1 := congrArg Matrix.toBlocks₁₁ hU
  have e2 := congrArg Matrix.toBlocks₁₂ hU
  rw [mul_toBlocks₁₁', c11, c12, hc, o11] at e1
  rw [mul_toBlocks₁₂, c11, c12, hc, hd, o12] at e2
  simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg] at e1 e2
  refine ⟨e1, ?_⟩
  rw [← sub_eq_zero]
  simpa [sub_eq_add_neg] using e2

theorem first_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u1 (g * k) = u1 g * u1 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

theorem second_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u2 (g * k) = u2 g * u2 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

theorem first_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u1 k)ᴴ * u1 k = 1 := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  obtain ⟨h1, h2⟩ := inK_toBlocks₁_unitary_relations hk
  have e : (u1 k)ᴴ * u1 k = ((k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂) +
      Complex.I • ((k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ - (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂) := by
    simp only [u1, hc, hd, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_neg,
      Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, neg_smul, Complex.I_mul_I, neg_mul]
    module
  rw [e, h1, h2, sub_self, smul_zero, add_zero]

def eps (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

theorem eps_sq : eps n * eps n = 1 := by
  simp [eps, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem eps_JJ : eps n * JJ n * eps n = -JJ n := by
  simp [eps, JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

theorem eps_conj : (eps n)ᴴ = eps n := by simp [eps, fromBlocks_conjTranspose]

theorem inK_eps {k : M2 n} (hk : InK k) : InK (eps n * k * eps n) := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have hU : kᴴ * k = 1 := hk.2
  have e : eps n * JJ n * eps n = -JJ n := eps_JJ
  refine ⟨?_, ?_⟩
  · show (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n) = JJ n
    calc (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * JJ n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = -(eps n * (kᴴ * JJ n * k) * eps n) := by
          rw [e]
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hG, e, neg_neg]
  · show (eps n * k * eps n)ᴴ * (eps n * k * eps n) = 1
    calc (eps n * k * eps n)ᴴ * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [eps_sq, Matrix.mul_one, hU, Matrix.mul_one, eps_sq]

theorem first_cayley_block_swap_conj (k : M2 n) : u1 (eps n * k * eps n) = u2 k := by
  simp [u1, u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, eps]

theorem second_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u2 k)ᴴ * u2 k = 1 := by
  rw [← first_cayley_block_swap_conj]
  exact first_cayley_block_compact_unitary (inK_eps hk)

theorem second_cayley_block_inv_eq_conjTranspose {k : M2 n} (hk : InK k) : (u2 k)⁻¹ = (u2 k)ᴴ := Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk)

theorem inverse_second_block_eq_neg_conjTranspose {x : M2 n} (hx : InG x) : ub2 x = -(u2 x)ᴴ := by
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks x
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  obtain ⟨n11, n21⟩ := neg_toBlocks₁₁_toBlocks₂₁ (JJ n * xᴴ * JJ n)
  simp only [ub2, u2, inv_of_inG hx, n11, n21, mul_toBlocks₁₁', mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, mul_toBlocks₁₂,
    c11, c12, c21, c22,
    j11, j12, j21, j22, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_I, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_neg, neg_smul, smul_neg]
  module

theorem Om_K {k : M2 n} (hk : InK k) : Om k = -((u2 k)⁻¹ * u1 k) := by
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose hk.1, inverse_first_block_eq_conjTranspose hk.1, Matrix.inv_eq_left_inv (mul_eq_one_comm.mp (first_cayley_block_compact_unitary hk)),
    ← second_cayley_block_inv_eq_conjTranspose hk, Matrix.neg_mul]

theorem normSq_det_u1K {k : M2 n} (hk : InK k) : Complex.normSq (u1 k).det = 1 := by
  have h := congrArg Matrix.det (first_cayley_block_compact_unitary hk)
  rw [det_mul, det_conjTranspose, det_one] at h
  have h' : (Complex.normSq (u1 k).det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast h'

theorem fz_K (m : ℕ) (e : ℤ) (z : ℂ) {k : M2 n} (hk : InK k) : fz m e z k = fz m e 0 k := by
  have hd : (u1 k).det * (ub1 k).det = 1 := by
    rw [inverse_first_block_eq_conjTranspose hk.1, Matrix.det_conjTranspose, Complex.star_def, mul_comm,
      ← Complex.normSq_eq_conj_mul_self, normSq_det_u1K hk, Complex.ofReal_one]
  simp only [fz, hd, Complex.one_cpow, neg_zero, Complex.cpow_zero]

theorem first_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u1 (p * y) = p.toBlocks₂₂ * u1 y := by
  simp only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul]

theorem second_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u2 (p * y) = p.toBlocks₂₂ * u2 y := by
  simp only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_neg]

theorem inG_mul {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hy' : yᴴ * JJ n * y = JJ n := hy
  show (x * y)ᴴ * JJ n * (x * y) = JJ n
  calc (x * y)ᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx', hy']

theorem Om_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) : Om (p * y) = Om y := by
  have hp' : pᴴ * JJ n * p = JJ n := hp
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks p
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  have e := congrArg Matrix.toBlocks₁₂ hp'
  rw [mul_toBlocks₁₂, mul_toBlocks₁₁', mul_toBlocks₁₂, c11, c12, j11, j12, j21, j22, hp21] at e
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    zero_add, add_zero, Matrix.mul_neg, neg_zero] at e
  have hq : (p.toBlocks₂₂)ᴴ * p.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.conjTranspose e
    simpa [Matrix.conjTranspose_mul] using this
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose (inG_mul hp hy), inverse_first_block_eq_conjTranspose (inG_mul hp hy), inverse_second_block_eq_neg_conjTranspose hy, inverse_first_block_eq_conjTranspose hy, second_cayley_block_upper_triangular_mul hp21, first_cayley_block_upper_triangular_mul hp21,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hq,
    Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (p.toBlocks₂₂)ᴴ, hq, Matrix.one_mul]

def lam (m : ℕ) (e : ℤ) (z : ℂ) (p : M2 n) : ℂ :=
  p.det ^ e * (p.toBlocks₂₂).det ^ (-(m : ℤ)) * ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) ^ (-z)

theorem fz_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (m : ℕ) (e : ℤ) (z : ℂ) :
    fz m e z (p * y) = lam m e z p * fz m e z y := by
  have h1 : (u1 (p * y)).det = (p.toBlocks₂₂).det * (u1 y).det := by rw [first_cayley_block_upper_triangular_mul hp21, Matrix.det_mul]
  have h2 : (u1 (p * y)).det * (ub1 (p * y)).det =
      ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) * ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose (inG_mul hp hy), Matrix.det_conjTranspose, h1, star_mul', Complex.star_def,
      Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have h3 : (u1 y).det * (ub1 y).det = ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hy, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  simp only [fz, lam]
  rw [h2, h3, h1, Matrix.det_mul, mul_zpow, mul_zpow,
    Complex.mul_cpow_ofReal_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)]
  ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

variable {n : ℕ}

theorem span_unitary_matrix :
    Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) = ⊤ := by
  open scoped Matrix.Norms.L2Operator in exact CStarAlgebra.span_unitary (A := Matrix (Fin n) (Fin n) ℂ)


def pm (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if σ i = j then 1 else 0

theorem pm_conj (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    pm σ * X * (pm σ)ᴴ = X.submatrix σ σ := by
  ext i j
  simp [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, eq_comm]

theorem pm_unit (σ : Equiv.Perm (Fin n)) : (pm σ)ᴴ * pm σ = 1 := by
  ext i j
  simp only [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases h : i = j <;> simp [h, eq_comm, Equiv.apply_eq_iff_eq_symm_apply]
  · intro k _ hk
    have : σ k ≠ i := fun e => hk (by rw [← e]; simp)
    simp [this]
  · simp

def dph (a : Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if i = a then Complex.I else 1

theorem dph_unit (a : Fin n) : (dph a)ᴴ * dph a = 1 := by
  rw [dph, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  by_cases hi : i = a <;> simp [hi]

theorem dph_conj {a b : Fin n} (hab : a ≠ b) :
    dph a * Matrix.single a b (1 : ℂ) * (dph a)ᴴ = Complex.I • Matrix.single a b (1 : ℂ) := by
  ext i j
  rw [dph, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  by_cases hi : a = i <;> by_cases hj : b = j
  · subst hi hj; simp [hab.symm]
  · simp [hj]
  · simp [hi]
  · simp [hi, hj]

theorem inv_trace (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → Xᴴ * X = 1 → L (U * X * Uᴴ) = L X) :
    ∀ X, L X = L 1 / n * X.trace := by

  have h' : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → L (U * X * Uᴴ) = L X := by
    intro U X hU
    let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      L.comp ((LinearMap.mulLeft ℂ U).comp (LinearMap.mulRight ℂ Uᴴ)) - L
    have hC : Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set _) ≤ LinearMap.ker C := by
      rw [Submodule.span_le]
      intro Y hY
      have hY' : Yᴴ * Y = 1 := hY.1
      simp only [SetLike.mem_coe, LinearMap.mem_ker, C, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← Matrix.mul_assoc]
      rw [h U Y hU hY', sub_self]
    have hX : X ∈ LinearMap.ker C := hC (by rw [span_unitary_matrix]; trivial)
    simpa [C, sub_eq_zero, ← Matrix.mul_assoc] using hX

  have hoff : ∀ a b : Fin n, a ≠ b → L (Matrix.single a b 1) = 0 := by
    intro a b hab
    have e := h' (dph a) (Matrix.single a b 1) (dph_unit a)
    rw [dph_conj hab, L.map_smul, smul_eq_mul] at e
    have : (Complex.I - 1) * L (Matrix.single a b 1) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (by simp [sub_eq_zero, Complex.ext_iff])
    · exact h0

  have hdiag : ∀ a b : Fin n, L (Matrix.single a a 1) = L (Matrix.single b b 1) := by
    intro a b
    have e := h' (pm (Equiv.swap a b)) (Matrix.single a a 1) (pm_unit _)
    rw [pm_conj] at e
    have : (Matrix.single a a (1 : ℂ)).submatrix (Equiv.swap a b) (Equiv.swap a b) = Matrix.single b b 1 := by
      have key : ∀ x, a = (Equiv.swap a b) x ↔ b = x := by
        intro x; rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, eq_comm]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.single_apply, key]
    rw [this] at e
    exact e.symm
  intro X
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : X = 0 := Subsingleton.elim _ _
    simp [this]
  set κ := L (Matrix.single (⟨0, hn⟩ : Fin n) ⟨0, hn⟩ 1)
  have hsum : ∀ Y : Matrix (Fin n) (Fin n) ℂ, L Y = κ * Y.trace := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    rw [Matrix.trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [show Matrix.single a a (Y a a) = Y a a • Matrix.single a a (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, smul_eq_mul, hdiag a ⟨0, hn⟩, Matrix.diag_apply]; ring
    · intro b _ hb
      rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, hoff a b (Ne.symm hb), smul_zero]
    · simp
  have h1 : L 1 = κ * n := by rw [hsum, trace_one, Fintype.card_fin]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hsum X, h1]; field_simp

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

section
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Hf (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (z : ℂ) (y : M2 n) : ℂ :=
  ∫ t, fz m e z (y * a * nU (herm t) * b) * ψ t

theorem isClosed_G : IsClosed {x : M2 n | InG x} := by
  show IsClosed {x : M2 n | xᴴ * JJ n * x = JJ n}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

instance instLC : LocallyCompactSpace (M2 n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

instance instFC : FirstCountableTopology (M2 n) :=
  inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

def Gs (n : ℕ) : Set (M2 n) := {x | InG x}

theorem continuousAt_fz {x : M2 n} (hx : InG x) (m : ℕ) (e : ℤ) (z : ℂ) :
    ContinuousAt (fun p : M2 n × ℂ => fz m e p.2 p.1) (x, z) := by
  have hdx : x.det ≠ 0 := (LoweringDerivative.isUnit_det_of_inG hx).ne_zero
  have hdet : Continuous (fun y : M2 n => y.det) := continuous_id.matrix_det
  have hdetn : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) := continuous_id.matrix_det
  have hu1 : Continuous (fun y : M2 n => u1 y) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply,
      smul_eq_mul]
    fun_prop
  have hub : ContinuousAt (fun y : M2 n => ub1 y) x :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      (contDiffOn_inverse_first_block i j).continuousOn.continuousAt (isOpen_det_ne.mem_nhds hdx)
  have hw : (u1 x).det * (ub1 x).det = ((Complex.normSq (u1 x).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  have hslit : (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := by
    rw [hw, Complex.ofReal_mem_slitPlane]
    exact Complex.normSq_pos.2 (det_first_block_ne_zero_group hx)
  show ContinuousAt (fun p : M2 n × ℂ =>
    p.1.det ^ e * (u1 p.1).det ^ (-(m : ℤ)) * ((u1 p.1).det * (ub1 p.1).det) ^ (-p.2)) (x, z)
  have hA : ContinuousAt (fun p : M2 n × ℂ => p.1.det) (x, z) := (hdet.comp continuous_fst).continuousAt
  have hB : ContinuousAt (fun p : M2 n × ℂ => (u1 p.1).det) (x, z) :=
    ((hu1.comp continuous_fst).matrix_det).continuousAt
  have hub' : ContinuousAt (fun y : M2 n => (ub1 y).det) x := hdetn.continuousAt.comp hub
  have hC : ContinuousAt (fun p : M2 n × ℂ => (ub1 p.1).det) (x, z) :=
    ContinuousAt.comp (g := fun y : M2 n => (ub1 y).det) (f := Prod.fst) (x := (x, z)) hub'
      continuous_fst.continuousAt
  refine ((hA.zpow₀ e (Or.inl hdx)).mul (hB.zpow₀ _ (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_
  exact (hB.mul hC).cpow continuous_snd.neg.continuousAt hslit

theorem inG_path {y a b : M2 n} (hy : InG y) (ha : InG a) (hb : InG b) (t : Fin n → Fin n → ℝ) :
    InG (y * a * nU (herm t) * b) := by
  have hH : (herm t)ᴴ = herm t := by
    ext i j
    simp only [herm, Matrix.conjTranspose_apply, Complex.star_def, map_add, map_div₀, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have hN : InG (nU (herm t)) := by
    show (nU (herm t))ᴴ * JJ n * nU (herm t) = JJ n
    simp [nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hH]
  exact inG_mul (inG_mul (inG_mul hy ha) hN) hb

private theorem continuous_nU_herm : Continuous (fun t : Fin n → Fin n → ℝ => nU (herm t)) := by
  have hherm : Continuous (fun t : Fin n → Fin n → ℝ => herm t) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  unfold nU
  exact continuous_const.matrix_fromBlocks hherm continuous_const continuous_const

private theorem continuous_fz_mul_nU_herm_mul {X : Type} [TopologicalSpace X] (m : ℕ) (e : ℤ)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) {a b : M2 n} (ha : InG a) (hb : InG b)
    (Y : X → M2 n) (hY : Continuous Y) (hYG : ∀ x, InG (Y x)) (Z : X → ℂ) (hZ : Continuous Z)
    (T : X → (Fin n → Fin n → ℝ)) (hT : Continuous T) :
    Continuous fun x => fz m e (Z x) (Y x * a * nU (herm (T x)) * b) * ψ (T x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine ContinuousAt.mul ?_ (hψ.comp hT).continuousAt
  have hG := inG_path (hYG x) ha hb (T x)
  have hP : Continuous fun x => (Y x * a * nU (herm (T x)) * b, Z x) :=
    (((hY.matrix_mul continuous_const).matrix_mul (continuous_nU_herm.comp hT)).matrix_mul
      continuous_const).prodMk hZ
  exact ContinuousAt.comp (g := fun p : M2 n × ℂ => fz m e p.2 p.1)
    (f := fun x => (Y x * a * nU (herm (T x)) * b, Z x)) (x := x)
    (continuousAt_fz hG m e (Z x)) hP.continuousAt

theorem continuous_Hf (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a b : M2 n} (ha : InG a) (hb : InG b) :
    Continuous fun q : ↥(Gs n) × ℂ => Hf m e ψ a b q.2 q.1.1 := by
  haveI : LocallyCompactSpace ↥(Gs n) := (isClosed_G (n := n)).locallyCompactSpace
  have hF := continuous_fz_mul_nU_herm_mul (X := (↥(Gs n) × ℂ) × (Fin n → Fin n → ℝ)) m e hψ ha hb
    (fun p => p.1.1.1) (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
    (fun p => p.1.1.2) (fun p => p.1.2) (continuous_snd.comp continuous_fst) (fun p => p.2) continuous_snd
  have key := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin n → Fin n → ℝ)))
    (f := fun (q : ↥(Gs n) × ℂ) t => fz m e q.2 (q.1.1 * a * nU (herm t) * b) * ψ t) hF hψc
  refine key.congr fun q => ?_
  unfold Hf
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
    rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]

theorem differentiable_Hf (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a b y : M2 n} (ha : InG a) (hb : InG b) (hy : InG y) : Differentiable ℂ fun z => Hf m e ψ a b z y := by
  have hC : IsCompact (tsupport ψ) := hψc
  haveI : IsFiniteMeasure ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) :=
    isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hnull : ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) (tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' (isClosed_tsupport ψ).measurableSet, Set.compl_inter_self, measure_empty]
  have hF := continuous_fz_mul_nU_herm_mul (X := (Fin n → Fin n → ℝ) × ℂ) m e hψ ha hb (fun _ => y) continuous_const
    (fun _ => hy) (fun p => p.2) continuous_snd (fun p => p.1) continuous_fst
  have hdiff : ∀ t ∈ tsupport ψ,
      DifferentiableOn ℂ (fun z => fz m e z (y * a * nU (herm t) * b) * ψ t) Set.univ := by
    intro t _ z _
    have hG := inG_path hy ha hb t
    have hc : (u1 (y * a * nU (herm t) * b)).det * (ub1 (y * a * nU (herm t) * b)).det ≠ 0 := by
      refine mul_ne_zero (det_first_block_ne_zero_group hG) ?_
      rw [inverse_first_block_eq_conjTranspose hG, Matrix.det_conjTranspose]
      exact star_ne_zero.2 (det_first_block_ne_zero_group hG)
    simp only [fz]
    exact (((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hc))).mul_const
      _).differentiableWithinAt
  have main := (AbsSt.holParam (Fin n → Fin n → ℝ) ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ))
    (tsupport ψ) hC hnull Set.univ (fun t z => fz m e z (y * a * nU (herm t) * b) * ψ t) isOpen_univ
    hF.continuousOn hdiff).1
  rw [differentiableOn_univ] at main
  have hEq : ∀ z, Hf m e ψ a b z y = ∫ t in tsupport ψ, fz m e z (y * a * nU (herm t) * b) * ψ t := by
    intro z
    unfold Hf
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]).symm
  simp only [hEq]
  exact main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

section
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem vacuum_at_zero_mul_compact (m : ℕ) (e : ℤ) (x : M2 n) {k : M2 n} (hk : InK k) :
    fz m e 0 (x * k) = fz m e 0 x * fz m e 0 k := by
  unfold fz
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  rw [first_cayley_block_mul_compact x hk, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow]
  ring

theorem norm_fz0K (m : ℕ) (e : ℤ) {k : M2 n} (hk : InK k) : star (fz m e 0 k) * fz m e 0 k = 1 := by
  have hk1 : Complex.normSq (det k) = 1 := by
    have h := congrArg Matrix.det hk.2
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      mul_comm, Complex.mul_conj] at h
    exact_mod_cast h
  have hu := normSq_det_u1K hk
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  unfold fz
  simp only [neg_zero, Complex.cpow_zero, mul_one, map_mul, map_zpow₀, hk1, hu, _root_.one_zpow]
  simp

theorem first_cayley_block_one : u1 (1 : M2 n) = 1 := by
  unfold u1
  rw [← Matrix.fromBlocks_one, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp
theorem second_cayley_block_one : u2 (1 : M2 n) = 1 := by
  unfold u2
  rw [← Matrix.fromBlocks_one, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)

include hK in
theorem ιK (k : Kg) : InK (ι k) := (hK _).mpr ⟨k, rfl⟩

theorem ι_inv (k : Kg) : ι k⁻¹ = (ι k)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← map_mul, inv_mul_cancel, map_one]

include hK in
theorem first_cayley_block_inv (k : Kg) : u1 (ι k⁻¹) = (u1 (ι k))⁻¹ := by
  have h : u1 (ι k⁻¹) * u1 (ι k) = 1 := by
    rw [← first_cayley_block_mul_compact _ (ιK ι hK k), ← map_mul, inv_mul_cancel, map_one, first_cayley_block_one]
  exact (Matrix.inv_eq_left_inv h).symm

include hK in
theorem second_cayley_block_inv (k : Kg) : u2 (ι k⁻¹) = (u2 (ι k))⁻¹ := by
  have h : u2 (ι k⁻¹) * u2 (ι k) = 1 := by
    rw [← second_cayley_block_mul_compact _ (ιK ι hK k), ← map_mul, inv_mul_cancel, map_one, second_cayley_block_one]
  exact (Matrix.inv_eq_left_inv h).symm

include hK in
theorem vacuum_at_zero_inv_star (m : ℕ) (e : ℤ) (k : Kg) : fz m e 0 (ι k⁻¹) = star (fz m e 0 (ι k)) := by
  have hk := ιK ι hK k
  have h1 : fz m e 0 (ι k⁻¹) * fz m e 0 (ι k) = 1 := by
    rw [← vacuum_at_zero_mul_compact m e _ hk, ← map_mul, inv_mul_cancel, map_one]
    unfold fz
    simp [first_cayley_block_one]
  have h2 := norm_fz0K m e hk
  have hne : fz m e 0 (ι k) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

include hK in
theorem rho_shift (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (k1 k : Kg) :
    rhoP ι m e Y (k1⁻¹ * k) = fz m e 0 (ι k1) * rhoP ι m e (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) k := by
  have ha := ιK ι hK k1
  have hb := ιK ι hK k
  have hdet : IsUnit (u2 (ι k1)).det := Matrix.isUnit_det_of_left_inverse (second_cayley_block_compact_unitary ha)
  unfold rhoP
  rw [map_mul, vacuum_at_zero_mul_compact m e _ hb, vacuum_at_zero_inv_star ι hK m e k1, second_cayley_block_mul_compact _ hb, first_cayley_block_mul_compact _ hb,
    second_cayley_block_inv ι hK k1, first_cayley_block_inv ι hK k1, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdet]
  simp only [star_mul', star_star, Matrix.mul_assoc]
  ring

theorem Hf_up (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b p y : M2 n} (ha : InG a) (hb : InG b)
    (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (z : ℂ) :
    Hf m e ψ a b z (p * y) = lam m e z p * Hf m e ψ a b z y := by
  simp only [Hf]
  rw [← integral_const_mul]
  congr 1; funext t
  rw [show p * y * a * nU (herm t) * b = p * (y * a * nU (herm t) * b) by simp only [Matrix.mul_assoc],
    fz_up hp hp21 (inG_path hy ha hb t)]
  ring

include hK in

theorem tOp_formula (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b p : M2 n} (ha : InG a) (hb : InG b)
    (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (k1 : Kg) (Y : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) (p * ι k1) =
      lam m e z p * fz m e 0 (ι k1) * tOp μ ι (rhoP ι m e (u2 (ι k1) * Y * (u1 (ι k1))⁻¹)) ψ a b (fz m e z) 1 := by
  unfold tOp
  have hs := integral_mul_left_eq_self (μ := μ) (fun k => rhoP ι m e Y k *
    ∫ t, fz m e z (p * ι k1 * ι k * a * nU (herm t) * b) * ψ t) k1⁻¹
  rw [← hs, mul_assoc, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext k
  have hι : ι k1 * ι (k1⁻¹ * k) = ι k := by
    rw [← map_mul, mul_inv_cancel_left]
  have hH := Hf_up m e ψ ha hb hp hp21 (ιK ι hK k).1 z
  unfold Hf at hH
  rw [rho_shift ι hK m e Y k1 k, Matrix.mul_assoc p (ι k1), hι, hH]
  simp only [Matrix.one_mul]
  ring

end Main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

section
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem rhoP_add {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (X Y : Matrix (Fin n) (Fin n) ℂ) (k : Kg) :
    rhoP ι m e (X + Y) k = rhoP ι m e X k + rhoP ι m e Y k := by
  simp only [rhoP, Matrix.mul_add, Matrix.add_mul, trace_add, mul_add, star_add]

theorem rhoP_smul {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (k : Kg) :
    rhoP ι m e (c • X) k = star c * rhoP ι m e X k := by
  simp only [rhoP, Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul, star_mul']; ring

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
  (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ)
  (hψc : HasCompactSupport ψ) {a b : M2 n} (ha : InG a) (hb : InG b)

def abelian₂ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  tOp μ ι (rhoP ι m e X) ψ a b (fz m e z) 1

theorem Lam_eq (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z X = ∫ k, rhoP ι m e X k * Hf m e ψ a b z (ι k) ∂μ := by
  simp only [abelian₂, tOp, Hf, one_mul]

include hι hK hψ hψc ha hb in
theorem continuous_integrand (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun k => rhoP ι m e X k * Hf m e ψ a b z (ι k) := by
  have hG : ∀ k, InG (ι k) := fun k => LoweringDerivative.inG_of_inK ((hK (ι k)).2 ⟨k, rfl⟩)
  have h1 : Continuous (rhoP (⇑ι) m e X) := LoweringDerivative.continuous_rhoP (⇑ι) hι hG m e X
  have h2 := continuous_Hf m e hψ hψc ha hb
  have h3 : Continuous fun k : Kg => ((⟨ι k, hG k⟩ : Gs n), z) :=
    (Continuous.subtype_mk hι (fun k => hG k)).prodMk continuous_const
  have h4 : Continuous fun k : Kg => Hf m e ψ a b z (ι k) := by
    have h5 := h2.comp h3
    simp only [Function.comp_def] at h5
    exact h5
  exact h1.mul h4

include hι hK hψ hψc ha hb in
theorem integrable_integrand (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Integrable (fun k => rhoP ι m e X k * Hf m e ψ a b z (ι k)) μ := by
  exact (continuous_integrand ι hι hK m e hψ hψc ha hb z X).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

include hι hK hψ hψc ha hb in
theorem Lam_add (z : ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z (X + Y) = abelian₂ μ ι m e ψ a b z X + abelian₂ μ ι m e ψ a b z Y := by
  simp only [Lam_eq, rhoP_add, add_mul]
  exact integral_add (integrable_integrand μ ι hι hK m e hψ hψc ha hb z X)
    (integrable_integrand μ ι hι hK m e hψ hψc ha hb z Y)

theorem Lam_smul (z c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z (c • X) = star c * abelian₂ μ ι m e ψ a b z X := by
  simp only [Lam_eq, rhoP_smul, mul_assoc, integral_const_mul]

private theorem inK_fromBlocks_unitary_diag (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    InK (Matrix.fromBlocks U 0 0 U : M2 n) := by
  refine ⟨?_, ?_⟩
  · simp [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU]
  · simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU]

private theorem u1_fromBlocks_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (y : M2 n) :
    u1 (Matrix.fromBlocks U 0 0 U * y) = U * u1 y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [u1, Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.mul_smul]

private theorem u2_fromBlocks_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (y : M2 n) :
    u2 (Matrix.fromBlocks U 0 0 U * y) = U * u2 y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [u2, Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

include hK ha hb in
theorem Lam_inv (z : ℂ) {U X : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (hX : Xᴴ * X = 1) :
    abelian₂ μ ι m e ψ a b z (U * X * Uᴴ) = abelian₂ μ ι m e ψ a b z X := by
  obtain ⟨k0, hk0⟩ := (hK _).1 (inK_fromBlocks_unitary_diag U hU)
  have hG : ∀ k, InG (ι k) := fun k => LoweringDerivative.inG_of_inK ((hK (ι k)).2 ⟨k, rfl⟩)
  have hpG : InG (Matrix.fromBlocks U 0 0 U : M2 n) := LoweringDerivative.inG_of_inK (inK_fromBlocks_unitary_diag U hU)
  have hp21 : Matrix.toBlocks₂₁ (Matrix.fromBlocks U 0 0 U : M2 n) = 0 :=
    Matrix.toBlocks_fromBlocks₂₁ _ _ _ _
  have hUi : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  have hd : star U.det * U.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hU, Matrix.det_one]
  have hn : Complex.normSq U.det = 1 := by
    have h : (Complex.normSq U.det : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hd
    exact_mod_cast h
  have hl : ∀ w : ℂ, lam m e w (Matrix.fromBlocks U 0 0 U : M2 n) =
      (U.det * U.det) ^ e * U.det ^ (-(m : ℤ)) := by
    intro w
    simp only [lam, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_fromBlocks_zero₂₁, hn, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
  have h1 : star ((U.det * U.det) ^ e) * (U.det * U.det) ^ e = 1 := by
    rw [star_zpow₀, ← mul_zpow, star_mul',
      show star U.det * star U.det * (U.det * U.det) = (star U.det * U.det) * (star U.det * U.det) by ring,
      hd, one_mul, _root_.one_zpow]
  have h2 : star (U.det ^ (-(m : ℤ))) * U.det ^ (-(m : ℤ)) = 1 := by
    rw [star_zpow₀, ← mul_zpow, hd, _root_.one_zpow]
  have hlam : star (lam m e 0 (Matrix.fromBlocks U 0 0 U : M2 n)) *
      lam m e z (Matrix.fromBlocks U 0 0 U : M2 n) = 1 := by
    rw [hl, hl]
    calc star ((U.det * U.det) ^ e * U.det ^ (-(m : ℤ))) * ((U.det * U.det) ^ e * U.det ^ (-(m : ℤ)))
        = (star ((U.det * U.det) ^ e) * (U.det * U.det) ^ e) *
          (star (U.det ^ (-(m : ℤ))) * U.det ^ (-(m : ℤ))) := by
          rw [star_mul']
          ring
      _ = 1 := by rw [h1, h2, one_mul]
  have aux : ∀ A B C : ℂ, star (lam m e 0 (Matrix.fromBlocks U 0 0 U : M2 n)) * A * B *
      (lam m e z (Matrix.fromBlocks U 0 0 U : M2 n) * C) = A * B * C := by
    intro A B C
    linear_combination (A * B * C) * hlam
  have key : ∀ k, rhoP ι m e (U * X * Uᴴ) (k0 * k) * Hf m e ψ a b z (ι (k0 * k)) =
      rhoP ι m e X k * Hf m e ψ a b z (ι k) := by
    intro k
    have hm : (u2 (ι k))⁻¹ * Uᴴ * (U * X * Uᴴ) * (U * u1 (ι k)) = (u2 (ι k))⁻¹ * X * u1 (ι k) := by
      calc (u2 (ι k))⁻¹ * Uᴴ * (U * X * Uᴴ) * (U * u1 (ι k))
          = (u2 (ι k))⁻¹ * (Uᴴ * U) * X * (Uᴴ * U) * u1 (ι k) := by
            simp only [Matrix.mul_assoc]
        _ = (u2 (ι k))⁻¹ * X * u1 (ι k) := by
            rw [hU]
            simp only [Matrix.mul_one]
    simp only [rhoP]
    rw [map_mul, hk0, Hf_up m e ψ ha hb hpG hp21 (hG k) z, fz_up hpG hp21 (hG k) m e 0,
      u1_fromBlocks_diag_mul, u2_fromBlocks_diag_mul, Matrix.mul_inv_rev, hUi, hm]
    simp only [star_mul']
    exact aux _ _ _
  have hinv := integral_mul_left_eq_self (μ := μ)
    (fun k => rhoP ι m e (U * X * Uᴴ) k * Hf m e ψ a b z (ι k)) k0
  simp only [key] at hinv
  rw [Lam_eq, Lam_eq]
  exact hinv.symm

end Main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

section
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
  (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ)
  (hψc : HasCompactSupport ψ) {a b : M2 n} (ha : InG a) (hb : InG b)

include hι hK hψ hψc ha hb in
theorem Lam_trace (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z X = abelian₂ μ ι m e ψ a b z 1 / n * star X.trace := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Y => star (abelian₂ μ ι m e ψ a b z Y)
      map_add' := fun Y W => by simp [Lam_add μ ι hι hK m e hψ hψc ha hb]
      map_smul' := fun c Y => by simp [Lam_smul, mul_comm] }
  have h := inv_trace L (fun U Y hU hY => by
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Lam_inv μ ι hK m e ha hb z hU hY]) X
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at h
  have h' := congrArg star h
  rw [star_star] at h'
  rw [h']
  simp [star_div₀, mul_comm]

include hι hK hψ hψc ha hb in
theorem Lam_diff : Differentiable ℂ fun z => abelian₂ μ ι m e ψ a b z 1 := by
  have hιK : ∀ k, InK (ι k) := ιK ι hK
  have hιG : ∀ k, InG (ι k) := fun k => (hιK k).1
  have hb21 : Continuous fun x : M2 n => toBlocks₂₁ x :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))
  have hb22 : Continuous fun x : M2 n => toBlocks₂₂ x :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))
  have hu1 : Continuous fun x : M2 n => u1 x := by
    show Continuous fun x : M2 n => Complex.I • toBlocks₂₁ x + toBlocks₂₂ x
    exact (hb21.const_smul Complex.I).add hb22
  have hu2 : Continuous fun x : M2 n => u2 x := by
    show Continuous fun x : M2 n => -(Complex.I • toBlocks₂₁ x) + toBlocks₂₂ x
    exact (hb21.const_smul Complex.I).neg.add hb22
  have hR : (rhoP ⇑ι m e 1) = fun k =>
      star ((det (ι k) ^ e * (u1 (ι k)).det ^ (-(m : ℤ))) * ((u2 (ι k))ᴴ * u1 (ι k)).trace) := by
    funext k
    rw [rhoP, Matrix.mul_one, Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary (hιK k))]
    simp [fz]
  have hRc : Continuous (rhoP ⇑ι m e 1) := by
    rw [hR]
    refine Continuous.star (Continuous.mul (Continuous.mul ?_ ?_) ?_)
    · exact hι.matrix_det.zpow₀ e fun k => Or.inl (LoweringDerivative.isUnit_det_of_inG (hιG k)).ne_zero
    · exact (hu1.comp hι).matrix_det.zpow₀ _ fun k => Or.inl (det_first_block_ne_zero_group (hιG k))
    · exact (((hu2.comp hι).matrix_conjTranspose).matrix_mul (hu1.comp hι)).matrix_trace
  have hH : Continuous fun p : Kg × ℂ => Hf m e ψ a b p.2 (ι p.1) := by
    have h1 := continuous_Hf m e hψ hψc ha hb
    refine h1.comp (f := fun p : Kg × ℂ => ((⟨ι p.1, hιG p.1⟩ : Gs n), p.2)) ?_
    refine Continuous.prodMk ?_ continuous_snd
    refine Continuous.subtype_mk ?_ _
    exact hι.comp continuous_fst
  set G : Kg → ℂ → ℂ := fun k w => rhoP ⇑ι m e 1 k * Hf m e ψ a b w (ι k) with hGdef
  have hG : Continuous (Function.uncurry G) := (hRc.comp continuous_fst).mul hH
  have hGd : ∀ k, Differentiable ℂ (G k) := fun k =>
    (differentiable_Hf m e hψ hψc ha hb (hιG k)).const_mul _
  have hLam : (fun z => abelian₂ μ ι m e ψ a b z 1) = fun z => ∫ k, G k z ∂μ := by
    funext z
    rw [Lam_eq]
  rw [hLam]
  intro z0
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall z0 2)).exists_bound_of_continuousOn
    hG.continuousOn
  have hbd : ∀ k, ∀ z ∈ Metric.ball z0 1, ‖deriv (G k) z‖ ≤ C := by
    intro k z hz
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) (C := C) one_pos
      (hGd k).diffContOnCl (fun w hw => by
        apply hC (k, w)
        refine ⟨Set.mem_univ _, ?_⟩
        rw [Metric.mem_closedBall]
        rw [Metric.mem_sphere] at hw
        rw [Metric.mem_ball] at hz
        linarith [dist_triangle w z z0])
    simpa using this
  have hmeas : Measurable fun k => deriv (G k) z0 :=
    by
    have hm := measurable_deriv_with_param (𝕜 := ℂ) (F := ℂ) (f := G) hG
    exact hm.comp (f := fun k : Kg => (k, z0)) (measurable_id.prodMk measurable_const)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun z k => G k z)
    (F' := fun z k => deriv (G k) z) (x₀ := z0) (bound := fun _ => C)
    (Metric.ball_mem_nhds z0 one_pos)
    (Filter.Eventually.of_forall fun z => (hG.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (integrable_integrand μ ι hι hK m e hψ hψc ha hb z0 1)
    hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k z hz => hbd k z hz)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k z _ => ((hGd k) z).hasDerivAt)
  exact key.2.differentiableAt

end Main

theorem lt2 : MultiplicityOneTestOperators := by
  intro n m e Kg _ _ _ _ _ _ μ _ ι hι hK ψ a b hψ hψc ha hb
  refine ⟨fun z => -(abelian₂ μ ι m e ψ a b z 1 / n), ?_, ?_⟩
  · exact ((Lam_diff μ ι hι hK m e hψ hψc ha hb).div_const _).neg
  · intro Y z x hx
    obtain ⟨p, k, hp, hk, hpk⟩ := AbsSt.iwa n (AbsSt.mkGR x hx)
    have hxe : x = mR p * mR k := by
      have h := congrArg mR hpk
      rw [AbsSt.mR_mkGR] at h
      rw [h]
      rfl
    obtain ⟨k1, hk1⟩ := (hK (mR k)).mp hk
    have hpG : InG (mR p) := p.2
    have hk1K : InK (ι k1) := hk1 ▸ hk
    rw [hxe, ← hk1, tOp_formula μ ι hK m e ψ ha hb hpG hp k1 Y z]
    change lam m e z (mR p) * fz m e 0 (ι k1) *
      abelian₂ μ ι m e ψ a b z (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) = _
    rw [Lam_trace μ ι hι hK m e hψ hψc ha hb, eQ, fz_up hpG hp hk1K.1, Om_up hpG hp hk1K.1,
      fz_K m e z hk1K, Om_K hk1K, Matrix.inv_eq_left_inv (first_cayley_block_compact_unitary hk1K),
      Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk1K)]
    have htr : star (u2 (ι k1) * Y * (u1 (ι k1))ᴴ).trace = ((u2 (ι k1))ᴴ * u1 (ι k1) * Yᴴ).trace := by
      rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    rw [htr]
    simp only [Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul,
      ← Matrix.mul_assoc]
    ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

namespace PositivityTheory.Rg.Sw.HSt

theorem lt2 : MultiplicityOneTestOperators := CompactCayleyBlocks.lt2

end PositivityTheory.Rg.Sw.HSt
end
end
