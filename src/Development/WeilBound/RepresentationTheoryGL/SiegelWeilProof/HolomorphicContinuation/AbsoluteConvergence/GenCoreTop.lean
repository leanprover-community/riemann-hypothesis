import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CayleyInverseConjTransposeMulApply
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilations
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousGramX
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DenseCell
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerFin
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalCharacterInvMul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolParam
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RightConn
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CompactUnitaryT2Space
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenTop

section
noncomputable section

open Matrix Filter Topology Set
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

lemma JJ_mul_JJ (n : ℕ) : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  congr 1 <;> simp

lemma det_JJ_ne (n : ℕ) : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ n)
  rw [det_mul, h, zero_mul, det_neg, det_one] at this
  simp at this

lemma exists_of_InG {M : M2 n} (h : InG M) : ∃ g : GR n, mR g = M := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have hdet : M.det ≠ 0 := by
    intro h0
    have hd := congrArg det h'
    rw [det_mul, det_mul, h0, mul_zero] at hd
    exact det_JJ_ne n hd.symm
  exact ⟨⟨GeneralLinearGroup.mkOfDetNeZero M hdet, h⟩, rfl⟩

lemma InG_JJ_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (JJ n * nU b) := by
  show (JJ n * nU b)ᴴ * JJ n * (JJ n * nU b) = JJ n
  simp [JJ, nU, fromBlocks_multiply, fromBlocks_conjTranspose, hb.eq]

lemma InG_lower (s : ℝ) : InG (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1) := by
  show (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1)ᴴ * JJ n *
    fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1 = JJ n
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose]

lemma yJyH {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have hJ := JJ_mul_JJ n
  have h1 : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by
    have e : (-(JJ n * Mᴴ * JJ n)) * M = -(JJ n * (Mᴴ * JJ n * M)) := by
      simp [Matrix.mul_assoc]
    rw [e, h', hJ, neg_neg]
  have h2 := mul_eq_one_comm.mpr h1
  calc M * JJ n * Mᴴ = (M * (-(JJ n * Mᴴ * JJ n))) * JJ n := by
        simp [Matrix.mul_assoc, hJ]
    _ = JJ n := by rw [h2, Matrix.one_mul]

lemma lowerDiagonalBlockAsGL {M : M2 n} (h : InG M) : M.toBlocks₂₁ * M.toBlocks₂₂ᴴ = M.toBlocks₂₂ * M.toBlocks₂₁ᴴ := by
  have h2 := congrArg toBlocks₂₂ (yJyH h)
  rw [← fromBlocks_toBlocks M] at h2
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h2
  exact (neg_add_eq_zero.mp h2).symm

end PositivityTheory.Rg.Sw.AbsSt.SZ
end
end

section
noncomputable section

open Matrix Filter Topology Set Polynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def lowM (n : ℕ) (s : ℝ) : M2 n := fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1

lemma lowM_mul (s s' : ℝ) : lowM n s * lowM n s' = lowM n (s + s') := by
  simp only [lowM, fromBlocks_multiply]
  simp [add_smul]

lemma lowM_zero : lowM n 0 = 1 := by
  unfold lowM; simp [fromBlocks_one]

def lowU (n : ℕ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨lowM n s, lowM n (-s), by rw [lowM_mul, add_neg_cancel, lowM_zero], by rw [lowM_mul, neg_add_cancel, lowM_zero]⟩

def lowG (n : ℕ) (s : ℝ) : GR n := ⟨lowU n s, InG_lower s⟩

lemma lowG_cont : Continuous (lowG n) := by
  unfold lowG
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have hc : Continuous (fun s : ℝ => lowM n s) := by
    unfold lowM
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      (Complex.continuous_ofReal.smul continuous_const) continuous_const
  exact ⟨hc, hc.comp continuous_neg⟩

lemma lowG_zero : lowG n 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact lowM_zero

lemma mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

lemma lower_left_block_lowering_mul (y : GR n) (s : ℝ) :
    (mR (y * lowG n s)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (s : ℂ) • (mR y).toBlocks₂₂ := by
  rw [mR_mul]
  show (mR y * lowM n s).toBlocks₂₁ = _
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  unfold lowM
  rw [fromBlocks_multiply]
  simp

lemma dense_cell (y : GR n) : y ∈ closure {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, C = (mR y).toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (mR y).toBlocks₂₂ := ⟨_, rfl⟩
  have hG : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hgg : mR y * mR y⁻¹ = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    rfl
  have hJJ : JJ n * JJ n = -1 := by
    rw [JJ, fromBlocks_multiply]
    simp [← fromBlocks_one, fromBlocks_neg]
  have key : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have h1 : (mR y)ᴴ * JJ n = JJ n * mR y⁻¹ := by
      calc (mR y)ᴴ * JJ n = (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hgg, Matrix.mul_one]
        _ = ((mR y)ᴴ * JJ n * mR y) * mR y⁻¹ := by simp only [Matrix.mul_assoc]
        _ = JJ n * mR y⁻¹ := by rw [hG]
    calc mR y * JJ n * (mR y)ᴴ = mR y * JJ n * (mR y)ᴴ * (JJ n * JJ n) * (-1) := by
          rw [hJJ]; simp
      _ = mR y * JJ n * ((mR y)ᴴ * JJ n) * JJ n * (-1) := by simp only [Matrix.mul_assoc]
      _ = mR y * (JJ n * JJ n) * mR y⁻¹ * JJ n * (-1) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = JJ n := by
          rw [hJJ]
          simp [hgg]
  have hherm : C * Dᴴ = D * Cᴴ := by
    have hb := congrArg Matrix.toBlocks₂₂ key
    rw [← fromBlocks_toBlocks (mR y), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at hb
    simp at hb
    rw [← hC, ← hD] at hb
    exact (neg_add_eq_zero.mp hb).symm
  have hpos : ((C * Cᴴ + D * Dᴴ).det) ≠ 0 := by
    have hu : IsUnit (mR y) := ⟨(y : GL (Fin n ⊕ Fin n) ℂ), rfl⟩
    open ComplexOrder in
    have hpd : ((mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr).PosDef :=
      (Matrix.PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_iff_isUnit.mpr hu)).submatrix Sum.inr_injective
    have he : (mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr = C * Cᴴ + D * Dᴴ := by
      change Matrix.toBlocks₂₂ (mR y * (mR y)ᴴ) = _
      rw [hC, hD]
      conv_lhs => rw [← fromBlocks_toBlocks (mR y), fromBlocks_conjTranspose, fromBlocks_multiply]
      simp
    rw [← he]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit |>.ne_zero
  have hprod : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = C * Cᴴ + D * Dᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [← hherm, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  have hI : (C + Complex.I • D).det ≠ 0 := by
    intro h
    apply hpos
    rw [← hprod, Matrix.det_mul, h, zero_mul]
  let P : Polynomial ℂ :=
    Matrix.det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  have hev : ∀ r : ℂ, P.eval r = (C + r • D).det := by
    intro r
    show Polynomial.evalRingHom r (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP : P ≠ 0 := fun h => hI (by rw [← hev, h, Polynomial.eval_zero])
  have hfin : {s : ℝ | P.eval (s : ℂ) = 0}.Finite := by
    apply Set.Finite.subset ((P.roots.toFinset.finite_toSet).preimage
      Complex.ofReal_injective.injOn)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp [Polynomial.mem_roots hP, hs]
  have hT : Tendsto (fun s : ℝ => y * lowG n s) (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
    have h0 : Tendsto (fun s : ℝ => y * lowG n s) (𝓝 0) (𝓝 (y * lowG n 0)) :=
      (continuous_const.mul lowG_cont).tendsto 0
    rw [lowG_zero, mul_one] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hT
  have hopen : ({s : ℝ | P.eval (s : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hfin.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with s hs hs0
  show ((mR (y * lowG n s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_lowering_mul, ← hC, ← hD, ← hev]
  intro h
  exact hs ⟨h, hs0⟩

end PositivityTheory.Rg.Sw.AbsSt.SZ
end
end

section
noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

lemma cell_decomp (y : GR n) (hy : ((mR y).toBlocks₂₁).det ≠ 0) :
    ∃ (p g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian ∧ mR g = JJ n * nU b ∧
      (mR p).toBlocks₂₁ = 0 ∧ y = p * g := by
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  have hyG : InG (mR y) := y.2
  have hrel : C * Dᴴ = D * Cᴴ := lowerDiagonalBlockAsGL hyG
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hy
  have hCHu : IsUnit (Cᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hy)
  set b := C⁻¹ * D with hb
  have hbH : b.IsHermitian := by
    show bᴴ = b
    calc bᴴ = Dᴴ * (Cᴴ)⁻¹ := by
            rw [hb, conjTranspose_mul, conjTranspose_nonsing_inv]
      _ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
            rw [← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]
      _ = b := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one, hb]
  obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hbH)
  set N : M2 n := fromBlocks (-b) (-1) 1 0 with hN
  have h1 : mR g⁻¹ * mR g = 1 := by
    rw [← SZ.mR_mul, inv_mul_cancel]
    rfl
  have h2 : mR g * N = 1 := by
    rw [hg, hN]
    simp only [JJ, nU, fromBlocks_multiply]
    rw [← fromBlocks_one]
    congr 1 <;> simp
  have hM : mR g⁻¹ = N := by
    calc mR g⁻¹ = mR g⁻¹ * (mR g * N) := by rw [h2, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨y * g⁻¹, g, b, hbH, hg, ?_, (inv_mul_cancel_right y g).symm⟩
  rw [SZ.mR_mul, hM, ← fromBlocks_toBlocks (mR y), hN, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  rw [← hC, ← hD, Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ hCu,
    Matrix.one_mul, neg_add_cancel]

end PositivityTheory.Rg.Sw.AbsSt.SZ

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SZ

theorem secZero : NullIff → SecZero := by
  intro hN m n ε c t p q e sL ρ hL P
  have ht : t ≠ 0 := by
    rcases hL.sign with ⟨h, -, -⟩ | ⟨h, -, -⟩
    · rw [h]; exact hL.cpos.ne'
    · rw [h]; exact neg_ne_zero.2 hL.cpos.ne'
  obtain ⟨C, hC, hcell⟩ := hL.cell
  rw [hN m n ε c t hL.cpos ht P]
  constructor
  · intro h y
    have hS : {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} ⊆ {z | sL P z = 0} := by
      intro z hz
      obtain ⟨p', g, b, hb, hg, hp, rfl⟩ := cell_decomp z hz
      show sL P (p' * g) = 0
      rw [hL.law P p' g hp, hcell P g b hb hg, h b hb, mul_zero, mul_zero]
    have hcl : IsClosed {z : GR n | sL P z = 0} := isClosed_eq (hL.cont P) continuous_const
    exact hcl.closure_subset_iff.2 hS (dense_cell y)
  · intro h b hb
    obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hb)
    have hh := hcell P g b hb hg
    rw [h g] at hh
    exact (mul_eq_zero.1 hh.symm).resolve_left hC

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

theorem groupPart : GroupPart := by
  intro n X a ha
  exact ⟨dil_mul ha, dil_zero ha, dil_up ha, cont_dil ha, fun y hy s => up_mul hy (dil_up ha s), cell_dec,
    fun g b hg h => conj_cell ha g b hg h, fun y hy s => cell_mul ha y hy s, dense_cell,
    fun p q e h => weight_factor_dilation ha p q e h⟩

end PositivityTheory.Rg.Sw.AbsSt.DF
end

section
namespace PositivityTheory.Rg.Sw.AbsSt

theorem derivative_vacuum_section : DerivativeVacuumDilations := DF.derivative_vacuum_of_parts DF.gaussPart DF.groupPart

end PositivityTheory.Rg.Sw.AbsSt
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.LocOpA

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 := by
  exact (Matrix.isUnits_det_units (g : GL (Fin n ⊕ Fin n) ℂ)).ne_zero

theorem continuous_toBlocks₂₁ : Continuous (fun M : M2 n => M.toBlocks₂₁) := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inr i) (Sum.inl j)

theorem continuous_toBlocks₂₂ : Continuous (fun M : M2 n => M.toBlocks₂₂) := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inr i) (Sum.inr j)

theorem continuous_det_first_block : Continuous (fun g : GR n => (u1 (mR g)).det) := by
  show Continuous fun g : GR n => (Complex.I • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂).det
  have h1 : Continuous fun g : GR n => (mR g).toBlocks₂₁ := continuous_toBlocks₂₁.comp continuous_mR
  have h2 : Continuous fun g : GR n => (mR g).toBlocks₂₂ := continuous_toBlocks₂₂.comp continuous_mR
  exact ((continuous_const (y := Complex.I)).smul h1 |>.add h2).matrix_det

theorem continuous_det_second_block : Continuous (fun g : GR n => (u2 (mR g)).det) := by
  show Continuous fun g : GR n => (-(Complex.I • (mR g).toBlocks₂₁) + (mR g).toBlocks₂₂).det
  have h1 : Continuous fun g : GR n => (mR g).toBlocks₂₁ := continuous_toBlocks₂₁.comp continuous_mR
  have h2 : Continuous fun g : GR n => (mR g).toBlocks₂₂ := continuous_toBlocks₂₂.comp continuous_mR
  exact ((continuous_const (y := Complex.I)).smul h1 |>.neg.add h2).matrix_det

theorem local_spherical_function_ne_zero (p q : ℤ) (g : GR n) : f0 p q (mR g) ≠ 0 := by
  unfold f0
  exact mul_ne_zero (zpow_ne_zero _ (det_first_block_ne_zero_group (inG_of g))) (zpow_ne_zero _ (det_second_cayley_block_ne (inG_of g)))

theorem weight_factor_ne_zero (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0
  exact mul_ne_zero (zpow_ne_zero _ (det_mR_ne g)) (local_spherical_function_ne_zero _ _ g)

theorem continuous_weight_factor (p q : ℕ) (e : ℤ) : Continuous (fun g : GR n => F0 p q e g) := by
  unfold F0 f0
  refine Continuous.mul (Continuous.zpow₀ (Continuous.matrix_det continuous_mR) e (fun g => Or.inl (det_mR_ne g))) ?_
  exact Continuous.mul (Continuous.zpow₀ continuous_det_first_block _ (fun g => Or.inl (det_first_block_ne_zero_group (inG_of g))))
    (Continuous.zpow₀ continuous_det_second_block _ (fun g => Or.inl (det_second_cayley_block_ne (inG_of g))))

theorem hLoc_pos (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.2 (pow_pos (norm_pos_iff.2 (det_first_block_ne_zero_group (inG_of g))) 2)

theorem continuous_hLoc : Continuous (fun g : GR n => hLoc g) := by
  unfold hLoc
  exact (continuous_det_first_block.norm.pow 2).inv₀ fun g =>
    (pow_pos (norm_pos_iff.2 (det_first_block_ne_zero_group (inG_of g))) 2).ne'

theorem toBlocks₂₁_one : (1 : M2 n).toBlocks₂₁ = 0 := by
  ext i j; simp [toBlocks₂₁]

theorem toBlocks₂₂_one : (1 : M2 n).toBlocks₂₂ = 1 := by
  ext i j; simp [toBlocks₂₂, Matrix.one_apply]

theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  have h1 : mR (1 : GR n) = 1 := rfl
  simp [F0, f0, u1, u2, h1, toBlocks₂₁_one, toBlocks₂₂_one]

def kSet (n : ℕ) : Set (M2 n) := {M | InK M}

theorem isCompact_kSet : IsCompact (kSet n) := by
  have hcl : IsClosed (kSet n) := by
    have hc : Continuous fun M : M2 n => Mᴴ := continuous_id.matrix_conjTranspose
    exact (isClosed_eq ((hc.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq (hc.matrix_mul continuous_id) continuous_const)
  have hbd : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbd.of_isClosed_subset hcl ?_
  intro M hM i _ j _
  have hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hM.2
  simpa using entry_norm_bound_of_unitary hu i j

def kOf (M : kSet n) : KR n := ⟨mkG M.1 M.2.1, M.2⟩

theorem continuous_kOf : Continuous (kOf (n := n)) :=
  Continuous.subtype_mk (continuous_mkG continuous_subtype_val (fun M => M.2.1)) _

theorem surj_kOf : Function.Surjective (kOf (n := n)) := by
  intro k
  refine ⟨⟨mR (k : GR n), k.2⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl

instance instCompactKR : CompactSpace (KR n) := by
  have : CompactSpace (kSet n) := isCompact_iff_compactSpace.1 isCompact_kSet
  exact Function.Surjective.compactSpace continuous_kOf surj_kOf

end PositivityTheory.Rg.Sw.AbsSt.LocOpA
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def jLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (w : ℂ) (g : GR n) : ℂ :=
  ∫ x, ((hLoc (g * A * nbEl x * B) : ℂ) ^ w * F0 p q e (g * A * nbEl x * B)) * ψ x

def czLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) [MeasurableSpace (KR n)] (μ : Measure (KR n))
    (w : ℂ) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ

theorem eigen (hI : Iwa) (hM : Mult) (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] (w : ℂ) (y : GR n) :
    ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * A * nbEl x * B) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * A * nbEl x * B)) * ψ x) ∂μ =
      czLoc p q e A B ψ μ w * ((hLoc y : ℂ) ^ w * F0 p q e y) := by
  obtain ⟨p0, k0, hp, hk0, rfl⟩ := hI n y
  have hM1 := (hM n p q e).1
  have hM2 := (hM n p q e).2
  have hJ : ∀ g : GR n, jLoc p q e A B ψ w (p0 * g) =
      ((hLoc p0 : ℂ) ^ w * F0 p q e p0) * jLoc p q e A B ψ w g := by
    intro g
    unfold jLoc
    rw [← integral_const_mul]
    congr 1
    funext x
    have h1 : p0 * g * A * nbEl x * B = p0 * (g * A * nbEl x * B) := by simp only [mul_assoc]
    rw [h1, (hM2 p0 _ hp).1, (hM2 p0 _ hp).2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (by unfold hLoc; positivity) (by unfold hLoc; positivity)]
    ring
  have hne : F0 p q e k0 ≠ 0 := by
    intro h0
    have h2 := (hM1 k0 k0⁻¹ (inv_mem hk0)).1
    rw [mul_inv_cancel, weight_factor_one, h0, zero_mul] at h2
    exact one_ne_zero h2
  let K0 : KR n := ⟨k0, hk0⟩
  have hK0 : (K0 : GR n) = k0 := rfl
  have hshift : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ =
      F0 p q e k0 * (F0 p q e ((K0 * k : KR n) : GR n))⁻¹ := by
    intro k
    rw [Subgroup.coe_mul, hK0, (hM1 k0 k k.2).1, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  calc _ = ∫ k : KR n, ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ((F0 p q e ((K0 * k : KR n) : GR n))⁻¹ * jLoc p q e A B ψ w ((K0 * k : KR n) : GR n)) ∂μ := by
        congr 1
        funext k
        show (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (p0 * k0 * (k : GR n)) = _
        rw [show p0 * k0 * (k : GR n) = p0 * ((K0 * k : KR n) : GR n) by
          rw [Subgroup.coe_mul, hK0, mul_assoc], hJ, hshift k]
        ring
    _ = ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self
          (fun k : KR n => (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n)) K0
    _ = _ := by
        rw [(hM1 p0 k0 hk0).1, (hM1 p0 k0 hk0).2]
        unfold czLoc
        ring

theorem cz_zero (p q : ℕ) (e : ℤ) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] (μ : Measure (KR n)) :
    czLoc p q e (mkG a ha) (mkG b hb) ψ μ 0 = (a.det * b.det) ^ e *
      ∫ k : KR n, (∫ x, f0 p q (mR (k : GR n) * a * nU (herm x) * b) * ψ x) * (f0 p q (mR (k : GR n)))⁻¹ ∂μ := by
  have hmul : ∀ g h : GR n, mR (g * h) = mR g * mR h := fun _ _ => rfl
  have hdetN : ∀ x, (nU (herm x) : M2 n).det = 1 := by
    intro x
    simp [nU, det_fromBlocks_zero₂₁]
  unfold czLoc
  rw [← integral_const_mul]
  congr 1
  funext k
  have hk : (mR (k : GR n)).det ^ e ≠ 0 := by
    apply zpow_ne_zero
    have h1 : (mR (k : GR n)).det * (mR ((k : GR n)⁻¹)).det = 1 := by
      rw [← det_mul, ← hmul, mul_inv_cancel]
      exact det_one
    exact left_ne_zero_of_mul_eq_one h1
  unfold jLoc
  simp only [Complex.cpow_zero, one_mul, F0, hmul, mR_mkG, nbEl, det_mul, hdetN, mul_one, mul_zpow,
    mul_assoc, integral_const_mul]
  generalize (mR (k : GR n)).det ^ e = D at hk ⊢
  have hD := inv_mul_cancel₀ hk
  rw [mul_inv]
  linear_combination (det a ^ e * (det b ^ e *
    ((∫ (x : Fin n → Fin n → ℝ), f0 (↑p) (↑q) (mR (k : GR n) * (a * (nU (herm x) * b))) * ψ x) *
      (f0 (↑p) (↑q) (mR (k : GR n)))⁻¹))) * hD

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def fLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (y : KR n × (Fin n → Fin n → ℝ)) (w : ℂ) : ℂ :=
  (F0 p q e (y.1 : GR n))⁻¹ * (((hLoc ((y.1 : GR n) * A * nbEl y.2 * B) : ℂ) ^ w *
    F0 p q e ((y.1 : GR n) * A * nbEl y.2 * B)) * ψ y.2)

theorem continuous_fLoc (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) :
    Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => fLoc p q e A B ψ y.1 y.2) := by
  have hg : Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => ((y.1.1 : GR n) * A * nbEl y.1.2 * B)) :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_const).mul
      (continuous_nbEl.comp (continuous_snd.comp continuous_fst))).mul continuous_const
  unfold fLoc
  refine (((continuous_weight_factor p q e).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).inv₀
    (fun _ => weight_factor_ne_zero _ _ _ _)).mul ?_
  refine ((Continuous.cpow ?_ continuous_snd ?_).mul ((continuous_weight_factor p q e).comp hg)).mul
    (hψ.comp (continuous_snd.comp continuous_fst))
  · exact Complex.continuous_ofReal.comp (continuous_hLoc.comp hg)
  · intro y
    exact Complex.ofReal_mem_slitPlane.2 (hLoc_pos _)

theorem continuous_fLoc_w (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (w : ℂ) :
    Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => fLoc p q e A B ψ y w) := by
  have h1 := continuous_fLoc p q e A B hψ
  have h2 : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => ((y, w) : (KR n × (Fin n → Fin n → ℝ)) × ℂ)) :=
    continuous_id.prodMk continuous_const
  have h3 := h1.comp h2
  exact h3

theorem cz_eq (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] (w : ℂ) :
    czLoc p q e A B ψ μ w =
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hint : Integrable (fun y => fLoc p q e A B ψ y w) ((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    ((continuous_fLoc_w p q e A B hψ.1 w).continuousOn).integrableOn_compact hK
  rw [← Measure.prod_restrict, Measure.restrict_univ] at hint ⊢
  rw [integral_prod _ hint]
  unfold czLoc jLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [fLoc]
  rw [integral_const_mul]
  congr 1
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have h0 : ψ x = 0 := by
    by_contra h
    exact hx (subset_tsupport ψ (Function.mem_support.2 h))
  simp [h0]

theorem cz_diff (hH : HolParam) (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] :
    Differentiable ℂ (czLoc p q e A B ψ μ) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hmeas : MeasurableSet ((univ : Set (KR n)) ×ˢ tsupport ψ) :=
    MeasurableSet.univ.prod (isClosed_tsupport ψ).measurableSet
  haveI : IsFiniteMeasure ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) hψ.2.1.measure_lt_top⟩
  have hnull : ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
      ((univ : Set (KR n)) ×ˢ tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' hmeas, compl_inter_self, measure_empty]
  have hcont := (continuous_fLoc p q e A B hψ.1).continuousOn (s := ((univ : Set (KR n)) ×ˢ tsupport ψ) ×ˢ (univ : Set ℂ))
  have hdiff : ∀ y ∈ ((univ : Set (KR n)) ×ˢ tsupport ψ),
      DifferentiableOn ℂ (fun w => fLoc p q e A B ψ y w) univ := by
    intro y _
    refine Differentiable.differentiableOn ?_
    unfold fLoc
    refine Differentiable.const_mul ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.const_cpow differentiable_id (Or.inl ?_)
    exact_mod_cast (hLoc_pos _).ne'
  have h := (hH (KR n × (Fin n → Fin n → ℝ)) ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
    _ hK hnull univ (fun y w => fLoc p q e A B ψ y w) isOpen_univ hcont hdiff).1
  have heq : czLoc p q e A B ψ μ = fun w =>
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    funext (cz_eq p q e A B hψ μ)
  rw [heq]
  exact differentiableOn_univ.1 h

set_option maxHeartbeats 800000 in
theorem locOp : LV → Iwa → Mult → HolParam → LocOp := by
  intro hLV hIwa hMult hHol n p q e hgood _ _ μ _ _
  let ι : KR n →* M2 n := (Units.coeHom (M2 n)).comp ((GR n).subtype.comp (KR n).subtype)
  have hι : Continuous ι := continuous_mR.comp continuous_subtype_val
  have hιs : ∀ g : M2 n, InK g ↔ ∃ k, ι k = g := by
    intro g
    constructor
    · intro hg
      exact ⟨kOf ⟨g, hg⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  obtain ⟨ψ, a, b, hψ, ha, hb, hne⟩ := hLV n p q hgood (KR n) μ ι hι hιs
  refine ⟨ψ, mkG a ha, mkG b hb, nbEl, czLoc p q e (mkG a ha) (mkG b hb) ψ μ, hψ, fun x => rfl, continuous_nbEl,
    cz_diff hHol p q e _ _ hψ μ, ?_, fun w y => eigen hIwa hMult p q e _ _ ψ μ w y⟩
  rw [cz_zero]
  refine mul_ne_zero (zpow_ne_zero _ (mul_ne_zero (det_mR_ne (mkG a ha)) (det_mR_ne (mkG b hb)))) ?_
  exact hne

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem inK_entry_le (M : M2 n) (hM : InK M) (i j : Fin n ⊕ Fin n) : ‖M i j‖ ≤ 1 := by
  exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hM.2) i j

theorem isCompact_inK : IsCompact {M : M2 n | InK M} := by
  have hB : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset ?_ ?_
  · have c1 : Continuous fun M : M2 n => Mᴴ * JJ n * M :=
      (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
    have c2 : Continuous fun M : M2 n => Mᴴ * M := continuous_id.matrix_conjTranspose.matrix_mul continuous_id
    exact (isClosed_eq c1 continuous_const).inter (isClosed_eq c2 continuous_const)
  · intro M hM
    simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact inK_entry_le M hM i j

def embK (k : KR n) : M2 n × (M2 n)ᵐᵒᵖ := Units.embedProduct (M2 n) (k : GR n).1

theorem isEmbedding_embK : Topology.IsEmbedding (embK (n := n)) :=
  Units.isEmbedding_embedProduct.comp (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)

theorem range_embK : Set.range (embK (n := n)) = (fun M : M2 n => (M, MulOpposite.op Mᴴ)) '' {M | InK M} := by
  ext ⟨A, B⟩
  constructor
  · rintro ⟨k, hk⟩
    have hK : InK (mR (k : GR n)) := k.2
    have hinv : ((((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) =
        (mR (k : GR n))ᴴ :=
      Units.inv_eq_of_mul_eq_one_left hK.2
    refine ⟨mR (k : GR n), hK, ?_⟩
    rw [← hk]
    simp only [embK, Units.embedProduct_apply, hinv]
    rfl
  · rintro ⟨M, hM, hMAB⟩
    have hM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hM.2
    let u : GL (Fin n ⊕ Fin n) ℂ := ⟨M, Mᴴ, hM', hM.2⟩
    let g : GR n := ⟨u, hM.1⟩
    have hg : g ∈ KR n := hM
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [← hMAB]
    rfl

theorem isCompact_KR : IsCompact (univ : Set (KR n)) := by
  rw [isEmbedding_embK.isCompact_iff, Set.image_univ, range_embK]
  exact isCompact_inK.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose))

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Dm (X : Fin n → ℝ) (s : ℝ) : M2 n :=
  fromBlocks (diagonal fun j => ((Real.exp (s * X j) : ℝ) : ℂ)) 0 0 (diagonal fun j => ((Real.exp (-(s * X j)) : ℝ) : ℂ))

theorem Dm_mul (X : Fin n → ℝ) (s t : ℝ) : Dm X s * Dm X t = Dm X (s + t) := by
  simp only [Dm, fromBlocks_multiply, diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 2
  · funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

theorem Dm_zero (X : Fin n → ℝ) : Dm X 0 = 1 := by
  simp [Dm, fromBlocks_one]

def dGL (X : Fin n → ℝ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨Dm X s, Dm X (-s), by rw [Dm_mul, add_neg_cancel, Dm_zero], by rw [Dm_mul, neg_add_cancel, Dm_zero]⟩

theorem diag_conjT_mul (f g : Fin n → ℝ) :
    (diagonal fun j => ((f j : ℝ) : ℂ))ᴴ * diagonal (fun j => ((g j : ℝ) : ℂ)) = diagonal fun j => ((f j * g j : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext j
  simp [Complex.conj_ofReal]

theorem inG_blocks (A B : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ * B = 1) : InG (fromBlocks A 0 0 B) := by
  have h' : Bᴴ * A = 1 := by
    have := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul] using this
  unfold InG JJ
  rw [fromBlocks_conjTranspose]
  simp only [conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [h, h']

theorem inG_Dm (X : Fin n → ℝ) (s : ℝ) : InG (Dm X s) := by
  apply inG_blocks
  rw [diag_conjT_mul, ← diagonal_one]
  congr 1
  funext j
  rw [← Real.exp_add]
  simp

def aD (X : Fin n → ℝ) (s : ℝ) : GR n := ⟨dGL X s, inG_Dm X s⟩

theorem isDil_aD (X : Fin n → ℝ) (s : ℝ) : IsDil X s (aD X s) := rfl

theorem isDil_unique (X : Fin n → ℝ) (s : ℝ) (a a' : GR n) (h : IsDil X s a) (h' : IsDil X s a') : a = a' := by
  apply Subtype.ext
  apply Units.ext
  exact h.trans h'.symm

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem form_inv (g : M2 n) (hg : InG g) (V : Fin n ⊕ Fin n → ℂ) :
    star (g *ᵥ V) ⬝ᵥ (JJ n *ᵥ (g *ᵥ V)) = star V ⬝ᵥ (JJ n *ᵥ V) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold InG at hg
  rw [hg]

theorem JJ_mulVec (y z : Fin n → ℂ) : JJ n *ᵥ Sum.elim y z = Sum.elim z (-y) := by
  funext i
  rcases i with i | i <;> simp [JJ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq]

theorem dot_elim (a b c d : Fin n → ℂ) : Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem star_elim (a b : Fin n → ℂ) : star (Sum.elim a b) = Sum.elim (star a) (star b) := by
  funext i
  rcases i with i | i <;> rfl

theorem mulVec_elim (g : M2 n) (y z : Fin n → ℂ) :
    g *ᵥ Sum.elim y z = Sum.elim (g.toBlocks₁₁ *ᵥ y + g.toBlocks₁₂ *ᵥ z) (g.toBlocks₂₁ *ᵥ y + g.toBlocks₂₂ *ᵥ z) := by
  funext i
  rcases i with i | i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
    toBlocks₂₂]

theorem u_det_ne (g : M2 n) (hg : InG g) (w : ℂ) (hw : w = Complex.I ∨ w = -Complex.I) :
    (w • g.toBlocks₂₁ + g.toBlocks₂₂).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have key := form_inv g hg (Sum.elim (w • x) x)
  rw [mulVec_elim] at key
  have hl : g.toBlocks₂₁ *ᵥ (w • x) + g.toBlocks₂₂ *ᵥ x = 0 := by
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.add_mulVec]
    exact hx
  rw [hl, JJ_mulVec, JJ_mulVec, star_elim, star_elim, dot_elim, dot_elim] at key
  have hs : star (w • x) = star w • star x := by
    funext j; simp [mul_comm]
  rw [hs] at key
  simp only [dotProduct_zero, zero_add, Pi.star_apply, star_zero, zero_dotProduct, dotProduct_neg, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at key
  have hxx : star x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_star_self_eq_zero.mp h)
  rcases hw with rfl | rfl
  · apply hxx
    have h2 : star Complex.I = -Complex.I := by simp [Complex.star_def]
    rw [h2] at key
    have : (-(2 * Complex.I)) * (star x ⬝ᵥ x) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h
  · apply hxx
    have h2 : star (-Complex.I) = Complex.I := by simp [Complex.star_def]
    rw [h2] at key
    have : (2 * Complex.I) * (star x ⬝ᵥ x) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h

theorem automorphy_first_det_ne_zero (h : GR n) : (u1 (mR h)).det ≠ 0 := u_det_ne _ h.2 _ (Or.inl rfl)

theorem automorphy_second_det_ne_zero (h : GR n) : (u2 (mR h)).det ≠ 0 := by
  have : u2 (mR h) = (-Complex.I) • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂ := by
    simp [u2, neg_smul]
  rw [this]
  exact u_det_ne _ h.2 _ (Or.inr rfl)

theorem det_mR_ne (h : GR n) : (mR h).det ≠ 0 := by
  have := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h.1)
  exact this.ne_zero

theorem continuous_mR : Continuous (mR (n := n)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_group_lower_left_block : Continuous fun h : GR n => (mR h).toBlocks₂₁ :=
  continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))

theorem continuous_group_lower_right_block : Continuous fun h : GR n => (mR h).toBlocks₂₂ :=
  continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))

theorem spherical_section_continuous_ne_zero (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) ∧ ∀ k : GR n, F0 p q e k ≠ 0 := by
  have c1 : Continuous fun h : GR n => (mR h).det := continuous_mR.matrix_det
  have c2 : Continuous fun h : GR n => (u1 (mR h)).det := by
    have : Continuous fun h : GR n => Complex.I • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂ :=
      (continuous_group_lower_left_block.const_smul Complex.I).add continuous_group_lower_right_block
    unfold u1
    exact this.matrix_det
  have c3 : Continuous fun h : GR n => (u2 (mR h)).det := by
    have : Continuous fun h : GR n => -(Complex.I • (mR h).toBlocks₂₁) + (mR h).toBlocks₂₂ :=
      (continuous_group_lower_left_block.const_smul Complex.I).neg.add continuous_group_lower_right_block
    unfold u2
    exact this.matrix_det
  refine ⟨?_, fun k => ?_⟩
  · unfold F0 f0
    exact (c1.zpow₀ e fun h => Or.inl (det_mR_ne h)).mul
      ((c2.zpow₀ _ fun h => Or.inl (automorphy_first_det_ne_zero h)).mul (c3.zpow₀ _ fun h => Or.inl (automorphy_second_det_ne_zero h)))
  · unfold F0 f0
    exact mul_ne_zero (zpow_ne_zero _ (det_mR_ne k))
      (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero k)) (zpow_ne_zero _ (automorphy_second_det_ne_zero k)))

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem mR_dil (X : Fin n → ℝ) (s : ℝ) (a : GR n) (h : IsDil X s a) : mR a = Ac X s := by
  rw [h]
  unfold Ac
  congr 2 <;> funext j <;> push_cast [Complex.ofReal_exp] <;> (try ring_nf)

theorem det_Ac (X : Fin n → ℝ) (z : ℂ) : (Ac X z).det = 1 := by
  unfold Ac
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add]
  try simp

theorem holomorphic_section_extension_eq (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (a : ℝ → GR n) (ha : ∀ s, IsDil X s (a s)) (h : GR n) (s : ℝ) :
    holomorphicSectionExtension p q e X h s = F0 p q e (h * a s) := by
  unfold holomorphicSectionExtension F0 f0
  rw [mR_mul, mR_dil X s (a s) (ha s), det_mul, det_Ac, mul_one, mul_assoc]

theorem continuous_Ac (X : Fin n → ℝ) : Continuous (Ac X) := by
  unfold Ac
  refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const ?_
  · exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)
  · exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)

theorem differentiable_Ac_entry (X : Fin n → ℝ) (a b : Fin n ⊕ Fin n) : Differentiable ℂ fun z => Ac X z a b := by
  rcases a with a | a <;> rcases b with b | b <;> by_cases hab : a = b <;>
    simp [Ac, diagonal_apply, hab] <;> fun_prop

theorem differentiable_det_entries {m : Type} [Fintype m] [DecidableEq m] (A : ℂ → Matrix m m ℂ)
    (hA : ∀ i j, Differentiable ℂ fun z => A z i j) : Differentiable ℂ fun z => (A z).det := by
  have : (fun z => (A z).det) = fun z => ∑ σ : Equiv.Perm m, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A z (σ i) i := by
    funext z
    rw [det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [this]
  refine Differentiable.fun_sum fun σ _ => ?_
  exact (differentiable_const _).mul (Differentiable.fun_finsetProd fun i _ => hA _ _)

theorem differentiable_u_det (M : M2 n) (X : Fin n → ℝ) (w : ℂ) :
    Differentiable ℂ fun z => (w • (M * Ac X z).toBlocks₂₁ + (M * Ac X z).toBlocks₂₂).det := by
  apply differentiable_det_entries
  intro i j
  have hm : ∀ a b, Differentiable ℂ fun z => (M * Ac X z) a b := by
    intro a b
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (differentiable_Ac_entry X k b)
  simp only [Matrix.add_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, of_apply, smul_eq_mul]
  exact ((differentiable_const _).mul (hm _ _)).add (hm _ _)

theorem continuous_u_det (X : Fin n → ℝ) (w : ℂ) :
    Continuous fun y : GR n × ℂ => (w • (mR y.1 * Ac X y.2).toBlocks₂₁ + (mR y.1 * Ac X y.2).toBlocks₂₂).det := by
  have hM : Continuous fun y : GR n × ℂ => mR y.1 * Ac X y.2 :=
    (continuous_mR.comp continuous_fst).matrix_mul ((continuous_Ac X).comp continuous_snd)
  have h21 : Continuous fun y : GR n × ℂ => (mR y.1 * Ac X y.2).toBlocks₂₁ :=
    hM.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))
  have h22 : Continuous fun y : GR n × ℂ => (mR y.1 * Ac X y.2).toBlocks₂₂ :=
    hM.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))
  exact ((h21.const_smul w).add h22).matrix_det

theorem first_cayley_block_eq (M : M2 n) : u1 M = Complex.I • M.toBlocks₂₁ + M.toBlocks₂₂ := rfl

theorem second_cayley_block_eq (M : M2 n) : u2 M = (-Complex.I) • M.toBlocks₂₁ + M.toBlocks₂₂ := by
  simp [u2, neg_smul]

theorem holomorphic_section_extension_exists (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (S : Set (GR n)) (hS : IsCompact S) :
    ∃ V : Set ℂ, IsOpen V ∧ (∀ s : ℝ, (s : ℂ) ∈ V) ∧
      ContinuousOn (fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) (S ×ˢ V) ∧
      ∀ h ∈ S, DifferentiableOn ℂ (holomorphicSectionExtension p q e X h) V := by
  have c1 : Continuous fun y : GR n × ℂ => (u1 (mR y.1 * Ac X y.2)).det := by
    simpa only [first_cayley_block_eq] using continuous_u_det X Complex.I
  have c2 : Continuous fun y : GR n × ℂ => (u2 (mR y.1 * Ac X y.2)).det := by
    simpa only [second_cayley_block_eq] using continuous_u_det X (-Complex.I)
  set Z := {y : GR n × ℂ | (u1 (mR y.1 * Ac X y.2)).det ≠ 0 ∧ (u2 (mR y.1 * Ac X y.2)).det ≠ 0}
  have hZ : IsOpen Z := (isOpen_ne_fun c1 continuous_const).inter (isOpen_ne_fun c2 continuous_const)
  have hreal : ∀ (h : GR n) (s : ℝ), ((h, (s : ℂ)) : GR n × ℂ) ∈ Z := by
    intro h s
    have hm : mR h * Ac X s = mR (h * aD X s) := by rw [mR_mul, mR_dil X s _ (isDil_aD X s)]
    refine ⟨?_, ?_⟩
    · show (u1 (mR h * Ac X s)).det ≠ 0
      rw [hm]
      exact automorphy_first_det_ne_zero _
    · show (u2 (mR h * Ac X s)).det ≠ 0
      rw [hm]
      exact automorphy_second_det_ne_zero _
  have tube : ∀ s : ℝ, ∃ v : Set ℂ, IsOpen v ∧ (s : ℂ) ∈ v ∧ S ×ˢ v ⊆ Z := by
    intro s
    obtain ⟨u, v, -, hv, hSu, hsv, huv⟩ := generalized_tube_lemma hS (isCompact_singleton (x := (s : ℂ))) hZ
      (by
        rintro ⟨h, z⟩ ⟨-, hz⟩
        simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hreal h s)
    exact ⟨v, hv, hsv rfl, (Set.prod_mono hSu le_rfl).trans huv⟩
  choose v hv hsv hSv using tube
  refine ⟨⋃ s, v s, isOpen_iUnion hv, fun s => Set.mem_iUnion.mpr ⟨s, hsv s⟩, ?_, ?_⟩
  · have hsub : S ×ˢ (⋃ s, v s) ⊆ Z := by
      rintro ⟨h, z⟩ ⟨hh, hz⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
      exact hSv s (Set.mk_mem_prod hh hs)
    intro y hy
    refine ContinuousAt.continuousWithinAt ?_
    have hyZ := hsub hy
    unfold holomorphicSectionExtension
    have e1 : ContinuousAt (fun y : GR n × ℂ => (mR y.1).det ^ e) y :=
      ((continuous_mR.comp continuous_fst).matrix_det.continuousAt).zpow₀ _ (Or.inl (det_mR_ne _))
    have e2 : ContinuousAt (fun y : GR n × ℂ => (u1 (mR y.1 * Ac X y.2)).det ^ (-(p : ℤ))) y :=
      c1.continuousAt.zpow₀ _ (Or.inl hyZ.1)
    have e3 : ContinuousAt (fun y : GR n × ℂ => (u2 (mR y.1 * Ac X y.2)).det ^ (-(q : ℤ))) y :=
      c2.continuousAt.zpow₀ _ (Or.inl hyZ.2)
    exact (e1.mul e2).mul e3
  · intro h hh z hz
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
    have hyZ := hSv s (Set.mk_mem_prod hh hs)
    have d1 : Differentiable ℂ fun z => (u1 (mR h * Ac X z)).det := by
      simpa only [first_cayley_block_eq] using differentiable_u_det (mR h) X Complex.I
    have d2 : Differentiable ℂ fun z => (u2 (mR h * Ac X z)).det := by
      simpa only [second_cayley_block_eq] using differentiable_u_det (mR h) X (-Complex.I)
    unfold holomorphicSectionExtension
    have g1 : DifferentiableAt ℂ (fun z => (u1 (mR h * Ac X z)).det ^ (-(p : ℤ))) z := (d1 z).zpow (Or.inl hyZ.1)
    have g2 : DifferentiableAt ℂ (fun z => (u2 (mR h * Ac X z)).det ^ (-(q : ℤ))) z := (d2 z).zpow (Or.inl hyZ.2)
    exact (((differentiableAt_const _).mul g1).mul g2).differentiableWithinAt

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem helpA : HelpA :=
  ⟨fun _ X => ⟨aD X, isDil_aD X⟩, fun _ X s a a' h h' => isDil_unique X s a a' h h', fun _ => isCompact_KR,
    fun _ h => ⟨automorphy_first_det_ne_zero h, automorphy_second_det_ne_zero h⟩, fun _ p q e X a ha h s => holomorphic_section_extension_eq p q e X a ha h s,
    fun _ p q e X S hS => holomorphic_section_extension_exists p q e X S hS,
    fun _ p q e => ⟨(spherical_section_continuous_ne_zero p q e).1, fun k _ => (spherical_section_continuous_ne_zero p q e).2 k⟩⟩

end PositivityTheory.Rg.Sw.AbsSt
end

section
noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

theorem anNhd_iter {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv r f) V := by
  rw [iteratedDeriv_eq_iterate]
  exact (hf.analyticOnNhd hV).iterated_deriv r

theorem real_iter (f : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (hR : ∀ s : ℝ, (s : ℂ) ∈ V)
    (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => f t) = fun s : ℝ => iteratedDeriv r f s := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [iteratedDeriv_succ]
    have hd : DifferentiableAt ℂ (iteratedDeriv n f) (s : ℂ) :=
      ((anNhd_iter hV hf n) s (hR s)).differentiableAt
    exact hd.hasDerivAt.comp_ofReal.deriv

theorem helpC : HelpC := by
  refine ⟨fun f V hV hR hf r s => congrFun (real_iter f V hV hR hf r) s, ?_⟩
  intro f V hV hR hf h0 s
  have hA := hf.analyticOnNhd hV
  have h0V : (0 : ℂ) ∈ V := by simpa using hR 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball)]
    simp [h0]
  have hpre : IsPreconnected (Set.range ((↑) : ℝ → ℂ)) :=
    (isConnected_range Complex.continuous_ofReal).isPreconnected
  have hsub := hpre.subset_connectedComponentIn (x := (0 : ℂ)) ⟨0, by simp⟩
    (by rintro _ ⟨t, rfl⟩; exact hR t)
  have hEq := (hA.mono (connectedComponentIn_subset V 0)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn (mem_connectedComponentIn h0V) hloc
  simpa using hEq (hsub ⟨s, rfl⟩)

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem integrable_of_cpt {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [IsFiniteMeasure μ] (hK : IsCompact (univ : Set K)) {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun _ _ => measure_lt_top μ _⟩
  exact hf.integrable_of_hasCompactSupport (hK.of_isClosed_subset (isClosed_tsupport f) (subset_univ _))

theorem finInt {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (hK : IsCompact (univ : Set K)) {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (v : K → V) (hv : ∀ k, v k ∈ W) (hc : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun k => l (v k))
    (w : K → ℂ) (hw : Continuous w) : ∃ Φ : V, ∀ l : V →ₗ[ℂ] ℂ, l Φ = ∫ k, w k * l (v k) ∂μ := by
  classical
  let b := Module.finBasis ℂ W
  have hext : ∀ i, ∃ L : V →ₗ[ℂ] ℂ, ∀ x : W, L x = b.repr x i := fun i => by
    obtain ⟨L, hL⟩ := LinearMap.exists_extend (b.coord i)
    exact ⟨L, fun x => by simpa using congrArg (fun f => f x) hL⟩
  choose L hL using hext
  refine ⟨∑ i, (∫ k, w k * L i (v k) ∂μ) • (b i : V), fun l => ?_⟩
  have hv' : ∀ k, l (v k) = ∑ i, L i (v k) * l (b i) := by
    intro k
    have h1 := b.sum_repr ⟨v k, hv k⟩
    have h2 : v k = ∑ i, (b.repr ⟨v k, hv k⟩ i) • (b i : V) := by
      have h3 := congrArg Subtype.val h1
      rw [Submodule.coe_sum] at h3
      simp only [Submodule.coe_smul] at h3
      exact h3.symm
    conv_lhs => rw [h2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, ← hL i ⟨v k, hv k⟩]
  rw [map_sum]
  simp_rw [map_smul, smul_eq_mul]
  have hint : ∀ i, Integrable (fun k => w k * L i (v k) * l (b i)) μ := fun i =>
    integrable_of_cpt μ hK ((hw.mul (hc (L i))).mul continuous_const)
  calc ∑ i, (∫ k, w k * L i (v k) ∂μ) * l (b i) = ∑ i, ∫ k, w k * L i (v k) * l (b i) ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_mul_const]
    _ = ∫ k, ∑ i, w k * L i (v k) * l (b i) ∂μ := (integral_finsetSum _ fun i _ => hint i).symm
    _ = ∫ k, w k * l (v k) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hv' k, Finset.mul_sum, mul_assoc]

set_option maxHeartbeats 4000000 in

theorem thSph_of' (hA : HelpA) (hC : HelpC) (hKAK : KAK) (hMult : Mult) (hD : DerivativeVacuumDilations) (hSph : Sph)
    (hSZ : SecZero) (hHP : HolParam) (hLC : LC) : ThSph := by
  intro m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG _ _ μ _ _ g y
  obtain ⟨hAdil, hAuniq, hAcpt, _hAdet, hAF0c, hAV, hAF0⟩ := hA
  obtain ⟨hCrc, hCzero⟩ := hC
  have hKc : IsCompact (univ : Set (KR n)) := hAcpt n
  have hF0 : Continuous (F0 (n := n) p q e) := (hAF0 n p q e).1
  have hF0ne : ∀ k : KR n, F0 p q e (k : GR n) ≠ 0 := fun k => (hAF0 n p q e).2 k k.2
  have hw : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ := (hF0.comp continuous_subtype_val).inv₀ hF0ne
  have hF01 : F0 (n := n) p q e 1 = 1 := by
    have h := ((hMult n p q e).1 1 1 (KR n).one_mem).1
    rw [mul_one] at h
    have hne : F0 (n := n) p q e 1 ≠ 0 := by simpa using hF0ne 1
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact h.symm)
  have hRI : ∀ (z k2 : GR n), k2 ∈ KR n →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (z * k2))) ∂μ) =
        F0 p q e k2 * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * z)) ∂μ := by
    intro z k2 hk2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have hk2' : InK (mR k2) := hk2
    have h1 : I 1 (g * ι ((k : GR n) * (z * k2))) = F0 p q e k2 * I 1 (g * ι ((k : GR n) * z)) := by
      rw [← mul_assoc, map_mul ι, ← mul_assoc g, hG.Ik 1 _ k2 hk2', hL.kvac k2 hk2', map_smul]
      rfl
    simp only [h1]
    ring
  have hRS : ∀ (z k2 : GR n), k2 ∈ KR n →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (z * k2)) ∂μ) =
        F0 p q e k2 * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * z) ∂μ := by
    intro z k2 hk2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [← mul_assoc, ((hMult n p q e).1 _ k2 hk2).1]
    ring
  have key : ∀ (k1 : GR n), k1 ∈ KR n → ∀ (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) ∂μ) =
        I 1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)) ∂μ := by
    intro k1 hk1 X a ha
    obtain ⟨U, F, hUo, hUR, hFc, hF⟩ := hG.Idil g X a ha
    have hmc : Continuous fun k : KR n => (k : GR n) * k1 := continuous_subtype_val.mul continuous_const
    obtain ⟨V, hVo, hVR, hVc, hVd⟩ := hAV n p q e X _ (hKc.image hmc)
    have hKm : ∀ k : KR n, (k : GR n) * k1 ∈ KR n := fun k => (KR n).mul_mem k.2 hk1
    have hSm : ∀ k : KR n, (k : GR n) * k1 ∈ (fun k : KR n => (k : GR n) * k1) '' univ :=
      fun k => mem_image_of_mem _ (mem_univ _)
    have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0
    have h0V : (0 : ℂ) ∈ V := by simpa using hVR 0
    set Q : PX m n := (dil c X ^ 0) 1 with hQ0
    let Gk : KR n → ℂ → ℂ := fun k z => (F0 p q e (k : GR n))⁻¹ *
      (F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z)
    have hpm : Continuous fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2) :=
      (hmc.comp continuous_fst).prodMk continuous_snd
    have hc1 : ContinuousOn (fun w : KR n × ℂ => F ((w.1 : GR n) * k1) w.2) (univ ×ˢ (U ∩ V)) :=
      ContinuousOn.comp (f := fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2)) (g := fun y : GR n × ℂ => F y.1 y.2)
        hFc hpm.continuousOn (fun w hw' => ⟨mem_univ _, hw'.2.1⟩)
    have hc2 : ContinuousOn (fun w : KR n × ℂ => holomorphicSectionExtension p q e X ((w.1 : GR n) * k1) w.2) (univ ×ˢ (U ∩ V)) :=
      ContinuousOn.comp (f := fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2))
        (g := fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) hVc hpm.continuousOn (fun w hw' => ⟨hSm w.1, hw'.2.2⟩)
    have hGc : ContinuousOn (fun w : KR n × ℂ => Gk w.1 w.2) (univ ×ˢ (U ∩ V)) :=
      ((hw.comp continuous_fst).continuousOn).mul (hc1.sub (continuousOn_const.mul hc2))
    have hGd : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (Gk k) (U ∩ V) := by
      intro k _
      refine DifferentiableOn.const_mul (DifferentiableOn.sub ?_ (DifferentiableOn.const_mul ?_ _)) _
      · exact ((hF _).1).mono inter_subset_left
      · exact (hVd _ (hSm k)).mono inter_subset_right
    obtain ⟨hφd, hφD⟩ := hHP (KR n) μ univ hKc (by simp) (U ∩ V) Gk (hUo.inter hVo) hGc hGd
    have hder : ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, Gk k z ∂μ) 0 = 0 := by
      intro r
      rw [hφD 0 ⟨h0U, h0V⟩ r]
      set Qr : PX m n := (dil c X ^ r) 1 with hQr
      obtain ⟨W, hWf, hQW, hWst, hWc⟩ := hL.kfin Qr
      haveI := hWf
      have hvW : ∀ k : KR n, ρ ((k : GR n) * k1) Qr ∈ W := fun k => hWst _ (hKm k) Qr hQW
      have hvc : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous fun k : KR n => l (ρ ((k : GR n) * k1) Qr) := fun l =>
        (hWc Qr hQW l).comp_continuous hmc (fun k => hKm k)
      obtain ⟨Φ, hΦ⟩ := finInt μ hKc W (fun k : KR n => ρ ((k : GR n) * k1) Qr) hvW hvc _ hw

      have hval : ∀ k : KR n, iteratedDeriv r (Gk k) 0 = (F0 p q e (k : GR n))⁻¹ *
          (I (ρ ((k : GR n) * k1) Qr) g - I 1 g * sL (ρ ((k : GR n) * k1) Qr) 1) := by
        intro k
        have hcF : ContDiffAt ℂ r (F ((k : GR n) * k1)) 0 :=
          ((hF _).1.contDiffOn hUo).contDiffAt (hUo.mem_nhds h0U)
        have hcG : ContDiffAt ℂ r (fun z => I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) 0 :=
          contDiffAt_const.mul (((hVd _ (hSm k)).contDiffOn hVo).contDiffAt (hVo.mem_nhds h0V))
        have e1 : iteratedDeriv r (Gk k) 0 = (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (fun z => F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) 0 := by
          simp only [Gk]
          rw [iteratedDeriv_const_mul_field]
        have e0 : (fun z => F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) =
            F ((k : GR n) * k1) - fun z => I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z := rfl
        rw [e1, e0, iteratedDeriv_sub hcF hcG]
        simp only [iteratedDeriv_const_mul_field]
        rw [(hF _).2.2 r, hG.Ik Qr g _ (hKm k)]
        have e2 : iteratedDeriv r (holomorphicSectionExtension p q e X ((k : GR n) * k1)) 0 = sL (ρ ((k : GR n) * k1) Qr) 1 := by
          have h3 := hCrc (holomorphicSectionExtension p q e X ((k : GR n) * k1)) V hVo hVR (hVd _ (hSm k)) r 0
          simp only [Complex.ofReal_zero] at h3
          rw [← h3]
          have h4 : (fun t : ℝ => holomorphicSectionExtension p q e X ((k : GR n) * k1) t) = fun s => F0 p q e ((k : GR n) * k1 * a s) :=
            funext fun s => hAF0c n p q e X a ha _ s
          rw [h4, (hD m n ε c t p q e sL ρ hL X a ha _ r).2]
          rw [← hL.kact Qr 1 _ (hKm k), one_mul]
        rw [e2]
      let lg : PX m n →ₗ[ℂ] ℂ := (LinearMap.proj g).comp I
      let ly : GR n → PX m n →ₗ[ℂ] ℂ := fun y' => (LinearMap.proj y').comp sL
      have hlg : ∀ P, lg P = I P g := fun P => rfl
      have hly : ∀ y' P, ly y' P = sL P y' := fun y' P => rfl
      have hcv : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * l (ρ ((k : GR n) * k1) Qr) :=
        fun l => hw.mul (hvc l)

      set D : ℂ := iteratedDeriv r (fun s : ℝ => ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
        F0 p q e ((k : GR n) * (k1 * a s)) ∂μ) 0 with hDdef
      have hsL : ∀ y' : GR n, sL Φ y' = F0 p q e y' * D := by
        intro y'
        have hm' : Continuous fun k : KR n => y' * ((k : GR n) * k1) := continuous_const.mul hmc
        obtain ⟨V', hV'o, hV'R, hV'c, hV'd⟩ := hAV n p q e X _ (hKc.image hm')
        have hSm' : ∀ k : KR n, y' * ((k : GR n) * k1) ∈ (fun k : KR n => y' * ((k : GR n) * k1)) '' univ :=
          fun k => mem_image_of_mem _ (mem_univ _)
        have h0V' : (0 : ℂ) ∈ V' := by simpa using hV'R 0
        let Gk' : KR n → ℂ → ℂ := fun k z => (F0 p q e (k : GR n))⁻¹ * holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1)) z
        have hpm' : Continuous fun w : KR n × ℂ => (y' * ((w.1 : GR n) * k1), w.2) :=
          (hm'.comp continuous_fst).prodMk continuous_snd
        have hc3 : ContinuousOn (fun w : KR n × ℂ => holomorphicSectionExtension p q e X (y' * ((w.1 : GR n) * k1)) w.2) (univ ×ˢ V') :=
          ContinuousOn.comp (f := fun w : KR n × ℂ => (y' * ((w.1 : GR n) * k1), w.2))
            (g := fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) hV'c hpm'.continuousOn (fun w hw' => ⟨hSm' w.1, hw'.2⟩)
        have hGc' : ContinuousOn (fun w : KR n × ℂ => Gk' w.1 w.2) (univ ×ˢ V') :=
          ((hw.comp continuous_fst).continuousOn).mul hc3
        have hGd' : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (Gk' k) V' := fun k _ =>
          (hV'd _ (hSm' k)).const_mul _
        obtain ⟨hψd, hψD⟩ := hHP (KR n) μ univ hKc (by simp) V' Gk' hV'o hGc' hGd'
        have step1 : sL Φ y' = ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) 0 ∂μ := by
          rw [← hly, hΦ (ly y')]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [hly]
          rw [← hL.kact Qr y' _ (hKm k), ← (hD m n ε c t p q e sL ρ hL X a ha _ r).2]
          have h3 := hCrc (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) V' hV'o hV'R (hV'd _ (hSm' k)) r 0
          simp only [Complex.ofReal_zero] at h3
          rw [← h3]
          congr 2
          funext s
          exact (hAF0c n p q e X a ha _ s).symm
        have step2 : (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) 0 ∂μ) =
            iteratedDeriv r (fun z => ∫ k, Gk' k z ∂μ) 0 := by
          rw [hψD 0 h0V' r]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [Gk', iteratedDeriv_const_mul_field]
        have step3 : iteratedDeriv r (fun z => ∫ k, Gk' k z ∂μ) 0 =
            iteratedDeriv r (fun t : ℝ => ∫ k, Gk' k t ∂μ) 0 := by
          have h3 := hCrc _ V' hV'o hV'R hψd r 0
          simp only [Complex.ofReal_zero] at h3
          exact h3.symm
        have step4 : (fun t : ℝ => ∫ k, Gk' k t ∂μ) = fun t : ℝ => F0 p q e y' *
            ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a t)) ∂μ := by
          funext t
          rw [← hSph n p q e μ y' (k1 * a t)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [Gk']
          rw [hAF0c n p q e X a ha _ t]
          simp only [mul_assoc]
        rw [step1, step2, step3, step4, iteratedDeriv_const_mul_field]
      have hν : sL Φ 1 = D := by rw [hsL 1, hF01, one_mul]
      have hnull : NullSec ε c (Φ - D • 1) := by
        refine (hSZ m n ε c t p q e sL ρ hL (Φ - D • 1)).mpr fun y' => ?_
        rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsL y', hL.vac y']
        ring
      have hLC' := hLC m n ε c hL.cpos lg (fun a b P => hG.Iinv g a b P) _ hnull
      rw [map_sub, map_smul, smul_eq_mul, hlg, hlg] at hLC'
      have hint1 := integrable_of_cpt μ hKc (hcv lg)
      have hint2 := integrable_of_cpt μ hKc (hcv (ly 1))
      calc (∫ k : KR n, iteratedDeriv r (Gk k) 0 ∂μ)
          = ∫ k : KR n, ((F0 p q e (k : GR n))⁻¹ * lg (ρ ((k : GR n) * k1) Qr) -
              I 1 g * ((F0 p q e (k : GR n))⁻¹ * ly 1 (ρ ((k : GR n) * k1) Qr))) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
            dsimp only
            rw [hval k, hlg, hly]
            ring
        _ = lg Φ - I 1 g * ly 1 Φ := by
            rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul, hΦ lg, hΦ (ly 1)]
        _ = 0 := by
            rw [hlg, hly, hν]
            linear_combination hLC'
    have hz := hCzero (fun z => ∫ k, Gk k z ∂μ) (U ∩ V) (hUo.inter hVo) (fun s => ⟨hUR s, hVR s⟩) hφd hder 1
    have hcI : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) :=
      hw.mul (hG.Icont.comp (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const))))
    have hcS : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)) :=
      hw.mul (hF0.comp (continuous_subtype_val.mul continuous_const))
    have hz' : (∫ k : KR n, ((F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) -
        I 1 g * ((F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)))) ∂μ) = 0 := by
      rw [← hz]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [Gk]
      rw [(hF _).2.1 1, hAF0c n p q e X a ha _ 1]
      simp only [mul_assoc]
      ring
    rw [integral_sub (integrable_of_cpt μ hKc hcI) ((integrable_of_cpt μ hKc hcS).const_mul _),
      integral_const_mul] at hz'
    exact sub_eq_zero.mp hz'
  obtain ⟨k1, k2, a1, X, hk1, hk2, hda1, rfl⟩ := hKAK n y
  obtain ⟨a, ha⟩ := hAdil n X
  have ha1 : a1 = a 1 := hAuniq n X 1 a1 (a 1) hda1 (ha 1)
  subst ha1
  rw [hRI _ k2 hk2, hRS _ k2 hk2, key k1 hk1 X a ha]
  ring

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
namespace PositivityTheory.Rg.Sw.AbsSt

theorem thSph_of : KAK → Mult → DerivativeVacuumDilations → Sph → SecZero → HolParam → LC → NullIff → ThSph :=
  fun hKAK hMult hD hSph hSZ hHP hLC _ => thSph_of' helpA helpC hKAK hMult hD hSph hSZ hHP hLC

end PositivityTheory.Rg.Sw.AbsSt
end

section
namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem absThm_of (hLV : LV) (hC : Cyc) (hLC : LC) (hN : NullIff) : AbsThm := by
  have hZ := secZero hN
  have hS := sph iwa mult
  have hT := thSph_of kAK mult derivative_vacuum_section hS hZ holParam hLC hN
  have hV := vacOut_of' detU1 (locOp hLV iwa mult holParam) holParam hT
  exact absThm_of' hV iwa detU1 kAK mult hZ derivative_vacuum_section (cycSec_of hC hZ secDer) hS holParam glue hLC hN

theorem genCore_top (hC : Cyc) (hLC : LC) (hN : NullIff) : GenCore := by
  have hZ := secZero hN
  exact genCore iwa detU1 kAK mult hZ derivative_vacuum_section (cycSec_of hC hZ secDer) holParam glue hLC

end PositivityTheory.Rg.Sw.AbsSt
end
