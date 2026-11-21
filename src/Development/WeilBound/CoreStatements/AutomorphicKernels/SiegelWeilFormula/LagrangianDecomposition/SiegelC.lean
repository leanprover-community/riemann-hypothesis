import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelSmall
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.BlockIndexInrLast

section
noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem block_index_inl_embedded {N n : ℕ} (h : n + 1 = N) (a : Fin n) : eB h (Sum.inl (em0 h a)) = Sum.inl (Sum.inl a) :=
  PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inl a)

theorem block_index_inr_embedded {N n : ℕ} (h : n + 1 = N) (a : Fin n) : eB h (Sum.inr (em0 h a)) = Sum.inl (Sum.inr a) :=
  PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inr a)

theorem blk_fromRows {R : Type*} [CommRing R] {N n : ℕ} (h : n + 1 = N) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (A : Matrix (Fin n) (Fin n) R)
    (hP : P * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) =
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) * A) :
    blk h P 1 * Matrix.fromRows (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin N) R) =
      Matrix.fromRows (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin N) R) *
        (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R).submatrix (eI h) (eI h) := by
  have hA : ∀ i j, P (Sum.inl i) (Sum.inl j) = A i j := by
    intro i j
    have := congrFun (congrFun hP (Sum.inl i)) j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have hB : ∀ i j, P (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have := congrFun (congrFun hP (Sum.inr i)) j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have key : ∀ c : Fin N, c = PositivityTheory.SiegelWeilFormula.Ald.i0 h ∨ ∃ j, c = PositivityTheory.SiegelWeilFormula.Ald.em0 h j := by
    intro c
    by_cases hc : c = PositivityTheory.SiegelWeilFormula.Ald.i0 h
    · exact Or.inl hc
    · obtain ⟨j, rfl⟩ := (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h c).1 hc
      exact Or.inr ⟨j, rfl⟩
  ext u c
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases u with a | a <;> rcases key a with rfl | ⟨i, rfl⟩ <;> rcases key c with rfl | ⟨j, rfl⟩ <;>
    simp [Matrix.one_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_embedded,
      PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_embedded, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last,
      PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv, PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv, hA, hB]

theorem det_blkA {R : Type*} [CommRing R] {N n : ℕ} (h : n + 1 = N) (A : Matrix (Fin n) (Fin n) R) :
    ((Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R).submatrix (eI h) (eI h)).det = A.det := by
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {ι κ ν : Type} [Fintype κ] (M : Matrix ι κ E) (N : Matrix κ ν E) :
    incM F (M * N) = incM F M * incM F N := by
  simp only [incM]
  exact Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F)))

theorem incM_diagCols (n : ℕ) :
    incM F (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) := by
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem mul_fromRows_one_zero {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    M * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) = M.toCols₁ := by
  ext u k
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

theorem frame_fromRows {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ tb : GL (Fin n) E, incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F tb.1 := by
  obtain ⟨-, tb, htb0⟩ := hb
  have htb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * tb.1 := htb0
  refine ⟨tb, ?_⟩
  have e : (incM F b.1).toCols₁ = incM F b.1.toCols₁ := rfl
  rw [mul_fromRows_one_zero, e, htb, incM_mul]
  congr 1
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem frame_decomp {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    w = (frQ b w).toCols₁ * (incM F b.1.toCols₁)ᵀ + (frQ b w).toCols₂ * (incM F b.1.toCols₂)ᵀ := by
  have e1 : frQ b w * (incM F b.1)ᵀ = w := by
    rw [frQ, Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  have e2 : incM F b.1 = Matrix.fromCols (incM F b.1.toCols₁) (incM F b.1.toCols₂) := by
    ext u v
    rcases v with v | v <;> rfl
  conv_lhs => rw [← e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (frQ b w), Matrix.fromCols_mul_fromRows]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cancel_l {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix ι κ (AE F E)) :
    incM F (b⁻¹).1 * (incM F b.1 * X) = X := by
  rw [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]

theorem cancel_l' {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix ι κ (AE F E)) :
    incM F b.1 * (incM F (b⁻¹).1 * X) = X := by
  rw [← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]


theorem cancel_r' {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix κ ι (AE F E)) :
    X * incM F b.1 * incM F (b⁻¹).1 = X := by
  rw [Matrix.mul_assoc, incM_mul_inv, Matrix.mul_one]

theorem mat_of_inFrame {n : ℕ} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    g.1.1 = incM F b.1 * inFrame b g * incM F (b⁻¹).1 := by
  rw [inFrame_eq]
  simp only [Matrix.mul_assoc, cancel_l', incM_mul_inv, Matrix.mul_one]

theorem diag_of_frame {n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (tb : GL (Fin n) E)
    (h : incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F tb.1) :
    (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (tb⁻¹).1 := by
  rw [h, cancel_r']

theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (t : GL ι E) (X : Matrix ι ι (AE F E)) :
    (incM F t.1 * X * incM F (t⁻¹).1).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, incM_inv_mul, Matrix.det_one, one_mul]

theorem det_conj' {ι : Type} [Fintype ι] [DecidableEq ι] (t : GL ι E) (X : Matrix ι ι (AE F E)) :
    (incM F (t⁻¹).1 * X * incM F t.1).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, incM_mul_inv, Matrix.det_one, one_mul]

theorem jPar (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    {j : G2 σ Y →* d.G} (hj : IsJ d h b j) (p : G2 σ Y) (t : GL (Fin n) (AE F E))
    (hpt : p.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * t.1) :
    ∃ t' : GL (Fin d.n) (AE F E), (j p).1.1 * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * t'.1 ∧
      Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det t := by
  obtain ⟨tb, hTb⟩ := frame_fromRows hb
  obtain ⟨td, hTd⟩ := frame_fromRows d.ok.frame
  set P := inFrame b p with hPdef
  set R0 := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR0
  set R0N := Matrix.fromRows (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) with hR0N
  set A : Matrix (Fin n) (Fin n) (AE F E) := incM F (tb⁻¹).1 * t.1 * incM F tb.1 with hA
  have hDn := diag_of_frame b tb hTb
  have hDN := diag_of_frame d.b td hTd
  have hp := mat_of_inFrame b p
  have hP : P * R0 = R0 * A := by
    have e := hpt
    rw [hp, hDn] at e
    have e2 : incM F b.1 * (P * R0) * incM F (tb⁻¹).1 = incM F b.1 * (R0 * A) * incM F (tb⁻¹).1 := by
      rw [hA]
      calc incM F b.1 * (P * R0) * incM F (tb⁻¹).1
          = incM F b.1 * P * incM F (b⁻¹).1 * (incM F b.1 * R0 * incM F (tb⁻¹).1) := by
            simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
        _ = incM F b.1 * R0 * incM F (tb⁻¹).1 * t.1 := e
        _ = incM F b.1 * (R0 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1)) * incM F (tb⁻¹).1 := by
            simp only [Matrix.mul_assoc, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one]
    have e3 := congrArg (fun X => incM F (b⁻¹).1 * X * incM F tb.1) e2
    simpa only [Matrix.mul_assoc, cancel_l, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one] using e3
  have hblk := blk_fromRows h P A hP
  have hjp : inFrame d.b (j p) = blk h P 1 := eq_blk h _ _ (hj.2.1 p) (hj.2.2 p)
  have hjm := mat_of_inFrame d.b (j p)
  rw [hjp] at hjm
  set blkA := (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (AE F E)).submatrix (eI h) (eI h)
    with hblkA
  set T : Matrix (Fin d.n) (Fin d.n) (AE F E) := incM F td.1 * blkA * incM F (td⁻¹).1 with hT
  have hdet : T.det = t.1.det := by
    rw [hT, det_conj, hblkA, det_blkA, hA, det_conj']
  have hu : IsUnit T.det := by
    rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  refine ⟨Matrix.nonsingInvUnit T hu, ?_, ?_⟩
  · show (j p).1.1 * _ = _ * T
    rw [hjm, hDN]
    calc incM F d.b.1 * blk h P 1 * incM F (d.b⁻¹).1 * (incM F d.b.1 * R0N * incM F (td⁻¹).1)
        = incM F d.b.1 * (blk h P 1 * R0N) * incM F (td⁻¹).1 := by simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
      _ = incM F d.b.1 * (R0N * blkA) * incM F (td⁻¹).1 := by rw [hblk]
      _ = incM F d.b.1 * R0N * incM F (td⁻¹).1 * T := by
          rw [hT]; simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet

end PositivityTheory.SiegelWeilFormula.Ald

end
end
