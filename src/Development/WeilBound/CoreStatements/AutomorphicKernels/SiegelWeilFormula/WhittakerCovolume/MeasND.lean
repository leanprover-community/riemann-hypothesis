module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem meas_det_of_hasSig {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin m := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin m) (Fin m) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hd : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [hA', Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg,
      Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  intro h0
  apply hd
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]

end PositivityTheory.SiegelWeilFormula.KWhit

end
