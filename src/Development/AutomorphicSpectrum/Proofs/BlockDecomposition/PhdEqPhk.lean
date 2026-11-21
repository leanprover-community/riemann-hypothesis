import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.BigCell

variable {F : Type} [Field F]

open Classical in

theorem hr_val (r : Fin 2 → F) (hv : r 1 ≠ 0) :
    (hr r).val = !![(r 1)⁻¹, 0; r 0, r 1] := by
  have hd : (!![(r 1)⁻¹, 0; r 0, r 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    simp [Matrix.det_fin_two, hv]
  unfold hr
  rw [dif_pos hd]
  rfl

theorem cell_val (y : Fˣ) (t : F) (r : Fin 2 → F) (hv : r 1 ≠ 0) :
    (dg2 y 1 * w0 * uni2 t * hr r : GL (Fin 2) F).val =
      !![(y : F) * r 0, (y : F) * r 1; -(r 1)⁻¹ - t * r 0, -(t * r 1)] := by
  have hy : (y : F) ≠ 0 := y.ne_zero
  simp only [Units.val_mul, hr_val r hv]
  simp only [dg2, w0, uni2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring


end GlobalTheory.CompanionTheory.BigCell

namespace GlobalTheory.CompanionTheory.BigCell


end GlobalTheory.CompanionTheory.BigCell
