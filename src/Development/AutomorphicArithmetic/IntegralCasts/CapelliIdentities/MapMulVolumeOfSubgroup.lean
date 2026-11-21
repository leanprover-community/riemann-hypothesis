import Mathlib

open MeasureTheory Set

private noncomputable def mulE {n : ℕ} (a x : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  Matrix.of.symm (Matrix.of a * Matrix.of x)











