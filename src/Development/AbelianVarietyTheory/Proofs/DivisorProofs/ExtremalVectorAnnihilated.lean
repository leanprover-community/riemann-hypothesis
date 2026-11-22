module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKTypeKilledCompactRootsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeKilledByNegativeNoncompactRootsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.ExtKill

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [exp_smul_conj hP]

theorem smoothVec_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

end GlobalTheory.HolRead.ExtKill
