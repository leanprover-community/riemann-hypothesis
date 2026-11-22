module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelDer
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Sig

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

lemma fh_op_mul (τ : KG ε →* unitary (V →L[ℂ] V)) (k k' : KG ε) :
    ((τ (k * k') : unitary (V →L[ℂ] V)) : V →L[ℂ] V) =
      ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V).comp ((τ k' : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
  rw [map_mul]
  rfl

end Sig

section InK

variable {n : ℕ} {ε : Fin n → Bool}

end InK

section Coef

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k : ℕ}

def fhEnt (k : ℕ) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] (Fin k × Fin k → ℂ) where
  toFun A ij := A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma fh_diff_eval (P : MvPolynomial (Fin k × Fin k) ℂ) (A : Matrix (Fin k) (Fin k) ℂ) :
    DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => MvPolynomial.eval (fhEnt k A) P) A := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact differentiableAt_const _
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (differentiableAt_pi.1
      (LinearMap.toContinuousLinearMap (fhEnt k)).differentiableAt i)

lemma fh_det_eq (A : Matrix (Fin k) (Fin k) ℂ) :
    A.det = MvPolynomial.eval (fhEnt k A) (Matrix.det (Matrix.mvPolynomialX (Fin k) (Fin k) ℂ)) := by
  have h : (fhEnt k A : Fin k × Fin k → ℂ) = fun p => A p.1 p.2 := rfl
  rw [h, RingHom.map_det, Matrix.mvPolynomialX_mapMatrix_eval]

end Coef

section Coef2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V]

lemma fh_det_ne_zero {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Kset (fun _ : Fin k => true)) : g.det ≠ 0 := by
  intro h0
  have hu := Matrix.mem_unitaryGroup_iff.1 hg.1
  have h := congrArg Matrix.det hu
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

end Coef2

end ReciprocityTheory.ChartRestriction.DS.HW
