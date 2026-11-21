import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open CompactHaarProbability

variable {n : ℕ}

section Schur

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}


theorem fct_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : S7.KG ε → E}
    (hf : Continuous f) : Integrable f (S7.muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)






end Schur

section Theta

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem fct_toMK_mem (k : S7.KG ε) : S7.toMK k ∈ UJset ε := k.1.2

theorem fct_cont_toMK : Continuous fun k : S7.KG ε => S7.toMK k :=
  (S7.continuous_toM ε).comp continuous_subtype_val

theorem fct_cont_R (r : L2 ε) : Continuous fun k : S7.KG ε => rreg ε (S7.toMK k) r :=
  ((rreg_isURepOn ε).2.2 r).comp_continuous fct_cont_toMK fct_toMK_mem


def fctTheta (T : S7.KType ε (lowK ε lam)) (r : L2 ε) (e p : T.V) : L2 ε :=
  ∫ k, ⟪T.op k e, p⟫_ℂ • rreg ε (S7.toMK k) r ∂(S7.muK ε)

theorem fct_cont_integrand (r : L2 ε) (e p : T.V) :
    Continuous fun k : S7.KG ε => ⟪T.op k e, p⟫_ℂ • rreg ε (S7.toMK k) r :=
  by
    have h1 : Continuous fun k : S7.KG ε => ⟪T.op k e, p⟫_ℂ :=
      ((cont_op T).clm_apply continuous_const).inner continuous_const
    exact h1.smul (fct_cont_R r)

theorem fct_theta_add (r : L2 ε) (e p q : T.V) :
    fctTheta T r e (p + q) = fctTheta T r e p + fctTheta T r e q := by
  unfold fctTheta
  rw [← integral_add (fct_integrable (fct_cont_integrand r e p)) (fct_integrable (fct_cont_integrand r e q))]
  congr 1
  funext k
  rw [inner_add_right, add_smul]

theorem fct_theta_smul (r : L2 ε) (e : T.V) (c : ℂ) (p : T.V) :
    fctTheta T r e (c • p) = c • fctTheta T r e p := by
  unfold fctTheta
  rw [← integral_smul]
  congr 1
  funext k
  rw [inner_smul_right, mul_smul]

def fctThetaLin (T : S7.KType ε (lowK ε lam)) (r : L2 ε) (e : T.V) : T.V →ₗ[ℂ] L2 ε where
  toFun := fctTheta T r e
  map_add' := fct_theta_add r e
  map_smul' := fct_theta_smul r e







end Theta

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}


end ReciprocityTheory.ChartRestriction.DS
end
end
