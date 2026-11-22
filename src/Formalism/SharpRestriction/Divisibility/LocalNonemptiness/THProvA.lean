module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Lemmata.ProductIdentities.ProdInvZpowMulOfProdZpowEqOne

@[expose] public section

open Matrix MeasureTheory Formalism.BasicNotions.TH

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

section DetExp

open NormedSpace

variable {n : Type} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => (exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, exp_zero, one_mul] at h
  let L : Matrix n n ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_det_of_one (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first | exact Bl.ProductIdentities.goal1 .. | (apply Bl.ProductIdentities.goal1 <;> assumption) | (intros; apply Bl.ProductIdentities.goal1 <;> assumption)

theorem det_exp (X : Matrix n n ℂ) : (exp X).det = Complex.exp X.trace := by
  set φ : ℝ → ℂ := fun t => (exp (t • X)).det with hφ
  have hmul : ∀ s t, φ (s + t) = φ s * φ t := by
    intro s t
    simp only [hφ, add_smul]
    rw [Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t), det_mul]
  have h0 : HasDerivAt φ X.trace 0 :=
    hasDerivAt_det_of_one _ _ (by simp) (hasDerivAt_exp_entry X)
  have hd : ∀ t, HasDerivAt φ (φ t * X.trace) t := by
    intro t
    have h1 : HasDerivAt (fun s => φ (s - t)) X.trace t := by
      have h00 := h0
      rw [← sub_self t] at h00
      exact h00.comp_sub_const t t
    have h2 := h1.const_mul (φ t)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ s = φ t * φ (s - t)
    rw [← hmul]; congr 1; ring
  let ψ : ℝ → ℂ := fun t => φ t * Complex.exp (-((t : ℂ) * X.trace))
  have hψ : ∀ t, HasDerivAt ψ 0 t := by
    intro t
    have e0 : HasDerivAt (fun t : ℝ => -((t : ℂ) * X.trace)) (-(1 * X.trace)) t := by
      have h := ((hasDerivAt_id t).ofReal_comp.mul_const X.trace).fun_neg
      simpa using h
    have e1 := e0.cexp
    have h3 := (hd t).fun_mul e1
    have h4 : φ t * X.trace * Complex.exp (-((t : ℂ) * X.trace)) +
        φ t * (Complex.exp (-((t : ℂ) * X.trace)) * -(1 * X.trace)) = 0 := by ring
    rw [h4] at h3
    exact h3
  have hc := is_const_of_deriv_eq_zero (fun t => (hψ t).differentiableAt) (fun t => (hψ t).deriv) 1 0
  simp only [ψ, hφ, one_smul, zero_smul, exp_zero, det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  exact (eq_of_mul_inv_eq_one hc)

end DetExp

variable (p q : ℕ)

instance : LocallyCompactSpace (Mat p q) :=
  inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))

instance : LocallyCompactSpace (covSub p q) :=
  (covSub_closed p q).isClosedEmbedding_subtypeVal.locallyCompactSpace

variable {p q}

variable (p q)

section Emb

open scoped Kronecker

variable (p q r s : ℕ)

attribute [instance] FockCore.nacg FockCore.ips FockCore.cs

variable {p q r s}

end Emb

section Checks

open MvPolynomial

variable {p q r s : ℕ}

end Checks

section Skew

open MvPolynomial

variable {p q r s : ℕ}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H)

variable {ι}

end Skew

section Compact

variable {p q : ℕ}

end Compact

section Triv

variable {p q : ℕ}

end Triv

end Formalism.MainNotions.DIV.Inh

end
