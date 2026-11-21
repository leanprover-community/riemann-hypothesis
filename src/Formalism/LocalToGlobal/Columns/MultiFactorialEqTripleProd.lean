import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound
import Formalism.LocalToGlobal.Columns.FactorialSumLePowMulProd

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section Main

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)


end Main

section Mono

theorem fock_norm_rational_eq {σ : Type} (P : MvPolynomial σ ℚ) : fockN (map (algebraMap ℚ ℂ) P) = ((Formalism.GradedWeylDivisibility.fockQ P P : ℚ) : ℝ) := by
  unfold fockN Formalism.GradedWeylDivisibility.fockQ
  rw [support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, mfact]
  have : ‖(algebraMap ℚ ℂ) (coeff m P)‖ ^ 2 = ((coeff m P : ℚ) : ℝ) * ((coeff m P : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.norm_ratCast, sq_abs]
    ring
  rw [this]
  push_cast
  rfl


variable {ι : Type} [Fintype ι] {n : ℕ}



def monC {κ : ℕ} (lam : ι → DomWeight (κ + 1)) : ℝ :=
  (((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2))⁻¹




end Mono

section Gen

open Formalism.HermitianLattices.TraceIntegrality

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {ι : Type} [Fintype ι]




end Gen

end Formalism.L2.Col
