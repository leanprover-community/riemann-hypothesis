module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix ComplexConjugate

variable {ι : Type} [Fintype ι] {r N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2)

def rho (w : ι → Fin r → ℂ) : Fin N → ℝ := fun k =>
  if (eqv k).2.2 = 0 then (w (eqv k).1 (eqv k).2.1).re else (w (eqv k).1 (eqv k).2.1).im

end Formalism.L2.Pj.FundamentalDomainD5
