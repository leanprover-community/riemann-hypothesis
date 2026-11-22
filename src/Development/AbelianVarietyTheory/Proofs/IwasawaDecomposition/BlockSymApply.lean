module

public import Mathlib

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DomainDens

def blockSym {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q,
    X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b))

end GlobalTheory.DomainDens
