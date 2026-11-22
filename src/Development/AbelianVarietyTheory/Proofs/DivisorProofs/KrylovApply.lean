module

public import Mathlib

@[expose] public section

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

def krylov {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => Matrix.mulVec (y ^ (j : ℕ)) e i

end GlobalTheory.LeviDesc.Krylov
