module

public import Mathlib

@[expose] public section

namespace KStar.Selmer

open Matrix Module

section Minors

variable {R : Type*} [CommRing R] {m n : Type*}

end Minors

section Complex

variable {R : Type*} [CommRing R] {m n m' n' : Type*}

def coefMap [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    (n → M) →ₗ[R] (m → M) :=
  LinearMap.pi fun i => ∑ j, Φ i j • LinearMap.proj j

theorem coefMap_apply [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M]
    (v : n → M) (i : m) : coefMap Φ M v i = ∑ j, Φ i j • v j := by
  simp [coefMap, LinearMap.sum_apply]

def H1c [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule R (n → M) :=
  LinearMap.ker (coefMap Φ M)

abbrev H2 [Fintype n] (Φ : Matrix m n R) : Type _ :=
  (m → R) ⧸ LinearMap.range Φ.mulVecLin

end Complex

section Special

variable {Λ O : Type*} [CommRing Λ] [CommRing O] {m n : Type*}

abbrev FracMod (O K : Type*) [CommRing O] [Field K] [Algebra O K] : Type _ :=
  K ⧸ (1 : Submodule O K)

end Special

section Koszul

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

end Koszul

section Lagrangian

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

variable {H H' : Type*} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module k H']

end Lagrangian

end KStar.Selmer
