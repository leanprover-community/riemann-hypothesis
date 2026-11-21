import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementB

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds






section Pure

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

def spLdeg (lt : ι → σ) (t : σ) (n : ι →₀ ℕ) : ℕ := ∑ k, if lt k = t then n k else 0





variable (lt : ι → σ) (N : σ → ι → R)



variable {lt N} (hN : ∀ s k, N s k ≠ 0 → lt k = s)
include hN






end Pure


section Minor

variable {R : Type*} [CommRing R] {m p : ℕ}

def spV (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) :
    MvPolynomial (Fin m × Fin (p + 1)) R :=
  o.elim (MvPolynomial.C (top c)) (fun k => MvPolynomial.X (k, c))

def spEx (o : Option (Fin m)) (c : Fin (p + 1)) : Fin m × Fin (p + 1) →₀ ℕ :=
  o.elim 0 (fun k => Finsupp.single (k, c) 1)

def spCo (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) : R :=
  o.elim (top c) (fun _ => 1)




end Minor


end Formalism.DworkPowerSeriesWeights
