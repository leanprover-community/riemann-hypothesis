import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section

namespace GlobalTheory.GoodProjectorTest

open Formalism.BasicNotions Formalism.MainNotions

def noPar (D : D7) : D7 :=
  { D with
    ntypes := { D.ntypes with
      Par := PEmpty
      labPar := fun _ σ => σ.elim
      labPar_monic := fun _ σ => σ.elim
      locPar := fun σ => σ.elim
      locPar_dim := fun σ => σ.elim
      labPar_def := fun _ σ => σ.elim
      MtPar := fun _ _ σ => σ.elim
      AmbPar := fun _ σ => σ.elim }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat
    nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    bc_tie := D.bc_tie
    rbar_tie := D.rbar_tie
    mtpar_tie := fun _ σ => σ.elim }

def withAmb (D : D7) (S : ∀ μ, D.ntypes.Par → Submodule ℂ (D.what₂.Amb μ)) : D7 :=
  { D with
    ntypes := { D.ntypes with AmbPar := S }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat
    nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    bc_tie := D.bc_tie
    rbar_tie := D.rbar_tie
    mtpar_tie := D.mtpar_tie }

def AlgebraPart (D : D7) : Prop :=
  (∀ g : G0g D.nd, D.ntypes.e0.coeff g ∈ D.ntypes.Qchi) ∧
  (∀ g : G0g D.nd, IsIntegral ℤ ((Nat.card (G0g D.nd) : ℂ) * D.ntypes.e0.coeff g)) ∧
  (∀ a : MonoidAlgebra ℂ (G0g D.nd), D.ntypes.e0 * a = a * D.ntypes.e0) ∧
  (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) (MM : AddSubgroup V),
    (∀ a : ℂ, IsIntegral ℤ a → ∀ x ∈ MM, a • x ∈ MM) → (∀ g, ∀ x ∈ MM, ρ g x ∈ MM) →
    let e := ρ.asAlgebraHom D.ntypes.e0
    let c : ℂ := (Nat.card (G0g D.nd) : ℂ)
    (∀ x ∈ MM, c • e x ∈ MM ∧ c • e x ∈ LinearMap.range e) ∧
    (∀ y ∈ MM, y ∈ LinearMap.range e → ∃ x ∈ MM, e x = y) ∧
    (∀ x ∈ MM, ∃ u ∈ MM, ∃ z ∈ MM, u ∈ LinearMap.range e ∧
      z ∈ LinearMap.range (LinearMap.id - e) ∧ c • x = u + z))



def ParOnto (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Sig : List (Part D.naut.CG)),
    N.IsBCV D.nd D.naut i P (N.twistIso D.nd D.naut (Sig ++ [N.muPart D.nd D.naut i]) D.naut.etaTinv) →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (N.isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r) →
    ∃ σ : D.ntypes.Par, ∀ w, N.isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ w

end GlobalTheory.GoodProjectorTest
