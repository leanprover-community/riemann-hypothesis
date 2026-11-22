module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

end Transfer

section Mu

variable (n : ℕ) [NeZero n]

end Mu

def IsStrictlySemistable {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ))) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.Et

end
