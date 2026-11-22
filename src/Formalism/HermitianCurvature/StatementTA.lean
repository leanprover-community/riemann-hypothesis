module

public import Mathlib
public import Formalism.HermitianCurvature.StatementK

@[expose] public section

namespace Formalism.FourierDecayAlt.TA

open Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

def PSDOn {α : Type} (P : Finset α) (k : α → α → ℂ) : Prop :=
  (∀ x ∈ P, ∀ y ∈ P, k y x = conj (k x y)) ∧
  ∀ a : α → ℂ, 0 ≤ (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y).re

section forms
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end forms

def LatSum {E : Type} [AddCommGroup E] (L : AddSubgroup E) (c : E → ℝ) (ep : ℝ) : Prop :=
  (∀ x, 0 ≤ c x) ∧ ∀ S : Finset E, (∀ x ∈ S, x ∈ L ∧ x ≠ 0) → ∑ x ∈ S, c x ≤ ep

section axioms
variable {E : Type} [Field E] [DecidableEq E]

end axioms

section estimates
variable {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {W : Type} [Fintype W]

end estimates

section levels
variable {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {W : Type} [Fintype W]

end levels

end Formalism.FourierDecayAlt.TA
