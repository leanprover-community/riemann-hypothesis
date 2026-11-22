module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms

open ReciprocityTheory.ChartRestriction.G.Out

def stdForm {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) : ℤ :=
  ∑ i : Fin g, (a (Sum.inl i) * b (Sum.inr i) - a (Sum.inr i) * b (Sum.inl i))

def reduce {g : ℕ} (k : ℕ) (a : Fin g ⊕ Fin g → ℤ) : Fin g ⊕ Fin g → ZMod k :=
  fun j => (a j : ZMod k)

variable {S : Scheme.{0}}

def mulBy (A : Over S) [GrpObj A] (k : ℕ) : A ⟶ A := (𝟙 A) ^ k

namespace Level

variable {P : PolAV S} {k : ℕ} {ζ : Γ(S, ⊤)ˣ}

end Level

end GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms
