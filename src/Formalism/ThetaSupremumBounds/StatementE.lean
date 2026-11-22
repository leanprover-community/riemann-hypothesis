module

public import Mathlib
public import Formalism.ThetaSupremumBounds.StatementA
public import Formalism.LogFactorialIndices.StatementSize

@[expose] public section

open Finset MeasureTheory
open scoped ComplexConjugate Real

noncomputable section

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

def liftOp {Cl Cl' A B : Type} [Fintype Cl] [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (γ : Cl → ℝ) (ε : Cl → Cl' → ℂ)
    (T : Cl → Cl' → A →L[ℂ] B) (fn : Cl → A) (L' : Cl') : B :=
  ∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)

def liftNormSq {Cl Cl' A B : Type} [Fintype Cl] [Fintype Cl'] [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (γ : Cl → ℝ) (γ' : Cl' → ℝ) (ε : Cl → Cl' → ℂ)
    (T : Cl → Cl' → A →L[ℂ] B) : ℝ :=
  sInf {X : ℝ | 0 ≤ X ∧ ∀ fn : Cl → A,
    (∑ L', γ' L' * ‖liftOp γ ε T fn L'‖ ^ 2) ≤ X * ∑ L, γ L * ‖fn L‖ ^ 2}

end Formalism.DimensionVariation
