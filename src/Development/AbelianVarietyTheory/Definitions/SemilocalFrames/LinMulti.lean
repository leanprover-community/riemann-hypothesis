module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.PeriodIntegrals.BesselMapUniq

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Ell

open Formalism.MainNotions.S

section Rep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))

def SmV (w : H) : Prop :=
  ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ Lie) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w

def dR (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : H := deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) 0

end Rep

def lieOf {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) := {X | Xᴴ * G + G * X = 0}

attribute [instance] Mod.nH Mod.iH Mod.nV Mod.iV

namespace Mod

variable {n k r : ℕ} (M : Mod n k r)

end Mod

end GlobalTheory.Ell
