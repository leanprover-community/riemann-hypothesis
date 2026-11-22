module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def de2 (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then -1 else 1

def IsGap (X : Data E r) (i j : Fin r) : Prop := (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ X.p0

namespace Weights

variable {X : Data E r} (w : Weights X)

end Weights

def lev (X : Data E r) (x0 : Frame X.Ψ r) (u : Frame X.Ψ r → ℝ) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((u (cpt X x0 y) : ℝ) : ℂ)) z ξ).re

def curv (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  lev X x0 (phla X la) z ξ

def curvDe (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  curv X x0 (de2 X) z ξ / 2

def omRh (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re

def IsInv (X : Data E r) (u : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x) ∧ ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, u (lact γ x) = u x

end

end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
