module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsInv (X : Data E r) (φ : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x

def levi (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((φ (cpt X x0 y) : ℝ) : ℂ)) z ξ).re

def GapsGe (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) : Prop :=
  ∀ (τ : X.Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → g ≤ ((la τ i - la τ j : ℤ) : ℝ)

def PairingGe (X : Data E r) (la : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ (τ : X.Ψ) (i0 i1 : Fin r), (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → m ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ)

def IsTwoDelta (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ (τ : X.Ψ) (i j : Fin r),
    (((i : ℕ) < X.p0 ↔ (j : ℕ) < X.p0) → la τ i = la τ j) ∧
    ((i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → la τ j = la τ i + 2)

def CuspDecay (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ, (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)) ∧
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
      (∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ : X.Ψ, X.tt ξ x τ

def IsExtra (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ IsInv X ps ∧ ContDiffOn ℝ ∞ ps X.dom ∧ (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C) ∧
    CuspDecay X ps a

namespace ThetaIn

variable {X : Data E r} (I : ThetaIn X)

end ThetaIn

end

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
