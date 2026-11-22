module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM

namespace GlobalTheory.ShFam.Pad

structure FinLB (X : Scheme.{0}) : Type where
  n : ℕ
  U : Fin n → X.Opens
  g : ∀ i k, Γ(X, U i ⊓ U k)ˣ
  isLB : LB.IsLB ⟨Fin n, U, g⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {D : D7}

end GlobalTheory.ShFam.Pad
