module

public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.LevModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def Moved (X₂ X : Data E r) (δ : GL (Fin r) E) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) : Prop :=
  ∀ (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ),
    mat x' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩


open Classical in
def genScal {S : Type} [CommRing S] (t : Sˣ) : Ix Dw → Sˣ := fun i => if i = none then t else 1

def Over (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) (U : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r)
    (U₂ : Unf d.Xo₂ d.c₂ σ₂ r) (k₂ : U₂.Comp) (k : U.Comp) (δ : GL (Fin r) E) : Prop :=
  ∀ (x : Frame (U₂.X k₂).Ψ r) (hx : x ∈ (U₂.X k₂).dom) (x' : Frame (U.X k).Ψ r), Moved (U₂.X k₂) (U.X k) δ x x' →
    ∃ hx' : x' ∈ (U.X k).dom, ∃ t : ℂˣ, ((∀ τ i, ‖dmin (U₂.X k₂).Gm x τ i‖ = 1) → ‖(t : ℂ)‖ = 1) ∧
      letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
      ∃ y : FrPt Xo c (CAt σ₂),
        FrBor (S := CAt σ₂) (genScal (Dw := Dw) (S := CAt σ₂) t) (U.un k ⟨x', hx'⟩) y ∧
        FrOver d (U₂.un k₂ ⟨x, hx⟩) y

end GlobalTheory.LevModel
