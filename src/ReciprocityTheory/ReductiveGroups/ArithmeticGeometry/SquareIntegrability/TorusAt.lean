module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsTorusAt (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (T : PT E) : Prop :=
  ∃ φ : (Fin r → E) →+ Vsp T.dim, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    (∀ y, y ∈ T.L ↔ ∃ v ∈ X.Λ, φ v = y) ∧
    (∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = act α (φ v)) ∧
    (∀ v ∈ X.Λ, ‖φ v‖ ^ 2 = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∧
    (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, (Hf (φ u) (φ v)).im =
      s * ((Algebra.trace ℚ E (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ))

def phiFD (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (th : ℝ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : ℝ :=
  if X.la1 x < th then 2 * PT.f E / (PT.rd E ^ 2 * X.la1 x ^ 2) else 0

def TorusAtLa1Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), x ∈ X.dom → ∀ T : PT E, IsTorusAt X x T →
      T.la1 = X.la1 x ∧ ∀ th : ℝ, T.ph th = phiFD X th x

end

end ReciprocityTheory.ChartRestriction.G.I2
