module

public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

def hq (χ : Matrix (Fin ρ) (Fin ρ) E) (η : Fin ρ → E) : E :=
  ∑ a, ∑ b, η a * χ a b * cc (η b)

def IsExpoFD (X : Data E r) (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) : Prop :=
  IsHermE χ ∧ ∀ k, ∃ z : ℤ, phZ X cu χ k = z

def KilledFD (X : Data E r) (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) (c : ℝ) : Prop :=
  ∃ η : Fin ρ → E, η ≠ 0 ∧ (∑ a, η a • cu.e a) ∈ X.Λ ∧ ∑ τ : X.Ψ, (τ.1 (hq χ η)).re ≤ c

def MaxCuspsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r),
    (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X ρ, ξ ∈ Submodule.span E (Set.range cu.e)) →
    (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) →
    ∀ (la : Wt X.Ψ r),
    (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ,
      (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) →
    ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
      (P ∈ X.SSgt la c ↔
        ∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c →
          ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0)

end Formalism.L2.Pj.QAt
