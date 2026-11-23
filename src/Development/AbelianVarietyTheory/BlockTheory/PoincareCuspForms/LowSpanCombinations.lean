module

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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def hf (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  X.c τ * X.maj x τ (Data.emb τ.1 ξ)

def ExtraBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, hf X ξ x τ ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)

def lowIdx (D T : ℕ) : Finset (Fin D → ℕ) :=
  (Fintype.piFinset fun _ : Fin D => Finset.range T).filter fun al => ∑ i, al i + D < T

theorem nonempty_cmType (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have := (X.cmType τ).not.1 h
    exact ⟨⟨_, not_not.1 this⟩⟩

theorem tt_eq (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.tt ξ x τ = 1 / hf X ξ x τ := rfl

end

end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
