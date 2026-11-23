module

public import ReciprocityTheory.SemistableReduction.LatSemiSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate Module
open scoped ComplexOrder

def ballRatio (r : ℕ) : ℝ := (1 + 1 / (7 * (r : ℝ))) / (1 - 1 / (7 * (r : ℝ)))

def signMat (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun k : Fin r => sgn p k

def BoundedBallStatement : Prop :=
  ∀ (r p : ℕ) (H : Matrix (Fin r) (Fin r) ℂ) (s : ℝ),
    H.PosDef → H * signMat p r * H = signMat p r → 0 ≤ s → s < 1 →
    (∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) →
    ∀ u : Fin r → ℂ, hq H u ≤ (1 + s) / (1 - s) * normSq u ∧
      normSq u ≤ (1 + s) / (1 - s) * hq H u

def NoContraction {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), u ≠ 0 → hq (H σ) (N.map σ *ᵥ u) < hq (H σ) u) → N = 0

end ReciprocityTheory.MultiplicativeHeights
