module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerIntegerDecompositionByTau
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.kummerTower_integer_decomposition_by_tau : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (y : Ω), IsInt (p := p) y →
    (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ o w : Ω, IsInt (p := p) o ∧ (∀ g ∈ Ggeo (p := p) Ω, g o = o) ∧ IsInt (p := p) w ∧
    (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) ∧
    (T.ζ 1 - 1) * y = (T.ζ 1 - 1) * o + (τ w - w) := by
  first | exact @GlobalTheory.K5.Decomp.decomp | exact GlobalTheory.K5.Decomp.decomp | (intros; apply GlobalTheory.K5.Decomp.decomp <;> assumption)
