module

public import Formalism.PeriodIntegrals.ZerosWindowIn
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open Metric

namespace PI.ZW

def RightNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

def RightHalfWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), (χ ≠ 1 ∨ N = 1) → ∀ t : ℝ,
    (RightNear χ t).Finite ∧
    ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))

def RightChiWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ t : ℝ,
    (RightNear χ t).Finite ∧
    ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))

def RightOneWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), N = 1 → ∀ t : ℝ,
    (RightNear χ t).Finite ∧
    ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))

def RightChi : Prop := PI.LBoundRight → PI.LInvRight → ∃ C : ℝ, RightChiWith C

def RightOne : Prop := PI.ZetaBoundRight → PI.LInvRight → ∃ C : ℝ, RightOneWith C

def Transfer : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
    DirichletCharacter.LFunction χ ρ = 0 →
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 ∧
    analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≤
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ)

def JensenCount : Prop :=
  ∀ (f : ℂ → ℂ) (c : ℂ) (M : ℝ), AnalyticOnNhd ℂ f (closedBall c (19 / 10)) → f c ≠ 0 → 1 ≤ M →
    (∀ z ∈ sphere c (19 / 10), ‖f z‖ ≤ M) →
    ∀ S : Set ℂ, S ⊆ {z | z ∈ closedBall c (37 / 20) ∧ f z = 0} →
      S.Finite ∧
      ∑ᶠ z ∈ S, (analyticOrderNatAt f z : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log ((19 / 10) / (37 / 20))

end PI.ZW
