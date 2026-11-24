module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def IsInvForm {k r : ℕ} (R R' : Rep k r) (Bf : R.H → R'.H → ℂ) : Prop :=
  (∀ x ∈ R.sm, ∀ x' ∈ R.sm, ∀ y ∈ R'.sm, Bf (x + x') y = Bf x y + Bf x' y) ∧
  (∀ (a : ℂ), ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf (a • x) y = a * Bf x y) ∧
  (∀ x ∈ R.sm, ∀ y ∈ R'.sm, ∀ y' ∈ R'.sm, Bf x (y + y') = Bf x y + Bf x y') ∧
  (∀ (a : ℂ), ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x (a • y) = star a * Bf x y) ∧
  (∀ g ∈ GG k r, ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf (R.σ g x) (R'.σ g y) = Bf x y) ∧
  ∃ (C : ℝ) (Ws Ws' : List (List (Mx k r))), (∀ W ∈ Ws ++ Ws', ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
    ∀ x ∈ R.sm, ∀ y ∈ R'.sm, ‖Bf x y‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W x‖).sum *
      (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W y‖).sum

def Poulsen : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r),
    R.IsDS ε mu → R'.IsDS ε mu' →
    (∀ Bf : R.H → R.H → ℂ, IsInvForm R R Bf → ∃ c : ℂ, ∀ x ∈ R.sm, ∀ y ∈ R.sm, Bf x y = c * ⟪y, x⟫_ℂ) ∧
    ∀ Bf : R.H → R'.H → ℂ, IsInvForm R R' Bf → (∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x y = 0) ∨
      ∃ U : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)

end BranchingSupport
