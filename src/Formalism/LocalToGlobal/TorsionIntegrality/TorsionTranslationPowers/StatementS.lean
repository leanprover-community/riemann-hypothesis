module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
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

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def IsShiftSys {K : Type} [NormedField K] [DecidableEq K] (W : WeierstrassCurve K)
    (A : AddSubgroup W.toAffine.Point) (S : W.toAffine.Point) (H : W.toAffine.Point → K⟦X⟧)
    (c : W.toAffine.Point → K) : Prop :=
  OneUnit (H 0) ∧ (∀ Q ∈ A, Q ≠ 0 → c Q ≠ 0) ∧
  ∀ P ∈ A, ∀ Q ∈ A, Q ≠ 0 → ∃ ρ : K, ‖ρ‖ = 1 ∧
    H (P + Q) * H (P - Q) = C (ρ * c Q ^ 2) * (C (px W Q) - xT W (P + S)) * H P ^ 2

def ShiftUnit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ (A : AddSubgroup W.toAffine.Point) [Finite A], ‖(Nat.card A : K)‖ = 1 →
    ∀ (S : W.toAffine.Point), S ∉ A →
    (∀ Q ∈ A, Q ≠ 0 → ‖px W Q‖ ≤ 1 ∧ ‖py W Q‖ ≤ 1) →
    (∀ P ∈ A, ‖px W (P + S)‖ ≤ 1 ∧ ‖py W (P + S)‖ ≤ 1) →
    ∀ (H : W.toAffine.Point → K⟦X⟧) (c : W.toAffine.Point → K), IsShiftSys W A S H c →
      (∀ Q ∈ A, Q ≠ 0 → ‖c Q‖ = 1) ∧
      ∀ P ∈ A, ‖constantCoeff (H P)‖ = 1 ∧ OneUnit (C (constantCoeff (H P))⁻¹ * H P)

def ShiftPtsInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ (A : AddSubgroup W.toAffine.Point) [Finite A], ‖(Nat.card A : K)‖ = 1 →
    ∀ (S : W.toAffine.Point), S ∉ A → S + S = 0 → ‖px W S‖ ≤ 1 → ‖py W S‖ ≤ 1 →
      (∀ Q ∈ A, Q ≠ 0 → ‖px W Q‖ ≤ 1 ∧ ‖py W Q‖ ≤ 1) ∧
      (∀ P ∈ A, ‖px W (P + S)‖ ≤ 1 ∧ ‖py W (P + S)‖ ≤ 1)

end Formalism.L2.Th1.E
