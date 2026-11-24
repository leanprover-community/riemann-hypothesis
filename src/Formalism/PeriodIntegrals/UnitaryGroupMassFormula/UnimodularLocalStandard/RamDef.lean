module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepArith
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def UnitVecRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m]
    [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (x0 y0 : ℤ) (T : Finset m) (i₀ : m),
    KeyHyps a b c d ha hd lam hlam m Λ d x0 y0 T i₀ →
    ∀ x : m → ℂ, SatMem d Λ x → (∀ j ∈ T, x j = 0) →
      (x = 0 ∨ ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m x x = repKappa a b d ha hd lam hlam * p / q) →
    ∀ z₀ : m → ℂ, SatMem d Λ z₀ → (∀ j ∈ T, z₀ j = 0) → stdH (cmL a b d ha hd lam hlam) m z₀ x = 0 → z₀ ≠ 0 →
    ∃ y : m → ℂ, SatMem d Λ y ∧ (∀ j ∈ T, y j = 0) ∧ stdH (cmL a b d ha hd lam hlam) m y x = 0 ∧
      ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m y y = repKappa a b d ha hd lam hlam * p / q

end PI.UnitaryGroupMassFormula.UnimodLocStd
