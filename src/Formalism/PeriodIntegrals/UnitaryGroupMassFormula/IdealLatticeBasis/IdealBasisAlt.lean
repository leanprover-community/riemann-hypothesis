module

public import Formalism.PeriodIntegrals.IdealLattice
public import Formalism.PeriodIntegrals.AreaLat
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

open NumberField

namespace PI.IdealLatticeWork

def OKArea : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ), Module.finrank ℚ K = 2 → IsEmpty (K →+* ℝ) →
    ∀ b : Module.Basis (Fin 2) ℤ (𝓞 K),
      |((starRingEnd ℂ) (φ (b 0 : K)) * φ (b 1 : K)).im| = Real.sqrt |(NumberField.discr K : ℝ)| / 2

def IdealBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (cc : Ideal (𝓞 K)), cc ≠ ⊥ →
    ∃ c₁ ∈ cc, ∃ c₂ ∈ cc, (∀ c ∈ cc, ∃ m n : ℤ, c = m • c₁ + n • c₂) ∧
      ∃ p q r s : ℤ, c₁ = p • b 0 + q • b 1 ∧ c₂ = r • b 0 + s • b 1 ∧
        (p * s - q * r).natAbs = Ideal.absNorm cc

def OKBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → Nonempty (Module.Basis (Fin 2) ℤ (𝓞 K))

def Assemble : Prop := OKArea → IdealBasis → OKBasis → PI.AreaLat → PI.IdealLattice

end PI.IdealLatticeWork
