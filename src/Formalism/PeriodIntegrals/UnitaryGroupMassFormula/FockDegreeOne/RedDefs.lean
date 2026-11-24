module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves
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

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW

def KHc : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ (e : ℕ) (P : Pol p q r s),
  homogeneousComponent e (fockAct1 p q r s (Eab a b) P) =
    fockAct1 p q r s (Eab a b) (homogeneousComponent e P)

def KHarm : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ P : Pol p q r s,
  Harm2 P → Harm2 (fockAct1 p q r s (Eab a b) P)

def HcHarm : Prop := ∀ p q r s : ℕ, ∀ (e : ℕ) (P : Pol p q r s),
  Harm2 P → Harm2 (homogeneousComponent e P)

def HarmSub : Prop := ∀ p q r s : ℕ,
  Harm2 (0 : Pol p q r s) ∧ (∀ P Q : Pol p q r s, Harm2 P → Harm2 Q → Harm2 (P + Q)) ∧
    (∀ (c : ℂ) (P : Pol p q r s), Harm2 P → Harm2 (c • P))

def KAdj : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ P Q : Pol p q r s,
  fockInner P (fockAct1 p q r s (Eab a b) Q) = fockInner (fockAct1 p q r s (Eab b a) P) Q

def HwExist : Prop := ∀ p q r s : ℕ, ∀ U : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ U → U ≠ ⊥ →
  (∀ a b : Ix p q, sameBlock a b → ∀ u ∈ U, fockAct1 p q r s (Eab a b) u ∈ U) →
    ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ IsHW (fockAct1 p q r s) ν v

end PI.FockOneDegW
