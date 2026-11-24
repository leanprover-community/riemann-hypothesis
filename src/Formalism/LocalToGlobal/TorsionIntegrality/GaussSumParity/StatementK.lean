module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TrDual
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def muPrime (l : ℕ) [Fact l.Prime] : Set ℂ_[l] := {ζ | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}

def ringA (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := Subring.closure (muPrime l)

def ringB (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := (ringA l).topologicalClosure

def KurUnram : Prop := ∀ (l : ℕ) [Fact l.Prime], Unram l (MaximalUnramifiedExtension l)

def KurIntegers : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringB l, ‖x‖ < 1 → ∃ y ∈ ringB l, x = (l : ℂ_[l]) * y) ∧
    (∀ x ∈ ringB l, ‖x‖ = 1 → x⁻¹ ∈ ringB l)

def KurRoots : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ¬ l ∣ n → ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ n

def KurComplete : Prop := ∀ (l : ℕ) [Fact l.Prime], CompleteSpace (MaximalUnramifiedExtension l)

def KurFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 2 < l →
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ ∧
      ∀ ζ : MaximalUnramifiedExtension l, (ζ : ℂ_[l]) ∈ muPrime l → σ ζ = ζ ^ l

def TrDualExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → Even d → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∃ om oms : Fin (d / 2) → K, OwOK d σ om oms ∧ TrDual d σ om oms

end Formalism.L2.Th1.D
