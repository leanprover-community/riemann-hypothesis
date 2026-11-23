module

public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsTwoTorsionOffKernels
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (latI UniqInv CMConjSet)

def IsLatClosure : Prop :=
  ∀ a b : ℂ, ((starRingEnd ℂ) a * b).im ≠ 0 → IsLat (AddSubgroup.closure {a, b})

def IsLatSmul : Prop := ∀ (Λ : AddSubgroup ℂ) (c : ℂ), c ≠ 0 → IsLat Λ → IsLat (c • Λ)

def LatILat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ x : K, x ^ 2 = -(d : K) →
    Module.finrank ℚ K = 2 → ∀ (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (δ : ℂ), 𝔞 ≠ ⊥ → δ ≠ 0 →
      IsLat (latI φ 𝔞 δ) ∧ HasCM d (latI φ 𝔞 δ)

end Formalism.L2.Th1.F2
