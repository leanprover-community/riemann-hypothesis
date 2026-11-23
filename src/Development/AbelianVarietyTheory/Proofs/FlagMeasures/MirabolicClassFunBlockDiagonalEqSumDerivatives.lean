module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClassFunctionBernsteinZelevinskyDerivativeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicConjInvariantEqSumInducedDerivativesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfanStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem inMir_diag1_succ {g : ℕ} [Fact g.Prime] {k : ℕ} (h : Gn g k) :
    InMir ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) := by
  unfold InMir diag1 toG
  intro i j hi
  split_ifs with hu
  · have hk : ¬ ((i : ℕ) < k) := by omega
    refine (congrFun (congrFun hu.unit_spec i) j).trans ?_
    simp [hk]
  · rfl

theorem mirClass_diag1_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (k : ℕ) (F : Gn g (k + 1) → ℂ), IsMirClass F → ∀ h : Gn g k, F (diag1 h (k + 1)) = ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i F) (gg ψ (k - i)) k h := by
  intro g inst ψ hψ k F hF h
  rw [GlobalTheory.T.mirabolicConjInvariant_eq_sum_induced_derivatives g ψ hψ (k + 1) F (by omega) hF (diag1 h (k + 1)) (inMir_diag1_succ h)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev g ψ i k (der ψ i F) hik (GlobalTheory.T.isClassFunction_bernsteinZelevinskyDerivative g ψ i (k + 1) F (by omega) hF) h

end GlobalTheory.GLm
