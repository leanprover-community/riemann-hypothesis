module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MulApply
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

@[expose] public section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.FiniteOrbit

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem exists_finiteDimensional_stable (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type)
    [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M))
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) (m : M)
    (hm : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) :
    ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by
  first
  | exact @_root_.GlobalTheory.OrbitGrowth.main
  | exact _root_.GlobalTheory.OrbitGrowth.main
  | (apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrbitGrowth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrbitGrowth.main ..)

end GlobalTheory.FiniteOrbit
