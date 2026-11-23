module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCommonFixedLeOneOfCommutingHecke
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr

@[expose] public section

open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.finrank_commonFixed_le_one_of_commuting_hecke : ∀ (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Monoid (H c)] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V), (∀ c, e c * e c = e c) → (∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g)) → (∀ c c', c ≠ c' → Commute (e c) (e c')) → (∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h)) → (∀ c g h, e c * a c g * e c * a c h * e c = e c * a c h * e c * a c g * e c) → (∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤) → ∀ W : Submodule ℂ V, (∀ v ∈ W, ∀ c, e c v = v) → finrank ℂ W ≤ 1 := by
  first | exact @GlobalTheory.CommutingHecke.finrank_fixed_le_one | exact GlobalTheory.CommutingHecke.finrank_fixed_le_one | (intros; apply GlobalTheory.CommutingHecke.finrank_fixed_le_one <;> assumption)
