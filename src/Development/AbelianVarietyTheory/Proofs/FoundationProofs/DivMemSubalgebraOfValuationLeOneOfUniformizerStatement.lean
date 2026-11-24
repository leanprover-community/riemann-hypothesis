module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivMemSubalgebraOfValuationLeOneOfUniformizer
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  first | exact @GlobalTheory.K5.IntFrac.mem_of_div_le_one | exact GlobalTheory.K5.IntFrac.mem_of_div_le_one | (intros; apply GlobalTheory.K5.IntFrac.mem_of_div_le_one <;> assumption)
