module

public import Mathlib.RingTheory.Valuation.RamificationGroup
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
import Formalism.ConjugateSelfDual.Statement

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual
open scoped Pointwise

namespace GlobalTheory.QuadSplit

theorem mem_decompositionSubgroup_iff' {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) : g ∈ A.decompositionSubgroup K ↔ ∀ x, g x ∈ A ↔ x ∈ A := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A) (x := x), h]
    rfl
  · intro h
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h]
    simp [AlgEquiv.smul_def]

end GlobalTheory.QuadSplit
