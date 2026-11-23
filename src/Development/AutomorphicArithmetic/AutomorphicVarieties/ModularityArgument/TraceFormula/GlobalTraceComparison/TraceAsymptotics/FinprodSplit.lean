module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem finprodSplit : FinprodSplit := by
  intro α S Z T F hZ hT hd h1
  classical
  have key : ∏ᶠ w ∈ S, F w = ∏ w ∈ T ∪ Z, F w := by
    apply finprod_mem_eq_prod_of_inter_mulSupport_eq
    ext w
    simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.coe_union, Set.mem_union,
      Finset.mem_coe]
    constructor
    · rintro ⟨hS, hF⟩
      refine ⟨?_, hF⟩
      by_contra hn
      exact hF (h1 w hS (fun h => hn (Or.inr h)) (fun h => hn (Or.inl h)))
    · rintro ⟨hw | hw, hF⟩
      · exact ⟨hT w hw, hF⟩
      · exact ⟨hZ w hw, hF⟩
  rw [key, Finset.prod_union hd, mul_comm]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
