module

public import Formalism.SharpRestriction.GrowthBounds.FlipOneThree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

end Formalism.MainNotions.G.SymmetricFormBlocks

namespace Formalism.MainNotions.G.SymmetricFormBlocks


theorem winA_sum (X : flipOneThree.Inst) (f : ℕ → ℝ) :
    ∑ aPlus ∈ X.winA, f aPlus = ∑ j ∈ Finset.range X.winA.card, f (X.L.a + j) := by
  unfold flipOneThree.Inst.winA
  rw [Nat.card_Icc, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

end Formalism.MainNotions.G.SymmetricFormBlocks

end
