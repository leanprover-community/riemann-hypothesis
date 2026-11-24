module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {K : Type*}

theorem diffStep_comm (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep a (diffStep b h) = diffStep b (diffStep a h) := by
  funext m
  simp only [diffStep, sub_sub, add_comm a b]
  ring

instance diffStep_leftCommutative :
    LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) :=
  ⟨diffStep_comm⟩

theorem mixedDiff_comp_perm {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n))
    (h : (K → ℤ) → ℤ) : mixedDiff (bs ∘ σ) h = mixedDiff bs h := by
  unfold mixedDiff
  exact (σ.ofFn_comp_perm bs).foldr_eq h

end

theorem IntNumSymm.proof : IntNumSymm.Statement := by
  intro F _ K _ _ ι _ I n bs σ
  unfold intNum
  rw [mixedDiff_comp_perm]

end GroundTheory.Heights₂.Heights.FieldNumbers
