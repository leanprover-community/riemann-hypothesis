module

public import Formalism.HermitianCurvature.StatementTL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

theorem identity_operator : TL.IdOp := by
  intro k r Wp Wq _ _ _ _ _ Bs
  let T : B.DTerm k r Wp Wq :=
    { coef := fun _ => 1
      coefAdj := fun _ => 1
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun _ _ _ => rfl }
  have hap : ∀ F, B.opApply [T] F = F := by
    intro F
    funext g
    simp [B.opApply, B.Rw, T]
  refine ⟨[T], ⟨?_, ?_, ?_⟩, hap⟩
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨?_, ?_⟩ <;> intro g₀ _ <;>
      refine ⟨Set.univ, fun _ => 1, ?_, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩
    all_goals
      first
      | exact isOpen_univ
      | exact contDiffOn_const
      | (open scoped Formalism.FourierDecayAlt.B in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Elementwise in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Operator in exact contDiffOn_const)
      | exact @contDiffOn_const _ _ _ _ _ _ _ _ _ _ _ _
  · intro p _ f _ g _
    simp only [hap]
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨fun _ => 1, 0, 0, 0, [], ⟨1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp
    · intro g
      simp
    · intro l _ _
      simp
    · simp [T]
    · simp
    · intro g _
      simp [C6.monoM, C6.Epart, T]

end

end Formalism.FourierDecayAlt.P
