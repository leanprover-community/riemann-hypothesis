module

public import Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Classical

def ConcreteFormsLevelZero (D : D7) (u : D.what₂.Word) : Prop := FormsTwistCompatibilityFamily D u ∧ product_first_zeroth_parts.admS D u

def FreeTT (D : D7) (u : D.what₂.Word) : Prop := ConcreteFormsLevelZero D u → Nonempty (product_first_zeroth_parts.FreeT D u)

def SlopeLineT (D : D7) (u : D.what₂.Word) : Prop := product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → product_first_zeroth_parts.SlopeLine D u

def SecondBranchIntegralityUnderForms (D : D7) (u : D.what₂.Word) : Prop :=
  product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength D u

variable {eps : ℝ}

theorem slope_free_branch_family (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) (hWT : ∀ (D : D7) (u : D.what₂.Word), FreeTT D u)
    (hμT : ∀ (D : D7) (u : D.what₂.Word), SlopeLineT D u) (hBT : ∀ (D : D7) (u : D.what₂.Word), SecondBranchIntegralityUnderForms D u) :
    FamU Fm (fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) ∧ FamU Fm product_first_zeroth_parts.SlopeLine ∧ FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength := by
  unfold FamU at tT ⊢
  obtain ⟨x0, hx⟩ := tT
  exact ⟨⟨x0, fun x h0 h1 i u hS => hWT _ u (hx x h0 h1 i u hS)⟩,
    ⟨x0, fun x h0 h1 i u hS => hμT _ u hS (hx x h0 h1 i u hS)⟩,
    ⟨x0, fun x h0 h1 i u hS => hBT _ u hS (hx x h0 h1 i u hS)⟩⟩

end Formalism.MainNotions.RT

end
