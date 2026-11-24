module

public import Formalism.SharpRestriction.ParamsHeightRankConstant
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions

section Ev

variable {eps : ℝ} (Fm : FamP eps)

def Ev (P : ∀ x, Fm.x1 < x → Fm.Ix x → Prop) : Prop := ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, P x hx i

variable {Fm}

end Ev

theorem closed_Csz_ge (𝒞 : FamClass) (c : ℝ) : Closed 𝒞 fun Fm _ => c ≤ Fm.Csz := by
  unfold Closed
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => c, fun _ => 0⟩,
    fun Fm CH _ hL => hL.2.2.1 Fm.Csz (by simp [FamP.cMid])⟩⟩

theorem closed_Csz_ge_fn (𝒞 : FamClass) (c : List ℝ → ℝ) : Closed 𝒞 fun Fm _ => c Fm.cOut ≤ Fm.Csz := by
  unfold Closed
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, c, fun _ => 0⟩,
    fun Fm CH _ hL => hL.2.2.1 Fm.Csz (by simp [FamP.cMid])⟩⟩

end Formalism.MainNotions.DIV

end
