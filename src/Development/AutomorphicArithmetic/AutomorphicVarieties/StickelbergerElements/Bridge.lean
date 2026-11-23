module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SingleInvMulGroupRingSumOverUnitsInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V

theorem UpperTheory.V.Stk.twistedStickelbergerElements_agree :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (Γ : Type) [CommGroup Γ] (φ : (ZMod M)ˣ →* Γ) (k : ℕ),
      B4.yEl k a ha φ = Stk.yForm k a φ ∧ B4.ytEl k a φ = Stk.ytEl k a φ ∧ B4.xEl a φ = Stk.xEl a φ ∧
      B4.coefMap ℚ Γ = Stk.cf ℚ Γ := by
  intro M a _ ha Γ _ φ k
  refine ⟨?_, rfl, rfl, ?_⟩
  · have e : B4.sumEl φ (B4.Ek M k) = Stk.sumEl φ (Stk.Ev M k) := rfl
    have hneg : ∀ f : ZMod M → ℚ, (Stk.sumEl φ fun b => -f b) = -Stk.sumEl φ f := by
      intro f
      simp [Stk.sumEl, Finset.sum_neg_distrib]
    have hE : Stk.Eva M k a =
        fun b => Stk.Ev M k b + -((a : ℚ) ^ k * Stk.Ev M k (Stk.yCl a b)) := by
      funext b
      simp [Stk.Eva, sub_eq_add_neg]
    simp only [B4.yEl, B4.thetaEl]
    rw [e, sub_mul, one_mul, mul_neg, Stk.single_inv_mul_groupRingSumOverUnitsInv, Stk.yForm, hE, Stk.sumEl_add, hneg]
    abel
  · apply MonoidAlgebra.ringHom_ext
    · intro n
      simp [B4.coefMap_single]
    · intro g
      simp [B4.coefMap_single]
