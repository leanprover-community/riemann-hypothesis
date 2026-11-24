module

public import Formalism.HermitianCurvature.StatementM
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx1

theorem star_sc (P : Par) (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  ext i j
  rw [Matrix.star_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end Formalism.FourierDecayAlt.P.Mx1

namespace Formalism.FourierDecayAlt.P

open Mx1

theorem model_nontrivial : Formalism.FourierDecayAlt.M.ModelNontrivial := by
  intro P
  have key : ∀ w : Pr P.r, sc P w = 0 → w = 0 := by
    intro w h
    have := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simpa [sc] using this
  refine ⟨⟨⟨0, 1, fun h => ?_⟩⟩, fun f fb h => ?_⟩
  · have h1 : (1 : Pr P.r) = 0 := key 1 (by unfold sc; rw [map_one]; exact h.symm)
    have h2 : (1 : Op P.r) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simp at h2
  · have h1 := key _ h
    have h2 : (mulOp f) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simpa [mulOp] using h2

theorem star_generators : Formalism.FourierDecayAlt.M.StarGens := by
  intro P
  have hs : ∀ X Y : Op P.r, star (mk X Y) = mk Y X := fun X Y => rfl
  have hneg : ∀ X Y : Op P.r, -(mk X Y : Pr P.r) = mk (-X) (-Y) := fun X Y => rfl
  have mc : ∀ f g : Fn P.r, mulOp f * mulOp g = mulOp g * mulOp f := fun f g => by
    refine LinearMap.ext fun x => ?_
    simp only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, mul_comm f g]
  refine ⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cA cbA; rw [star_sc]; rfl
  · unfold ciA cbiA; rw [star_sc]; rfl
  · unfold pA pbA
    rw [star_sc]
    unfold sc
    rw [← map_neg]
    congr 1
    unfold pP pbP
    rw [hs, hneg, neg_neg]
  · unfold zA zbA; rw [star_sc]; rfl
  · unfold ziA zbiA; rw [star_sc]; rfl
  · unfold ggA; rw [star_sc]; rfl
  · unfold ggiA; rw [star_sc]; rfl
  · have e1 : star (dzP : Pr P.r) = -dzbP := by
      unfold dzP dzbP
      rw [hs, hneg, neg_neg]
    have e2 : star (zbP : Pr P.r) = zP := rfl
    have e3 : star (ggiP P.TT : Pr P.r) = ggiP P.TT := rfl
    have e4 : (ggiP P.TT : Pr P.r) * zP = zP * ggiP P.TT := by
      unfold ggiP zP fnP M.mk
      refine Prod.ext (mc _ _) ?_
      show MulOpposite.op _ * MulOpposite.op _ = MulOpposite.op _ * MulOpposite.op _
      rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, mc]
    unfold nabA nabsA
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext π
    rw [Pi.star_apply, star_add, star_smul, star_mul, e1, e2, e3, e4, Complex.star_def, Complex.conj_ofReal]

end Formalism.FourierDecayAlt.P
