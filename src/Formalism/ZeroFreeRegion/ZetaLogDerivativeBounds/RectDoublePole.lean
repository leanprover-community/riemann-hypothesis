module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BdIntEqZeroOfPrimitive
public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.LFunctionBounds.ExpSumLowerBound
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZF

theorem rectangle_double_pole : RectDoublePole := by
  intro g G a b p x0 x1 y0 y1 h1 h2 h3 h4 hU hg
  obtain ⟨U, hUo, hRU, hGU⟩ := hU
  have hmem : ∀ x y : ℝ, x ∈ Set.uIcc x0 x1 → y ∈ Set.uIcc y0 y1 → (x : ℂ) + y * I ∈ U := by
    intro x y hx hy
    apply hRU
    rw [Complex.mem_reProdIm]
    simp [hx, hy]
  let B : Set ℂ := U \ {p}
  have hSides : GlobalTheory.ResRect.SidesIn x0 x1 y0 y1 B := by
    refine ⟨fun x hx => ⟨hmem x y0 hx Set.left_mem_uIcc, ?_⟩,
      fun x hx => ⟨hmem x y1 hx Set.right_mem_uIcc, ?_⟩,
      fun y hy => ⟨hmem x1 y Set.right_mem_uIcc hy, ?_⟩,
      fun y hy => ⟨hmem x0 y Set.left_mem_uIcc hy, ?_⟩⟩ <;>
      intro hp <;>
      have h := Set.mem_singleton_iff.mp hp
    · have hi := congrArg Complex.im h
      simp at hi
      linarith
    · have hi := congrArg Complex.im h
      simp at hi
      linarith
    · have hr := congrArg Complex.re h
      simp at hr
      linarith
    · have hr := congrArg Complex.re h
      simp at hr
      linarith
  have hc : ContinuousOn G B := hGU.continuousOn.mono Set.sdiff_subset
  have hd : ContinuousOn (fun w : ℂ => w - p) B := continuousOn_id.sub continuousOn_const
  have hn : ∀ w ∈ B, w - p ≠ 0 := fun w hw =>
    sub_ne_zero.mpr fun h => hw.2 (Set.mem_singleton_iff.mpr h)
  have hb : ContinuousOn (fun w : ℂ => b / (w - p)) B := continuousOn_const.div₀ hd hn
  have hregular : ContinuousOn (fun w => g w - a / (w - p) ^ 2) B := by
    refine (hc.add hb).congr fun w hw => ?_
    simp only [Pi.add_apply]
    rw [hg w (sub_ne_zero.mp (hn w hw))]
    ring
  have hdouble : ContinuousOn (fun w : ℂ => a / (w - p) ^ 2) B :=
    continuousOn_const.div₀ (hd.pow 2) fun w hw => pow_ne_zero _ (hn w hw)
  have hsplit := GlobalTheory.ResRect.bdInt_add hSides hregular hdouble
  simp only [sub_add_cancel, GlobalTheory.ResRect.bdInt_sq h1 h2 h3 h4 a, add_zero] at hsplit
  change GlobalTheory.ResRect.bdInt x0 x1 y0 y1 g = _
  rw [hsplit]
  have hres := Formalism.FX.rectangle_residue (fun w => g w - a / (w - p) ^ 2) G {p} (fun _ => b)
    x0 x1 y0 y1 (by linarith) (by linarith) (by simp [h1, h2, h3, h4]) ⟨U, hUo, hRU, hGU⟩
    (by
      intro w hw
      have hwp : w ≠ p := by simpa using hw
      simp only [Finset.sum_singleton]
      rw [hg w hwp]
      ring)
  exact (show GlobalTheory.ResRect.bdInt x0 x1 y0 y1 (fun w => g w - a / (w - p) ^ 2) =
    Formalism.FX.rectInt (fun w => g w - a / (w - p) ^ 2) x0 x1 y0 y1 from rfl).trans
      (by simpa only [Finset.sum_singleton] using hres)

end Formalism.ZF
