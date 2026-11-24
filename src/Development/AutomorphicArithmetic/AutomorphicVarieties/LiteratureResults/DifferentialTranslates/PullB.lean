module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem pullB : PullB := by
  intro V F _ _ _ _ _ _ Y hY hC l hl q w hw
  obtain ⟨hlsm, hlpos, _⟩ := hl
  have hφY : ∀ p ∈ Y, l p • p ∈ Y := fun p hp => hC _ (hlpos p hp) p hp
  have hφ : ∀ p ∈ Y, ContDiffAt ℝ ∞ (fun x => l x • x) p := fun p hp =>
    (hlsm.contDiffAt (hY.mem_nhds hp)).smul contDiffAt_id
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w (l p • p) := fun p hp =>
    hw.contDiffAt (hY.mem_nhds (hφY p hp))
  refine ⟨?_, ?_⟩
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply altSmooth V V F q (pull l w) p
    intro v
    have hcomp : ContDiffAt ℝ ∞ (fun y => w (l y • y)) p :=
      ContDiffAt.comp (g := w) (f := fun x => l x • x) p (hwat p hp) (hφ p hp)
    have h := applySmooth V V F q (fun y => w (l y • y))
      (fun i y => fderiv ℝ (fun x => l x • x) y (v i)) p hcomp
      (fun i => ((hφ p hp).fderiv_right (by simp)).clm_apply contDiffAt_const)
    exact h
  · intro p hp
    exact extDeriv_pullback ((hwat p hp).differentiableAt (by simp)) (hφ p hp)
      (by simpa using (WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞))

end UpperTheory.V.Lit.Dr
