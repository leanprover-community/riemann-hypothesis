module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb
open scoped ContDiff

theorem UpperTheory.isArchSmooth_of_contDiff_chart :
    UpperTheory.V.Fb.SmTo := by
  intro E _ _ _ a φ hφ g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro x
  let L0 : ArchMatrix E a →ₗ[ℝ] TR.Lie E a := (matEq E a).symm.toLinearMap
  let L : ArchMatrix E a →L[ℝ] TR.Lie E a := LinearMap.toContinuousLinearMap L0
  have hL : ∀ z : archGroup E a, L ((z : (ArchMatrix E a)ˣ) : ArchMatrix E a) = TR.toL ((grpEq E a).symm z).val := by
    intro z
    obtain ⟨y, rfl⟩ := (grpEq E a).surjective z
    rw [MulEquiv.symm_apply_apply, coe_grpEq]
    exact (matEq E a).symm_apply_apply y.val
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix E a → ArchMatrix E a) :=
    contDiff_iff_contDiffAt.2 fun X => (NormedSpace.exp_analytic (𝕂 := ℝ) X).contDiffAt
  have hc : ContDiff ℝ ∞ fun Y : archLie E a =>
      L (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) :=
    L.contDiff.comp (contDiff_const.mul (hexp.comp (archLie E a).subtypeL.contDiff))
  have e : (fun Y : archLie E a => archSlice φ g (x * (isExpLieAlgebra E a).expG Y)) = fun Y : archLie E a =>
      TR.chart φ g (L (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) := by
    funext Y
    rw [hL, TR.chart_val, ← infEmb_grpEq, MulEquiv.apply_symm_apply]
    rfl
  rw [e]
  refine contDiff_iff_contDiffAt.2 fun Y => (TR.contDiffAt_chart hφ g ?_).comp Y hc.contDiffAt
  rw [hL]
  exact TR.val_mem_invSet _
