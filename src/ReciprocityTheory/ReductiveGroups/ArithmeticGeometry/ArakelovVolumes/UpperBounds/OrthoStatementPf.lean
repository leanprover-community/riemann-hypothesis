module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ortho_holds : OrthoStatement (E := E) := by
  intro r X x hx

  have hBor := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem (X := X) hx
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x),
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf (X := X) hx,
    fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹ :
      Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
  · intro τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    haveI : Invertible (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ) :=
      Matrix.invertibleOfIsUnitDet _ hdet
    have hM : (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).BlockTriangular id :=
      fun i j hij => (hBor τ).2 i j hij
    have hMi := Matrix.blockTriangular_inv_of_blockTriangular hM
    refine ⟨?_, fun a c hca => hMi hca⟩
    show ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹).det ≠ 0
    exact (Matrix.isUnit_nonsing_inv_det _ hdet).ne_zero
  · funext τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    show ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat x τ *
      ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ *
      (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
