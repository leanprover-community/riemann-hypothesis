module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped Classical
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRow

theorem exists_row_level_analytic (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticP) : StepAnalyticConstantsP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀),
    fun C' Cl e1 e2 D large₂ X Y u u' hTies hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, hBk',
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hTies hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'⟩

end GlobalTheory.NGRow
