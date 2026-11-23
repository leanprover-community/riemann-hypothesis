module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanCosetSumLe
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeSumBound
import Formalism.SharpRestriction.CuspSpanNormBounds.MinorIntegralityTorus
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section
open scoped Classical
open Formalism.MainNotions Formalism.MainNotions.KTwoCosetCount Formalism.MainNotions.MinorIntegralityTorus
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem sum_labels_one_record : ∀ (CH C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), 1 ≤ Cl → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E), (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) → ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b (21 + 4 * |CH|) D.R.m D.R.f ^ ((21 + 4 * |CH|) * (D.R.rS : ℝ)) := by
  intro CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hCl1 hH j hj T hTm
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, rfl, rfl⟩ := hTm δ hδ
    exact labFacts_conc t
  have h := kloostermanCosetSum_le Formalism.MainNotions.MinorIntegralityTorus.NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact
  unfold H1C
  refine h.trans ?_
  have hb : 1 ≤ large₂.sc.b := by linarith [KappaEndpoints.two_le_scale_b D large₂]
  have hCl0 : 0 < Cl := by linarith
  have hc0 : 0 ≤ ccOf CH Cl := by unfold ccOf; positivity
  have hcle : ccOf CH Cl ≤ 21 + 4 * |CH| := by
    unfold ccOf
    have : 4 / Cl ≤ 4 := by rw [div_le_iff₀ hCl0]; linarith
    linarith
  unfold Hb
  rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS := by positivity
  have e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) =
      ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  have e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) =
      (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx

end GlobalTheory.Core.Deg
