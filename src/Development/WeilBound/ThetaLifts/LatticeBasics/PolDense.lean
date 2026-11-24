module

public import Development.WeilBound.ThetaLifts.ConeHypotheses.PolDense
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
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

namespace GlobalTheory.ThK.Dbl

open scoped Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem polDense : PositivityTheory.ThKG.PolDense := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have h0 := fun T hT => Dense.pol_dense M hP.base hP.herm hP.skew T hT
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  by_contra hnd
  obtain ⟨x, hx⟩ : ∃ x, x ∉ (M.Pol B.ψ B.emb).topologicalClosure := by
    by_contra h
    push Not at h
    exact hnd (eq_top_iff.2 fun x _ => h x)
  obtain ⟨f, u, hfs, hfx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (((M.Pol B.ψ B.emb).topologicalClosure.restrictScalars ℝ).convex)
    (M.Pol B.ψ B.emb).isClosed_topologicalClosure hx
  have hf0 : ∀ a ∈ (M.Pol B.ψ B.emb).topologicalClosure, f a = 0 := by
    intro a ha
    by_contra hne
    have hmem : ((((|u| + 1 : ℝ) : ℂ) / f a) • a) ∈ (M.Pol B.ψ B.emb).topologicalClosure :=
      (M.Pol B.ψ B.emb).topologicalClosure.smul_mem _ ha
    have hlt := hfs _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at hlt
    simp at hlt <;> linarith [le_abs_self u]
  have hfz : f = 0 := h0 f (fun g hg => hf0 g ((M.Pol B.ψ B.emb).le_topologicalClosure hg))
  have h00 := hfs 0 (Submodule.zero_mem _)
  rw [hfz] at hfx
  simp at hfx h00
  linarith

end GlobalTheory.ThK.Dbl

end
