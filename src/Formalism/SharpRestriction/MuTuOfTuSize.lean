module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
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

namespace Formalism.MainNotions

open Formalism.BasicNotions

abbrev WithTw (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ TwGood Fm

theorem muTu_of_tuSize {eps : ℝ} (Fm : FamP eps) (h0 : 0 < eps) (h : TuSize Fm) : J.MuTu Fm := by
  obtain ⟨x0, h⟩ := h
  have ht : Filter.Tendsto (fun x : ℝ => x ^ (eps / 100)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by positivity)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop Fm.CTu)
  refine J.muTu_of_sizeTu Fm ⟨max (max x0 x2) (Fm.x1 + 1), fun x hx i u => ?_⟩
  have a0 : x ≥ x0 := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have a2 : x ≥ x2 := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have a1 : Fm.x1 < x := lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hx)
  refine ((h x a0 i).2 u).trans ?_
  have hL : 0 ≤ (Fm.L x i).sc.L := Real.rpow_nonneg (zero_lt_one.trans (Fm.L x i).sc.one_lt_alt).le _
  have hC : Fm.CTu ≤ (Fm.L x i).sc.x ^ szTh (Fm.L x i) := by
    unfold szTh; rw [Fm.L_x x i a1, Fm.L_eps x i]; exact hx2 x a2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) hL

end Formalism.MainNotions

end
