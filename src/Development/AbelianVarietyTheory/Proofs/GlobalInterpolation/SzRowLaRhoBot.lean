module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_la_rho_bot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  intro eps he he' C hC
  have hLa1 : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (eps + eps / 100)
    (2 * C.GK.La * CN ^ 2) 2 (by linarith)
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    ((2 + 8 * eps + eps / 100) + -(eps / 8) + eps + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 32 0 (by linarith)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    (eps / 100 + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 2 1 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max (max x1 x2) (max x3 x4)) 1, ?_⟩⟩⟩
  intro D L hε hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hone⟩ := hx
  have hpos : 0 < L.sc.x := by linarith
  obtain ⟨hlo, hhi⟩ := (h1 L.sc hε hx1).2.2 C.GK hLa1
  rw [← hV.La_eq] at hlo hhi
  have hup : L.LaG ≤ L.sc.x ^ (eps + eps / 100) := by
    have := h2 _ hx2
    rw [hε] at hhi
    calc L.LaG ≤ _ := hhi
      _ = 2 * C.GK.La * CN ^ 2 * L.sc.x ^ eps * Real.log L.sc.x ^ 2 := by ring
      _ ≤ _ := this
  refine ⟨⟨hlo, ?_⟩, ?_, ?_⟩
  · simpa only [szTh, hε] using hup
  · have hn := hV.ranks.n_le
    obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
    have h3' := h3 _ hx3
    have h4' := h4 _ hx4
    simp only [Real.rpow_add hpos, pow_zero, pow_one, mul_one] at h3' h4'
    rw [← Real.rpow_add hpos 2, ← Real.rpow_add hpos (2 + 8 * eps) (eps / 100), ← Real.rpow_add hpos (9 / 2),
      ← Real.rpow_add hpos eps (eps / 100)] at h3'
    rw [← Real.rpow_add hpos (9 / 2), ← Real.rpow_add hpos eps (eps / 100)] at h4'
    have hL0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hpos _).le hlo
    unfold SizeRho szNst szTh Scale.delta1
    rw [hε] at hn hk ⊢
    have hkpos : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hpos _) hk
    have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hone
    rw [← add_div, div_le_iff₀ hkpos]
    have hA : 4 * (2 * (D.R.n : ℝ) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps * L.LaG ≤
        4 * (2 * (2 * L.sc.x ^ (2 + 8 * eps + eps / 100)) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps *
          L.sc.x ^ (eps + eps / 100) := by gcongr
    have hB : L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.LaG ≤
        L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.sc.x ^ (eps + eps / 100) := by gcongr
    have hK : L.sc.x ^ (-2 : ℝ) * L.sc.x ^ (9 / 2 + 10 * eps) ≤ L.sc.x ^ (-2 : ℝ) * D.R.k := by gcongr
    linarith
  · intro t
    have := hV.bT_le t
    unfold szNst
    exact this

end GlobalTheory.EX
