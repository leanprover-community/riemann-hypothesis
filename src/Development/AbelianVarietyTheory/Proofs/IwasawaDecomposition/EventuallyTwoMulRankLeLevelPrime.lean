module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.Top.Bl

theorem two_mul_r_le_g_level : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ k,
    2 * (w.D Z).R.r ≤ (w.D Z).host.g k := by
  refine evG_all fun K => lg_all K fun B f T hO _ T' w Z k => ?_
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hR' : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hg : B.toPre.host.g = K.P.H.g := by rw [hB]; rfl
  show 2 * B.R.r ≤ B.host.g k
  rw [show B.host.g k = K.P.H.g k from congrFun hg k, show B.R.r = K.P.R.r from by rw [hR']]
  have hgk : ((K.P.R.k : ℝ) * K.s.b) ^ 8 ≤ (K.P.H.g k : ℝ) := (K.ok.val.2.2.2.2.1 k).1
  have hb : 1 ≤ K.s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [K.s.one_lt_alt]) _)
  have hk0 : (0 : ℝ) ≤ K.P.R.k := Nat.cast_nonneg _
  have hkb : (K.P.R.k : ℝ) ^ 8 ≤ (K.P.H.g k : ℝ) :=
    le_trans (pow_le_pow_left₀ hk0 (le_mul_of_one_le_right hk0 hb) 8) hgk
  have hk8 : (K.P.R.k) ^ 8 ≤ K.P.H.g k := by exact_mod_cast hkb
  have h2k : 2 ≤ K.P.R.k := by
    have := K.P.R.f_le_k
    have : 0 < K.P.R.ord := K.P.R.ord_pos
    omega
  have hr : 2 * K.P.R.r ≤ 4 * K.P.R.k := by
    have := K.P.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have h4 : 4 * K.P.R.k ≤ K.P.R.k ^ 8 := by
    calc 4 * K.P.R.k ≤ K.P.R.k ^ 7 * K.P.R.k := by
          apply Nat.mul_le_mul_right
          calc 4 ≤ 2 ^ 7 := by norm_num
            _ ≤ K.P.R.k ^ 7 := Nat.pow_le_pow_left h2k 7
      _ = K.P.R.k ^ 8 := by ring
  omega

end GlobalTheory.Mem.Top.Bl
