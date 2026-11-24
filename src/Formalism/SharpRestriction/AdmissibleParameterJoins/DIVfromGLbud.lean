module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLb
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
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

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

variable {D : D7} {L : SizeData₂ D}

theorem gammaDiscriminant_budget_of_sizes {Cn cL CG : ℝ} (hcL : 1 ≤ cL) (hCG : 0 ≤ CG) (hN : NumsL D L Cn cL) (hG : FactDGam D CG) :
    WeightDegreeSizes.StabiliserLogBound D L (4 * CG) := by
  unfold WeightDegreeSizes.StabiliserLogBound
  unfold FactDGam at hG
  intro u
  have hNu := hN u
  unfold flipTwoThree.Nums at hNu
  obtain ⟨hb0, -, -, -, -, hb', -, -, -, -, hNL, -, -, hx2, -, -⟩ := hNu
  have hfk : D.R.f ≤ D.R.k := by
    unfold Ranks.f
    exact D.R.f_le_k
  have hmf : D.R.m ≤ D.R.f := by
    unfold Ranks.f
    exact D.R.m_le_f
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hkN : D.R.k ≤ D.R.N D.R.m := by
    unfold Ranks.N
    omega
  have hfN : (D.R.f : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hfk.trans hkN
  have hf2 : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hm2.trans hmf
  have hm2r : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hN0 : (0 : ℝ) < D.R.N D.R.m := by linarith
  have hx1 := L.sc.one_lt_alt
  have hLr : 1 ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hbb : L.sc.x * L.sc.b / L.sc.x = L.sc.b := by
    field_simp
  rw [hbb] at hb'
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNL' : (D.R.N D.R.m : ℝ) * L.sc.L ≤ L.sc.b := by
    have : (D.R.N D.R.m : ℝ) * L.sc.L ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) := by
      apply mul_le_mul_of_nonneg_left _ hN0.le
      nlinarith
    linarith
  have hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.L := by
    have hNb : (D.R.N D.R.m : ℝ) ≤ Real.exp L.sc.L := by
      have : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L.sc.L := le_mul_of_one_le_right hN0.le hLr
      have hb : L.sc.b = Real.exp L.sc.L := rfl
      linarith
    calc Real.log (D.R.N D.R.m : ℝ) ≤ Real.log (Real.exp L.sc.L) := Real.log_le_log hN0 hNb
      _ = L.sc.L := Real.log_exp _
  have hlogf : Real.log (D.R.f : ℝ) ≤ Real.log (D.R.N D.R.m : ℝ) := Real.log_le_log (by linarith) hfN
  have hlog : Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.sc.L := by
    rw [Real.log_mul (by linarith) hN0.ne']
    linarith
  have hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  have hb0' : 0 < L.sc.b := Real.exp_pos _
  have key : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.B0 := by
    have h1 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤
        (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * (2 * L.sc.L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * L.sc.L) ≤ (D.R.f : ℝ) * L.sc.b :=
      mul_le_mul_of_nonneg_left hNL' (by positivity)
    have h3 : (D.R.f : ℝ) * L.sc.b * 1 ≤ (D.R.f : ℝ) * L.sc.b * ((D.R.m : ℝ) * L.sc.L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [hB0]
    nlinarith
  have hG' := hG u
  have := mul_le_mul_of_nonneg_left key hCG
  nlinarith

end Formalism.MainNotions.J

end
