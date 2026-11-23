module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
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

@[expose] public section

set_option autoImplicit false



open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

theorem ppv_deg_three_eq_deg_two {D : D7} (large₂ : SizeData₂ D) :
    WeightFamilies.PPv D large₂ 1041 3 = WeightFamilies.PPv D large₂ (1041 * zBase large₂) 2 := by
  have h : (0 : ℝ) < zBase large₂ := lt_of_lt_of_le one_pos (WeightFamilies.one_le_zBase large₂)
  unfold WeightFamilies.PPv
  rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add h, Real.rpow_one, mul_assoc]

theorem inputsR_deg_two : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ X (kR CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → InputsR large₂ X (k4 large₂ CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ CL H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus h
  obtain ⟨h1, h2, h3, G, Gc, PH, Prw, Pet, Pd, h4, ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩, h6⟩ := h
  have e := ppv_deg_three_eq_deg_two large₂
  refine ⟨h1, ?_, h3, G, Gc, PH, Prw, Pet, Pd, h4, ⟨f1, f2, f3, ?_, f5, f6, f7, f8, f9, f10, f11, f12⟩, h6⟩
  · intro F σ
    have := h2 F σ
    change _ ≤ Real.exp (WeightFamilies.PPv D large₂ 1041 3 * _) * _ at this
    rw [e] at this
    exact this
  · have := f4
    change WeightFamilies.PPv D large₂ 1041 3 * _ ≤ _ at this
    rw [e] at this
    exact this

end GlobalTheory.FinalJoin
