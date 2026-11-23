module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Jacobi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

lemma conj_mul_im_eq_normSq_mul_div_im (a b : ℂ) (ha : a ≠ 0) :
    ((starRingEnd ℂ) a * b).im = Complex.normSq a * (b / a).im := by
  have hn : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

lemma ne_zero_and_div_im_pos (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    a ≠ 0 ∧ 0 < (b / a).im := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  refine ⟨ha, ?_⟩
  rw [conj_mul_im_eq_normSq_mul_div_im a b ha] at hab
  exact pos_of_mul_pos_right hab (Complex.normSq_nonneg a)

theorem discr_closure_pair_ne_zero (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    discr (AddSubgroup.closure {a, b}) ≠ 0 := by
  obtain ⟨ha, hpos⟩ := ne_zero_and_div_im_pos a b hab
  rw [discr_closure_pair a b hpos]
  have hpi : (2 * Real.pi / a : ℂ) ≠ 0 := by
    refine div_ne_zero ?_ ha
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_ne_zero (pow_ne_zero _ hpi) (pow_ne_zero _ (ModularForm.eta_ne_zero hpos))

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
