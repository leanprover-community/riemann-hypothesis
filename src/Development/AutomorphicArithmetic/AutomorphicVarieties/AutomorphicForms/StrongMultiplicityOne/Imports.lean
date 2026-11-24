module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open GlobalTheory.CuspRep (Cinf Lie)

namespace UpperTheory.V.TG

variable (E : Type) [Field E] [NumberField E]

instance : (volume : Measure (Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

def tr : Cinf E →ₗ[ℝ] ℝ where
  toFun x := ∑ w, 2 * (x w).re
  map_add' x y := by simp only [Pi.add_apply, Complex.add_re, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.re_ofReal_mul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem tr_apply (x : Cinf E) : tr E x = ∑ w, 2 * (x w).re := rfl

end UpperTheory.V.TG
