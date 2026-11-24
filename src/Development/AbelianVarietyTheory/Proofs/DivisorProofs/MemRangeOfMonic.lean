module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

namespace GlobalTheory.MonicRootRange

theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (h : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  set f := algebraMap T (FractionRing T)
  have hinj : Function.Injective f := IsFractionRing.injective T (FractionRing T)
  have hb0 : f b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hsmul : (b • p : (FractionRing T)[X]) = C (f b) * p := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hn : 1 ≤ p.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have hdeg : q.natDegree = p.natDegree := by
    have := congrArg natDegree hq
    rwa [natDegree_map_eq_of_injective hinj, hsmul, natDegree_C_mul hb0] at this
  have hq0 : q ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hdeg; omega
  have hc0 : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hinj).mpr (leadingCoeff_ne_zero.mpr hq0)
  obtain ⟨w, hw⟩ := h q.integralNormalization (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  refine ⟨f w / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (hdeg ▸ hn) f (f w / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hc0, eval₂_at_apply, hw, map_zero] at key
  have h2 : q.eval₂ f (f w / f q.leadingCoeff) = 0 :=
    (mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ hc0)
  rw [← eval_map, hq, hsmul, eval_mul, eval_C] at h2
  exact (mul_eq_zero.mp h2).resolve_left hb0

end GlobalTheory.MonicRootRange
