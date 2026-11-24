module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.appSz :
    AppSz := by
  intro V W F _ _ _ _ _ _ k x
  refine ⟨?_, ?_, ?_⟩
  · intro f g a b hf hg ha hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    obtain ⟨u, hu, hfu⟩ := (hf.of_le hi').contDiffOn (m := i) le_rfl (by simp)
    obtain ⟨v, hv, hgv⟩ := (hg.of_le hi').contDiffOn (m := i) le_rfl (by simp)
    obtain ⟨s, hs, hso, hxs⟩ := mem_nhds_iff.1 (Filter.inter_mem hu hv)
    have key := norm_iteratedFDerivWithin_clm_apply (n := i)
      (hfu.mono fun y hy => (hs hy).1) (hgv.mono fun y hy => (hs hy).2) hso.uniqueDiffOn hxs le_rfl
    simp only [iteratedFDerivWithin_of_isOpen _ hso hxs] at key
    refine key.trans ?_
    have h0 := ha.nonneg
    have h1 := hb.nonneg
    calc _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * a * b := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have e1 := ha j (hj'.trans hi)
          have e2 := hb (i - j) ((Nat.sub_le _ _).trans hi)
          gcongr
      _ = 2 ^ i * a * b := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          simp
      _ ≤ 2 ^ k * a * b := by
          gcongr
          norm_num
  · intro L g b hg hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have key := L.iteratedFDeriv_comp_left hg (i := i) hi'
    have e : (fun y => L (g y)) = L ∘ g := rfl
    rw [e, key]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hb i hi) (norm_nonneg _))
  · intro ι s g b hg hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have key := iteratedFDeriv_fun_sum_apply (n := i) (u := s) (f := g) (x := x)
      (fun j hj => (hg j hj).of_le hi')
    rw [key]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hb j hj i hi)
