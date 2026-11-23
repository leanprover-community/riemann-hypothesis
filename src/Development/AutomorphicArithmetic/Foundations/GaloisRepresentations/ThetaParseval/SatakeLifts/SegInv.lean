module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem range_val_map_rev (t : ℕ) :
    (Finset.range t).val.map (fun i : ℕ => t - 1 - i) = (Finset.range t).val := by
  have hinj : ∀ i ∈ (Finset.range t).val, ∀ j ∈ (Finset.range t).val, t - 1 - i = t - 1 - j → i = j := by
    intro i hi j hj h
    simp only [Finset.mem_val, Finset.mem_range] at hi hj
    omega
  rw [Multiset.Nodup.ext (Multiset.Nodup.map_on hinj (Finset.range t).nodup) (Finset.range t).nodup]
  intro y
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hy
    exact ⟨t - 1 - y, by omega, by omega⟩

private theorem npowU_neg {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) :
    GlobalTheory.LFun.npowU w (-z) = (GlobalTheory.LFun.npowU w z)⁻¹ := by
  ext
  rw [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.coe_npowU]
  unfold GlobalTheory.LFun.npow
  exact Complex.cpow_neg _ _

theorem UpperTheory.Gal.TP.Loc.segInv :
    UpperTheory.Gal.TP.Loc.SegInv := by
  intro K _ _ w x t
  unfold GlobalTheory.LFun.seg
  rw [Multiset.map_map]
  conv_rhs => rw [← range_val_map_rev t, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i hi
  simp only [Finset.mem_val, Finset.mem_range] at hi
  simp only [Function.comp_apply, mul_inv, ← npowU_neg]
  congr 2
  rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + i ≤ t)]
  push_cast
  ring
