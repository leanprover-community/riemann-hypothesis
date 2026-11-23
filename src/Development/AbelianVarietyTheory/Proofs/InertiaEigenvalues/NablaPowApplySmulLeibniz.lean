module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal.Conn

theorem pow_apply_smul_nsmul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      k.choose p • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  induction k with
  | zero => simp
  | succ k ih =>

    rw [Finset.sum_choose_succ_nsmul
      (fun i j => (fun τ => (⇑(PowerSeries.derivative (R := K)))^[i] (f τ)) • (C.nabla ^ j) v) k,
      pow_succ', mul_apply_eq_comp, ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    rw [map_nsmul, C.leibniz, smul_add, add_comm]
    congr 2
    · rw [show k + 1 - p = k - p + 1 by omega, pow_succ', mul_apply_eq_comp]
    · congr 1
      funext τ
      rw [Function.iterate_succ_apply']

theorem pow_apply_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  rw [pow_apply_smul_nsmul]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm

end GlobalTheory.BKReal.Conn
