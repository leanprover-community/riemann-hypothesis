module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
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

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.ZclMulPf
open LateralTheory.DivDb

theorem left_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (s : Mat C N) (hs : s ∈ S) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    s * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulLeft C s) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact hf _ (S.mul_mem hs ht)
  have := hy f' hv
  rw [hf'] at this
  simpa using this

theorem mul_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (x : Mat C N) (hx : x ∈ Zcl (S : Set (Mat C N))) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    x * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulRight C y) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact left_mem hC S t ht y hy f hf
  have := hx f' hv
  rw [hf'] at this
  simpa using this

end LateralTheory.DivDb.ZclMulPf

namespace LateralTheory.DivDb

theorem ZclMul_of (hC : Chain) : ZclMul := fun _C _ _N S x hx y hy =>
  LateralTheory.DivDb.ZclMulPf.mul_mem hC S x hx y hy

end LateralTheory.DivDb
