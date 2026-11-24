module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
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

open Matrix Complex
open scoped Classical
namespace GlobalTheory.SW

private theorem intM_add_iff_of_intM_right {K : Type} [Field K] {κ ι : Type} {x y : Matrix κ ι K} (hy : IntM y) :
    IntM (x + y) ↔ IntM x :=
  ⟨fun h k i => by simpa using (h k i).sub (hy k i), fun h k i => (h k i).add (hy k i)⟩


open Classical in
theorem ind_sb {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    HasLevel 1 (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_one, one_smul]
    by_contra h
    exact hx (if_neg h)
  · rw [Nat.cast_one, one_smul]
    exact if_congr (intM_add_iff_of_intM_right hy) rfl rfl


open Classical in
theorem ind_isSB {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    IsSB (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := ⟨1, one_pos, ind_sb⟩


open Classical in
theorem ind_ne_zero {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [if_pos (show IntM (0 : Matrix κ ι K) from fun k i => by simpa using isIntegral_zero)] at h0
  exact one_ne_zero h0

end GlobalTheory.SW
