module

public import Mathlib.RingTheory.PowerSeries.Inverse
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

theorem UpperTheory.invOfUnit_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (f : PowerSeries R), (∀ n, PowerSeries.coeff n f ∈ S) → PowerSeries.constantCoeff f = 1 → ∀ n, PowerSeries.coeff n (PowerSeries.invOfUnit f 1) ∈ S := by
  intro R _ S f hf _ n
  have h1 : ((1⁻¹ : Rˣ) : R) ∈ S := by
    rw [inv_one, Units.val_one]
    exact S.one_mem
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hn
    · exact h1
    · refine S.mul_mem (S.neg_mem h1) (S.sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact S.mul_mem (hf _) (ih _ hx)
      · exact S.zero_mem
