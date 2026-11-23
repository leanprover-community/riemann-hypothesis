module

import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SubstZOfXCoordZA
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.OddLogRelation

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF altF)

variable {p : ℕ} [hp : Fact p.Prime]

theorem sx_dual_even {n' : ℕ} (B : OmBasis p n') (i i' : Fin (n' / 2)) :
    ∑ r, (sigW p)^[2 * i.val] (B.omS r) * (sigW p)^[2 * i'.val] (B.om r) = if i = i' then 1 else 0 := by
  classical
  have hAB : (Matrix.of fun (r j : Fin (n' / 2)) => (sigW p)^[2 * j.val] (B.om r)) *
      (Matrix.of fun (j r' : Fin (n' / 2)) => (sigW p)^[2 * j.val] (B.omS r')) = 1 := by
    refine Matrix.ext fun r r' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply, ← B.dual r r']
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.of_apply, Matrix.of_apply, iterate_map_mul]
  have hBA := mul_eq_one_comm.mp hAB
  have h := congrFun (congrFun hBA i) i'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa using h

theorem sx_dual {n' : ℕ} (B : OmBasis p n') (hev : Even n') (a b : Fin n') (hab : a.val % 2 = b.val % 2) :
    ∑ r, (sigW p)^[a.val] (B.omS r) * (sigW p)^[b.val] (B.om r) = if a = b then 1 else 0 := by
  apply Formalism.L2.G.Pend.dualS <;> assumption

theorem frobenius_congruence_witt (a : WW p) : ∃ y : WW p, sigW p a = a ^ p + p * y := by
  obtain ⟨y, hy⟩ := Formalism.InvariantFactorPaths.G7.WModel.frob_sub_pow p a
  exact ⟨y, by unfold sigW; linear_combination hy⟩

theorem sx_lift {ι K' : Type} [Field K'] {R : Subring K'} {f : MvPowerSeries ι K'} (hf : IntR R f) :
    ∃ f0 : MvPowerSeries ι R, MvPowerSeries.map R.subtype f0 = f := by
  refine ⟨fun m => ⟨MvPowerSeries.coeff m f, hf m⟩, ?_⟩
  ext m
  rfl

theorem sx_sum_pow {A α : Type} [CommRing A] (s : Finset α) (x : α → A) :
    ∃ r : A, (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + (p : A) * r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [zero_pow hp.out.ne_zero]⟩
  | insert a s ha ih =>
    obtain ⟨r1, hr1⟩ := ih
    obtain ⟨r2, hr2⟩ := exists_add_pow_prime_eq hp.out (x a) (∑ i ∈ s, x i)
    refine ⟨r1 + x a * (∑ i ∈ s, x i) * r2, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr2, hr1]
    ring

theorem sx_frob_sum {ι α K' : Type} [Field K'] (R : Subring K') (s : Finset α) (x : α → MvPowerSeries ι K')
    (hx : ∀ i ∈ s, IntR R (x i)) :
    ∃ Y, IntR R Y ∧ (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + MvPowerSeries.C (p : K') * Y := by
  classical
  have hlift : ∀ i ∈ s, ∃ f0 : MvPowerSeries ι R, MvPowerSeries.map R.subtype f0 = x i :=
    fun i hi => sx_lift (hx i hi)
  choose y hy using hlift
  let y' : α → MvPowerSeries ι R := fun i => if h : i ∈ s then y i h else 0
  obtain ⟨r, hr⟩ := sx_sum_pow (p := p) s y'
  refine ⟨MvPowerSeries.map R.subtype r, fun n => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n r).2
  · have hsum : ∀ i ∈ s, MvPowerSeries.map R.subtype (y' i) = x i := fun i hi => by
      simp only [y', dif_pos hi]
      exact hy i hi
    have h2 := congrArg (MvPowerSeries.map R.subtype) hr

    simp only [map_pow, map_sum, map_add (f := _), map_mul, map_natCast] at h2
    have e3 : ∑ i ∈ s, (MvPowerSeries.map R.subtype (y' i)) ^ p = ∑ i ∈ s, x i ^ p :=
      Finset.sum_congr rfl fun i hi => by rw [hsum i hi]
    rw [Finset.sum_congr rfl hsum, e3] at h2
    rw [h2, map_natCast]

end Formalism.MainNotions.FormalGroupSystem.Pf
