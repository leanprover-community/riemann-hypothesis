module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcRow_succ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) (k : ℕ) :
    ∑ l, (hcMat R μ ^ (k+1)) i l =
      shift R μ i * ∑ l, (hcMat R μ ^ k) i l - ∑ j ∈ Finset.univ.filter (fun j => i < j), ∑ l, (hcMat R μ ^ k) j l := by
  rw [pow_succ']
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hpt : ∀ j : Fin N, hcMat R μ i j * ∑ l, (hcMat R μ ^ k) j l =
      (if j = i then shift R μ i * ∑ l, (hcMat R μ ^ k) j l else 0) +
      (if i < j then -∑ l, (hcMat R μ ^ k) j l else 0) := by
    intro j
    simp only [hcMat, Matrix.of_apply]
    by_cases h1 : j = i
    · subst h1; simp
    · by_cases h2 : i < j
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_ite_eq' , ← Finset.sum_filter,
    Finset.sum_neg_distrib]
  simp [sub_eq_add_neg]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

def hcRowSeries (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) : PowerSeries R :=
  PowerSeries.mk fun k => ∑ l, (hcMat R μ ^ k) i l

theorem hcRowSeries_eq (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) :
    (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) * hcRowSeries R μ i =
      1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j => i < j), hcRowSeries R μ j := by
  ext n
  cases n with
  | zero => simp [hcRowSeries, sub_mul, mul_assoc, Matrix.one_apply]
  | succ k =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hcRowSeries, sub_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, map_sum, hcRow_succ]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcTelescope (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    ∀ d, d ≤ N →
      (1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), hcRowSeries R μ j) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j + 1) * PowerSeries.X) := by
  intro d
  induction d with
  | zero =>
    intro _
    have : Finset.univ.filter (fun j : Fin N => N - 0 ≤ j.val) = ∅ := by
      ext j; simp
    rw [this]; simp
  | succ d ih =>
    intro hd
    set i : Fin N := ⟨N - d - 1, by omega⟩ with hi
    have hS : Finset.univ.filter (fun j : Fin N => N - (d+1) ≤ j.val) =
        insert i (Finset.univ.filter (fun j : Fin N => N - d ≤ j.val)) := by
      ext j; simp [hi, Fin.ext_iff]; omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      simp [hi]; omega
    have hgt : Finset.univ.filter (fun j : Fin N => i < j) = Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      ext j; simp [hi, Fin.lt_iff_val_lt_val]; omega
    have h := hcRowSeries_eq R N μ i
    rw [hgt] at h
    have IH := ih (by omega)
    rw [hS, Finset.sum_insert hnot, Finset.prod_insert hnot, Finset.prod_insert hnot]
    rw [map_add (f := _), map_one]
    linear_combination (1 - PowerSeries.C (shift R μ i) * PowerSeries.X - PowerSeries.X) * IH
      - PowerSeries.X * (∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X)) * h

theorem hcVal_generating (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) =
      ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  have h := hcTelescope R N μ N le_rfl
  have hU : Finset.univ.filter (fun j : Fin N => N - N ≤ j.val) = Finset.univ := by
    ext j; simp
  have hmk : PowerSeries.mk (hcVal R μ) = ∑ j, hcRowSeries R μ j := by
    ext n; simp [hcVal, hcRowSeries, map_sum]
  rw [hU] at h
  rw [hmk]
  exact h

end GlobalTheory.Alc
