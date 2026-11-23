module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory.HTLat

namespace GlobalTheory.TateRel

theorem lev_sum {M : Type} [CommGroup M] {l : ℕ} {ι : Type} (s : Finset ι) (f : ι → Tate l M) (N : ℕ) :
    (∑ i ∈ s, f i).lev N = ∏ i ∈ s, (f i).lev N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Tate.lev_add, ih]

theorem prod_pow_eq_one (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]) (h : ∑ i, c i • Tate.map l (φ i) = 0) (N : ℕ)
    (m : Fin n → ℤ) (hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)))
    (t : Tate l M) : ∏ i, φ i (t.lev N) ^ m i = 1 := by
  have h0 : ((∑ i, c i • Tate.map l (φ i)) t).lev N = 1 := by rw [h]; rfl
  rw [LinearMap.sum_apply, lev_sum] at h0
  rw [← h0]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Tate.lev_smul, Tate.lev_map]
  set y := φ i (t.lev N)
  have hy : y ^ ((l ^ N : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← map_pow, Tate.lev_pow, map_one]
  have hc : ((GlobalTheory.PDiv.digit N (c i) : ℕ) : ZMod (l ^ N)) = ((m i : ℤ) : ZMod (l ^ N)) := by
    rw [GlobalTheory.PDiv.cast_digit, hm i]
  have hc' : (((GlobalTheory.PDiv.digit N (c i) : ℕ) : ℤ) : ZMod (l ^ N)) = ((m i : ℤ) : ZMod (l ^ N)) := by
    rw [Int.cast_natCast]; exact hc
  rw [ZMod.intCast_eq_intCast_iff'] at hc'
  rw [zpow_eq_zpow_emod (m i) hy, ← hc', ← zpow_eq_zpow_emod _ hy, zpow_natCast]

end GlobalTheory.TateRel
