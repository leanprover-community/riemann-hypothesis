module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
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

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValPowDvd

theorem dvd_of_pow_mul_dvd_pow : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  intro S _ ϖ hϖ hV z m d hd hdiv
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨w, hw⟩ := hdiv
  obtain ⟨e, he, h1, h2⟩ := hV (ϖ ^ m) z ⟨m, Ideal.subset_span (Set.mem_insert _ _)⟩
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : (e * ϖ ^ m) ^ (d' + 1) = (c' * z) ^ (d' + 1) := by rw [hc']
  rw [mul_pow, mul_pow, hw, he.pow_succ_eq d', ← pow_mul] at h3
  have key : (e - w * c' ^ (d' + 1)) * ϖ ^ (m * (d' + 1)) = 0 := by linear_combination h3
  have he' : e = w * c' ^ (d' + 1) :=
    sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (pow_mem hϖ (m * (d' + 1)))).2 _ key)
  have hee : e * e = e := he.eq
  exact ⟨e * w * c' ^ d' + c, by
    linear_combination (-1 : S) * hc + (-z) * hee + (z * e) * he' + (e * w * c' ^ d') * hc' +
      (w * c' ^ d' * ϖ ^ m) * hee⟩

end GlobalTheory.CompanionTheory.ValPowDvd
